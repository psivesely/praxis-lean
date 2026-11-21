import Praxis.Proofs.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Index

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec

open scoped ENNReal

lemma uniform_map_addHom {U V : Type} [AddGroup U] [AddGroup V] [Fintype U] [Fintype V]
    [su : SampleableType U] [sv : SampleableType V] (f : U →+ V) (hf : Function.Surjective f) :
    evalSPMF (f <$> ($ᵗ U)) = evalSPMF ($ᵗ V) := by
  classical
  letI dv : DecidableEq V := Classical.decEq V
  let custom : SampleableType V :=
    { selectElem := f <$> ($ᵗ U)
      mem_support_selectElem := by
        intro v
        obtain ⟨u, rfl⟩ := hf v
        simp only [support_map, Set.mem_image]
        exact ⟨u, mem_support_uniformSample U, rfl⟩
      probOutput_selectElem_eq := by
        intro v w
        rw [probOutput_map, probOutput_map]
        rw [@probEvent_uniformSample U su _ (fun u => f u = v) (fun _ => Classical.propDecidable _),
          @probEvent_uniformSample U su _ (fun u => f u = w) (fun _ => Classical.propDecidable _)]
        have hcard := @AddMonoidHom.card_fiber_eq_of_mem_range U V (U →+ V)
          _ _ _ dv _ _ f v w (hf v) (hf w)
        exact congrArg (fun c : ℕ => (c : ℝ≥0∞) / Fintype.card U) hcard }
  apply evalSPMF_ext
  intro v
  have h := @probOutput_uniformSample V custom _ v
  exact h.trans (@probOutput_uniformSample V sv _ v).symm

section Count

variable {K : Type} [Field K] [Fintype K] {d : ℕ}

lemma span_eq_top_iff_transpose_independent (s : Fin 3 → Fin d → K) :
    Submodule.span K (Set.range s) = ⊤ ↔
      LinearIndependent K (fun i : Fin d => fun j : Fin 3 => s j i) := by
  have hrank : Module.finrank K (Submodule.span K (Set.range s)) =
      Module.finrank K (Submodule.span K (Set.range (fun i : Fin d => fun j : Fin 3 => s j i))) := by
    change Module.finrank K (Submodule.span K (Set.range (Matrix.of s).row)) =
      Module.finrank K (Submodule.span K (Set.range (Matrix.of s).transpose.row))
    rw [← Matrix.rank_eq_finrank_span_row (Matrix.of s),
      ← Matrix.rank_eq_finrank_span_row (Matrix.of s).transpose, Matrix.rank_transpose]
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_fin, Set.finrank]
  change Submodule.span K (Set.range s) = ⊤ ↔ d = _
  constructor
  · intro hs
    rw [← hrank, hs]
    simp
  · intro hs
    apply Submodule.eq_top_of_finrank_eq
    rw [hrank, ← hs]
    simp

lemma card_spanning_triples (hd : d ≤ 3) :
    Nat.card {s : Fin 3 → Fin d → K // Submodule.span K (Set.range s) = ⊤} =
      ∏ i : Fin d, (Fintype.card K ^ 3 - Fintype.card K ^ i.val) := by
  let e : (Fin 3 → Fin d → K) ≃ (Fin d → Fin 3 → K) := Equiv.piComm (fun _ : Fin 3 => fun _ : Fin d => K)
  have he : ∀ s, Submodule.span K (Set.range s) = ⊤ ↔ LinearIndependent K (e s) :=
    fun s => span_eq_top_iff_transpose_independent s
  have ee := e.subtypeEquiv (q := fun a => LinearIndependent K a) he
  rw [Nat.card_congr ee]
  simpa using (card_linearIndependent (K := K) (V := Fin 3 → K) (k := d) (by simpa using hd))

lemma coordinate_span_failure_bound (hd : d ≤ 3)
    [SampleableType (Fin 3 → Fin d → K)] :
    (Pr[fun s : Fin 3 → Fin d → K => Submodule.span K (Set.range s) ≠ ⊤ |
      $ᵗ (Fin 3 → Fin d → K)]).toReal ≤ 2 / (Fintype.card K : ℝ) := by
  classical
  let q := Fintype.card K
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have htotal : Fintype.card (Fin 3 → Fin d → K) = (q ^ d) ^ 3 := by
    simp [q, Fintype.card_fun]
  have hgood : Fintype.card {s : Fin 3 → Fin d → K //
      Submodule.span K (Set.range s) = ⊤} =
      ∏ i : Fin d, (q ^ 3 - q ^ i.val) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_spanning_triples hd
  have hprod : (∏ i : Fin d, (q ^ 3 - q ^ i.val)) ≤ (q ^ d) ^ 3 := by
    rw [← hgood, ← htotal]
    exact Fintype.card_subtype_le _
  have hbad : (Finset.univ.filter fun s : Fin 3 → Fin d → K =>
      Submodule.span K (Set.range s) ≠ ⊤).card =
      (q ^ d) ^ 3 - ∏ i : Fin d, (q ^ 3 - q ^ i.val) := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, htotal, hgood]
  rw [probEvent_uniformSample, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, hbad, htotal, Nat.cast_sub hprod]
  have hinner (i : Fin d) : ((q ^ 3 - q ^ i.val : ℕ) : ℝ) =
      (q : ℝ) ^ 3 - (q : ℝ) ^ i.val := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : i.val ≤ 3))]
    push_cast
    rfl
  simp_rw [Nat.cast_prod, hinner]
  simp only [Nat.cast_pow]
  change (((q : ℝ) ^ d) ^ 3 - ∏ i : Fin d, ((q : ℝ) ^ 3 - (q : ℝ) ^ i.val)) /
    ((q : ℝ) ^ d) ^ 3 ≤ 2 / q
  interval_cases d
  · simpa using (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hqpos.le)
  · simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one]
    apply (div_le_div_iff₀ (by positivity) hqpos).mpr
    nlinarith [sq_nonneg (q : ℝ)]
  · simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    apply (div_le_div_iff₀ (by positivity) hqpos).mpr
    have h1 : 0 ≤ (q : ℝ) ^ 4 * (q - 1) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ (q : ℝ) ^ 3 * (q - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  · simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    apply (div_le_div_iff₀ (by positivity) hqpos).mpr
    have h1 : 0 ≤ (q : ℝ) ^ 7 * (q - 1) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ (q : ℝ) ^ 3 * ((q : ℝ) ^ 2 - 1) :=
      mul_nonneg (by positivity) (by nlinarith)
    nlinarith [pow_nonneg hqpos.le 4]

end Count

end Praxis.Proofs.Injectivity
