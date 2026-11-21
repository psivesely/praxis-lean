import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration

open Classical

namespace Domination

section Abstract

variable {α β Ω : Type}

lemma probOutput_rat (oa : ProbComp α) (x : α) :
    ∃ r : ℚ≥0, Pr[= x | oa] = ((r : ℝ≥0) : ℝ≥0∞) := by
  classical
  let : DecidableEq α := Classical.decEq α
  induction oa using ProbComp.inductionOn with
  | pure a =>
      by_cases h : x = a
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [probOutput_pure, h]⟩
  | query_bind n f ih =>
      choose r hr using ih
      refine ⟨∑ i : Fin (n + 1), (n + 1 : ℚ≥0)⁻¹ * r i, ?_⟩
      rw [probOutput_bind_eq_sum_fintype]
      simp_rw [ProbComp.probOutput_uniformFin, hr]
      have hs : ((∑ i : Fin (n + 1), (n + 1 : ℚ≥0)⁻¹ * r i : ℚ≥0) : ℝ≥0) =
          ∑ i : Fin (n + 1), (((n + 1 : ℚ≥0)⁻¹ * r i : ℚ≥0) : ℝ≥0) := by
        simpa only [NNRat.coe_castHom] using
          (map_sum (NNRat.castHom ℝ≥0) (fun i : Fin (n + 1) => (n + 1 : ℚ≥0)⁻¹ * r i) Finset.univ)
      rw [hs, ENNReal.ofNNReal_finsetSum]
      simp [NNRat.cast_mul, NNRat.cast_inv, ENNReal.coe_mul, ENNReal.coe_inv]

lemma exists_probComp_of_weights (s : Finset α) (w : α → ℚ≥0)
    (hw : ∑ x ∈ s, w x = 1) :
    ∃ oa : ProbComp α, ∀ x,
      Pr[= x | oa] = if x ∈ s then ((w x : ℝ≥0) : ℝ≥0∞) else 0 := by
  classical
  let : DecidableEq α := Classical.decEq α
  let D := ∏ x ∈ s, (w x).den
  have hD : 0 < D := Finset.prod_pos fun x _ => (w x).den_pos
  let f : α → ℕ := fun x => (w x).num * (D / (w x).den)
  have hf (x : α) (hx : x ∈ s) : (f x : ℚ≥0) = w x * D := by
    have hd : (w x).den ∣ D := Finset.dvd_prod_of_mem (fun x => (w x).den) hx
    calc
      (f x : ℚ≥0) = ((w x).num : ℚ≥0) * (D / (w x).den : ℕ) := by simp [f]
      _ = (w x * (w x).den) * (D / (w x).den : ℕ) := by rw [NNRat.mul_den_eq_num]
      _ = w x * D := by rw [mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hd]
  have hsum : ∑ x ∈ s, f x = D := by
    have he : ((∑ x ∈ s, f x : ℕ) : ℚ≥0) = D := by
      push_cast
      rw [Finset.sum_congr rfl hf, ← Finset.sum_mul, hw, one_mul]
    exact_mod_cast he
  let ι := (x : s) × Fin (f x)
  have hcard : Fintype.card ι = D := by
    simpa [ι, Fintype.card_sigma, Fintype.card_fin, Finset.sum_attach] using hsum
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let := SampleableType.ofFintype ι
  refine ⟨(fun z : ι => z.1.val) <$> ($ᵗ ι), ?_⟩
  intro x
  rw [probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample, hcard]
  change (∑ z : (a : s) × Fin (f a), if x = z.1.val then (D : ℝ≥0∞)⁻¹ else 0) = _
  rw [Fintype.sum_sigma]
  change (∑ a : s, ∑ _ : Fin (f a), if x = a.val then (D : ℝ≥0∞)⁻¹ else 0) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hx : x ∈ s
  · rw [if_pos hx]
    have he : (∑ a : s, (f a : ℝ≥0∞) * if x = a.val then (D : ℝ≥0∞)⁻¹ else 0) =
        (f x : ℝ≥0∞) * (D : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_eq_single (⟨x, hx⟩ : s)]
      · simp
      · intro a _ ha
        have : x ≠ a.val := fun h => ha (Subtype.ext h.symm)
        simp [this]
      · simp
    rw [he]
    have hrat : (f x : ℚ≥0) / D = w x := by
      rw [hf x hx, mul_div_cancel_right₀ _ (by positivity : (D : ℚ≥0) ≠ 0)]
    rw [← hrat, NNRat.cast_div]
    simp only [NNRat.cast_natCast]
    rw [ENNReal.coe_div (by positivity : (D : ℝ≥0) ≠ 0)]
    simp [div_eq_mul_inv]
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro a _
    have : x ≠ a.val := fun h => hx (h.symm ▸ a.property)
    simp [this]

private def jointRat (oa : ProbComp α) (x : α) : ℚ≥0 :=
  (probOutput_rat oa x).choose

private lemma jointRat_spec (oa : ProbComp α) (x : α) :
    Pr[= x | oa] = (((jointRat oa x) : ℝ≥0) : ℝ≥0∞) :=
  (probOutput_rat oa x).choose_spec

private lemma jointRat_zero [DecidableEq α] (oa : ProbComp α) (x : α) (hx : x ∉ finSupport oa) :
    jointRat oa x = 0 := by
  have h := probOutput_eq_zero' oa x hx
  rw [jointRat_spec] at h
  exact_mod_cast h

private lemma jointRat_sum [DecidableEq α] (oa : ProbComp α) :
    ∑ x ∈ finSupport oa, jointRat oa x = 1 := by
  have h := sum_finSupport_probOutput_eq_one (mx := oa) (by simp)
  let c : ℚ≥0 →+* ℝ≥0∞ := ENNReal.ofNNRealHom.comp (NNRat.castHom ℝ≥0)
  have hc : Function.Injective c := fun x y hxy => NNRat.cast_injective (ENNReal.coe_injective hxy)
  apply hc
  rw [map_sum, map_one]
  calc (∑ x ∈ finSupport oa, c (jointRat oa x)) = ∑ x ∈ finSupport oa, Pr[= x | oa] := by
         apply Finset.sum_congr rfl
         intro x hx
         exact (jointRat_spec oa x).symm
       _ = 1 := h

lemma exists_joint_of_dominated (obs : ProbComp Ω) (trials : ProbComp β)
    (E : Ω → Prop) (T : Ω → ProbComp β)
    (hdom : ∀ b, (∑' ω, Pr[= ω | obs] * (if E ω then Pr[= b | T ω] else 0)) ≤
      Pr[= b | trials]) :
    ∃ joint : ProbComp (Ω × β),
      evalSPMF (Prod.fst <$> joint) = evalSPMF obs ∧
      evalSPMF (Prod.snd <$> joint) = evalSPMF trials ∧
      ∀ z ∈ support joint, E z.1 → z.2 ∈ support (T z.1) := by
  classical
  let : DecidableEq β := Classical.decEq β
  let : DecidableEq Ω := Classical.decEq Ω
  let c : ℚ≥0 →+* ℝ≥0∞ := ENNReal.ofNNRealHom.comp (NNRat.castHom ℝ≥0)
  have hc_inj : Function.Injective c := by
    intro r s h
    change ((r : ℝ≥0) : ℝ≥0∞) = ((s : ℝ≥0) : ℝ≥0∞) at h
    exact_mod_cast h
  have hc_le (r s : ℚ≥0) : c r ≤ c s ↔ r ≤ s := by
    change ((r : ℝ≥0) : ℝ≥0∞) ≤ ((s : ℝ≥0) : ℝ≥0∞) ↔ r ≤ s
    norm_cast
  let tagged : ProbComp (Option β) := obs >>= fun ω =>
    if E ω then some <$> T ω else pure none
  have hsome (b : β) : Pr[= some b | tagged] =
      ∑' ω, Pr[= ω | obs] * (if E ω then Pr[= b | T ω] else 0) := by
    rw [probOutput_bind_eq_tsum]
    apply tsum_congr
    intro ω
    by_cases h : E ω
    · simp only [if_pos h]
      rw [probOutput_map_injective (T ω) (Option.some_injective β)]
    · simp [h]
  have hnone : Pr[= none | tagged] =
      ∑' ω, Pr[= ω | obs] * (if E ω then 0 else 1) := by
    rw [probOutput_bind_eq_tsum]
    apply tsum_congr
    intro ω
    by_cases h : E ω <;> simp [h]
  let v : β → ℚ≥0 := fun b => jointRat tagged (some b)
  let p : β → ℚ≥0 := jointRat trials
  let d : ℚ≥0 := jointRat tagged none
  have hv (b : β) : c (v b) = Pr[= some b | tagged] := (jointRat_spec _ _).symm
  have hp (b : β) : c (p b) = Pr[= b | trials] := (jointRat_spec _ _).symm
  have hd : c d = Pr[= none | tagged] := (jointRat_spec _ _).symm
  have hvle (b : β) : v b ≤ p b := by
    apply (hc_le _ _).mp
    rw [hv, hp, hsome]
    exact hdom b
  have hvzero (b : β) (hb : b ∉ finSupport trials) : v b = 0 := by
    apply le_antisymm _ (zero_le)
    simpa only [p, jointRat_zero trials b hb] using hvle b
  have htotal : d + ∑ b ∈ finSupport trials, v b = 1 := by
    apply hc_inj
    simp only [map_add, map_sum, map_one, hv, hd]
    have hsum : (∑' b, Pr[= some b | tagged]) =
        ∑ b ∈ finSupport trials, Pr[= some b | tagged] := by
      apply tsum_eq_sum
      intro b hb
      rw [← hv, hvzero b hb, map_zero]
    rw [← hsum]
    simpa using probOutput_none_add_tsum_some tagged
  have hres : ∑ b ∈ finSupport trials, (p b - v b) = d := by
    apply add_right_cancel (b := ∑ b ∈ finSupport trials, v b)
    rw [← Finset.sum_add_distrib]
    simp_rw [tsub_add_cancel_of_le (hvle _)]
    rw [show (∑ b ∈ finSupport trials, p b) = 1 from jointRat_sum trials, htotal]
  have hR : ∃ R : ProbComp β, ∀ b,
      c (v b) + c d * Pr[= b | R] = c (p b) := by
    by_cases hz : d = 0
    · refine ⟨trials, fun b => ?_⟩
      have hrzero : p b - v b = 0 := by
        by_cases hb : b ∈ finSupport trials
        · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le)).mp
            (hres.trans hz) b hb
        · simp [p, jointRat_zero trials b hb, hvzero b hb]
      have heq : v b = p b := le_antisymm (hvle b) (tsub_eq_zero_iff_le.mp hrzero)
      simp [hz, heq]
    · have hweights : ∑ b ∈ finSupport trials, (p b - v b) / d = 1 := by
        rw [← Finset.sum_div, hres, div_self hz]
      obtain ⟨R, hR⟩ := exists_probComp_of_weights (finSupport trials)
        (fun b => (p b - v b) / d) hweights
      refine ⟨R, fun b => ?_⟩
      have hRb : Pr[= b | R] = c ((p b - v b) / d) := by
        rw [hR]
        split_ifs with hb
        · rfl
        · simp [p, jointRat_zero trials b hb, hvzero b hb]
      rw [hRb, ← map_mul, mul_div_cancel₀ _ hz, ← map_add,
        add_tsub_cancel_of_le (hvle b)]
  obtain ⟨R, hR⟩ := hR
  let K : Ω → ProbComp β := fun ω => if E ω then T ω else R
  let joint : ProbComp (Ω × β) := obs >>= fun ω => (fun b => (ω, b)) <$> K ω
  refine ⟨joint, ?_, ?_, ?_⟩
  · apply evalSPMF_ext
    intro ω
    change Pr[= ω | Prod.fst <$> (obs >>= fun a => (fun b => (a, b)) <$> K a)] = _
    rw [map_bind, probOutput_bind_eq_tsum]
    simp only [Functor.map_map]
    have hconst (a : Ω) :
        Pr[= ω | (fun _ : β => a) <$> K a] = Pr[= ω | (pure a : ProbComp Ω)] := by
      simp [probOutput_map_const]
    simp_rw [hconst]
    rw [← probOutput_bind_eq_tsum, bind_pure]
  · apply evalSPMF_ext
    intro b
    change Pr[= b | Prod.snd <$> (obs >>= fun ω => (fun b => (ω, b)) <$> K ω)] = _
    rw [map_bind]
    simp only [Functor.map_map, show (fun a : β => a) = id from rfl, id_map]
    rw [probOutput_bind_eq_tsum]
    calc (∑' ω, Pr[= ω | obs] * Pr[= b | K ω]) =
        Pr[= some b | tagged] + Pr[= none | tagged] * Pr[= b | R] := by
          rw [hsome, hnone, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          apply tsum_congr
          intro ω
          by_cases h : E ω <;> simp [K, h]
      _ = Pr[= b | trials] := by rw [← hv, ← hd, ← hp]; exact hR b
  · intro z hz he
    change z ∈ support (obs >>= fun ω => (fun b => (ω, b)) <$> K ω) at hz
    simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image] at hz
    obtain ⟨ω, hω, b, hb, hpair⟩ := hz
    cases hpair
    simpa only [K, if_pos he] using hb

end Abstract

end Domination

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration
