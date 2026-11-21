import Praxis.Combinatorics.Mass
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.Lattice

open Finset Module

open scoped BigOperators Matrix

variable {ι J : Type*} [Fintype ι] [DecidableEq ι]

def saturation (Γ : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℤ) where
  carrier := {v | ∃ a : ℤ, a ≠ 0 ∧ a • v ∈ Γ}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a*b, mul_ne_zero ha hb, ?_⟩
    have h := Γ.add_mem (Γ.smul_mem b hx) (Γ.smul_mem a hy)
    simpa only [smul_add, smul_smul, mul_comm b a] using h
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    simpa only [smul_smul, mul_comm c a] using Γ.smul_mem c hx

def IsSaturated (E : Submodule ℤ (ι → ℤ)) : Prop :=
  ∀ (a : ℤ), a ≠ 0 → ∀ v : ι → ℤ, a • v ∈ E → v ∈ E

theorem le_saturation (Γ : Submodule ℤ (ι → ℤ)) : Γ ≤ saturation Γ := by
  intro v hv
  exact ⟨1, one_ne_zero, by simpa using hv⟩

theorem saturation_isSaturated (Γ : Submodule ℤ (ι → ℤ)) :
    IsSaturated (saturation Γ) := by
  rintro a ha v ⟨b, hb, h⟩
  exact ⟨b*a, mul_ne_zero hb ha, by simpa only [smul_smul] using h⟩

variable [Fintype J] [DecidableEq J]

theorem basis_mod_independent (p : ℕ) [Fact p.Prime]
    (E : Submodule ℤ (ι → ℤ)) (hE : IsSaturated E) (b : Basis J ℤ E) :
    LinearIndependent (ZMod p) (fun j i => ((b j).val i : ZMod p)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let u : E := ∑ j, ((c j).val : ℤ) • b j
  have hu : ∀ i, ((u.val i : ℤ) : ZMod p) = 0 := by
    intro i
    have h := congrFun hc i
    simpa only [u, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, Pi.smul_apply', smul_eq_mul, Pi.natCast_apply, Pi.intCast_apply,
      Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
      Pi.zero_apply] using h
  have hdiv : ∀ i, (p : ℤ) ∣ u.val i := fun i =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hu i)
  choose w hw using hdiv
  have hwv : (p : ℤ) • w = u.val := by
    ext i
    exact (hw i).symm
  have hp : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hwE : w ∈ E := hE p hp w (hwv ▸ u.property)
  have he : u = (p : ℤ) • (⟨w, hwE⟩ : E) := Subtype.ext hwv.symm
  have hueq : b.equivFun u = fun j => ((c j).val : ℤ) := by
    rw [show u = b.equivFun.symm (fun j => ((c j).val : ℤ)) from
      (b.equivFun_symm_apply _).symm]
    exact b.equivFun.apply_symm_apply _
  have hcj : (c j).val = (p : ℤ) * b.equivFun ⟨w, hwE⟩ j := by
    have h := congrArg b.equivFun he
    rw [hueq, map_smul] at h
    exact congrFun h j
  have hcast := congrArg (fun x : ℤ => (x : ZMod p)) hcj
  simpa using hcast

theorem basis_eval (E : Submodule ℤ (ι → ℤ)) (b : Basis J ℤ E) (x : E) (i : ι) :
    ∑ j, (b j).val i * b.equivFun x j = x.val i := by
  have h := congrArg (fun y : E => y.val i) (b.sum_equivFun x)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using h

theorem exists_prime_minor (p : ℕ) [Fact p.Prime]
    (E : Submodule ℤ (ι → ℤ)) (hE : IsSaturated E) (b : Basis J ℤ E) :
    ∃ e : J ↪ ι,
      ((Matrix.det (fun i j => (b j).val (e i) : Matrix J J ℤ) : ℤ) : ZMod p) ≠ 0 := by
  classical
  let v : ι → J → ZMod p := fun i j => ((b j).val i : ZMod p)
  obtain ⟨s, -, -, hspan, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty (ZMod p) v) (Set.empty_subset (Set.univ : Set ι))
  have hsp : Submodule.span (ZMod p) (Set.range (fun i : s => v i)) =
      Submodule.span (ZMod p) (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have := hspan ⟨j, Set.mem_univ j, rfl⟩
      simpa only [Set.image_eq_range] using this
  let V : Matrix J ι (ZMod p) := fun j i => ((b j).val i : ZMod p)
  have hr : V.rank = Fintype.card J :=
    (basis_mod_independent p E hE b).rank_matrix
  have hcard : Fintype.card s = Fintype.card J := by
    rw [← finrank_span_eq_card hli, hsp]
    change finrank (ZMod p) (Submodule.span (ZMod p) (Set.range V.transpose.row)) = _
    rw [← Matrix.rank_eq_finrank_span_row, Matrix.rank_transpose, hr]
  let e : J ≃ s := Fintype.equivOfCardEq hcard.symm
  let f : J ↪ ι := e.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨f, ?_⟩
  have hi : LinearIndependent (ZMod p)
      (fun i j => ((b j).val (f i) : ZMod p)) := hli.comp e e.injective
  have hunit := (Matrix.linearIndependent_rows_iff_isUnit).mp hi
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have heq := (Int.castRingHom (ZMod p)).map_det
    (fun i j => (b j).val (f i) : Matrix J J ℤ)
  exact fun h => hdet (heq.symm.trans h)

theorem finrank_saturation (Γ : Submodule ℤ (ι → ℤ)) :
    finrank ℤ (saturation Γ) = finrank ℤ Γ := by
  classical
  let E := saturation Γ
  obtain ⟨k, b⟩ := E.basisOfPid (Pi.basisFun ℤ ι)
  have hb : finrank ℤ E = k := by simpa using finrank_eq_card_basis b
  have hle : finrank ℤ Γ ≤ finrank ℤ E :=
    (Submodule.inclusion (le_saturation Γ)).finrank_le_finrank_of_injective
      (Submodule.inclusion_injective _)
  have hmul : ∀ j : Fin k, ∃ a : ℤ, a ≠ 0 ∧ a • (b j).val ∈ Γ :=
    fun j => (b j).property
  choose a ha hmem using hmul
  let v : Fin k → Γ := fun j => ⟨a j • (b j).val, hmem j⟩
  have hv : LinearIndependent ℤ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have hsum : ∑ l, (c l * a l) • b l = 0 := by
      apply Subtype.ext
      have hc' := congrArg Γ.subtype hc
      simpa only [map_sum, map_smul, Submodule.subtype_apply, v,
        Submodule.coe_mk, smul_smul, Submodule.coe_sum, Submodule.coe_smul,
        Submodule.coe_zero] using hc'
    have hcoef := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum j
    exact (mul_eq_zero.mp hcoef).resolve_right (ha j)
  have hge := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hge
  exact le_antisymm (hb.trans_le hge) hle

end Praxis.Algebra.Lattice
