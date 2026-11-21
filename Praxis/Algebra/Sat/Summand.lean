import Praxis.Algebra.Sat.Definitions
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Projection
import Praxis.Algebra.DifferenceLattice.Saturation

set_option autoImplicit false

namespace Praxis.Algebra.Sat

open Praxis.Algebra.Lattice (IsSaturated)

variable {ι : Type*}

theorem quotient_isTorsionFree (E : Submodule ℤ (ι → ℤ)) (hsat : IsSaturated E) :
    Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ E) :=
  Module.IsTorsionFree.of_smul_eq_zero (by
    intro a x hx
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨v, rfl⟩ := E.mkQ_surjective x
      apply (Submodule.Quotient.mk_eq_zero E).mpr
      apply hsat a ha v
      apply (Submodule.Quotient.mk_eq_zero E).mp
      change E.mkQ (a • v) = 0
      rw [map_smul]
      exact hx)

variable [Fintype ι]

theorem saturated_projection (E : Submodule ℤ (ι → ℤ)) (hsat : IsSaturated E) :
    ∃ P : (ι → ℤ) →ₗ[ℤ] E, ∀ x : E, P x.val = x := by
  let := quotient_isTorsionFree E hsat
  let : Module.Free ℤ ((ι → ℤ) ⧸ E) := Module.free_iff_isTorsionFree.mpr inferInstance
  obtain ⟨s, hs⟩ := (Module.Projective.iff_split_of_projective E.mkQ E.mkQ_surjective).mp
    (inferInstance : Module.Projective ℤ ((ι → ℤ) ⧸ E))
  let f : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id - s.comp E.mkQ
  have hf (v : ι → ℤ) : f v ∈ E := by
    apply (Submodule.Quotient.mk_eq_zero E).mp
    change E.mkQ (f v) = 0
    dsimp [f]
    have he := LinearMap.congr_fun hs (E.mkQ v)
    exact sub_eq_zero.mpr he.symm
  let P : (ι → ℤ) →ₗ[ℤ] E := f.codRestrict E hf
  refine ⟨P, ?_⟩
  intro v
  apply Subtype.ext
  change v.val - s (E.mkQ v.val) = v.val
  have hv : E.mkQ v.val = 0 := (Submodule.Quotient.mk_eq_zero E).mpr v.property
  rw [hv, map_zero, sub_zero]

variable [DecidableEq ι]

theorem satDirectSummand : SatDirectSummand ι := by
  intro E hsat
  obtain ⟨P, hP⟩ := saturated_projection E hsat
  exact ⟨LinearMap.ker P, LinearMap.isCompl_of_proj hP⟩

end Praxis.Algebra.Sat
