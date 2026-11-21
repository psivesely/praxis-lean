import Praxis.Algebra.Sat.Definitions
import Mathlib.LinearAlgebra.Projection

set_option autoImplicit false

open Finset

open scoped BigOperators

namespace Praxis.Algebra.Sat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem intAnnihilator_lift_of_isCompl {p : ℕ} [Fact p.Prime]
    (E F : Submodule ℤ (ι → ℤ)) (hEF : IsCompl E F)
    (z : ι → ZMod p) (hz : z ∈ modAnnihilator p E) :
    ∃ w ∈ intAnnihilator E, redVec p w = z := by
  classical
  let P : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := E.projection F hEF
  let u : ι → ℤ := fun i => ((z i).val : ℤ)
  let f : (ι → ℤ) →ₗ[ℤ] ℤ := {
    toFun := fun x => ∑ i, u i * x i
    map_add' := by intro x y; simp [mul_add, sum_add_distrib]
    map_smul' := by
      intro c x
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
      apply sum_congr rfl
      intro i _
      ring }
  let h : (ι → ℤ) →ₗ[ℤ] ℤ := f - f.comp P
  let w : ι → ℤ := fun i => h (Pi.single i 1)
  have hrepr (x : ι → ℤ) : ∑ i, w i * x i = h x := by
    have hx : (∑ i, x i • (Pi.single i 1 : ι → ℤ)) = x := by
      ext j
      simp [Pi.single_apply]
    have hh := congrArg h hx
    simpa only [map_sum, map_smul, smul_eq_mul, w, mul_comm] using hh
  have hw : w ∈ intAnnihilator E := by
    intro x hx
    rw [hrepr]
    change f x - f (P x) = 0
    rw [show P x = x from Submodule.projection_apply_of_mem_left hEF hx, sub_self]
  refine ⟨w, hw, ?_⟩
  ext i
  have hzP : ((f (P (Pi.single i 1)) : ℤ) : ZMod p) = 0 := by
    have hh := hz (P (Pi.single i 1)) (Submodule.projection_apply_mem hEF _)
    simpa [f, u] using hh
  change ((f (Pi.single i 1) - f (P (Pi.single i 1)) : ℤ) : ZMod p) = z i
  rw [Int.cast_sub, hzP, sub_zero]
  simp [f, u, Pi.single_apply]

theorem satAnnihilatorEq (hSummand : SatDirectSummand ι) : SatAnnihilatorEq ι := by
  intro p hp E hE
  obtain ⟨F, hEF⟩ := hSummand E hE
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, hred⟩ := intAnnihilator_lift_of_isCompl E F hEF z hz
    exact Submodule.subset_span ⟨w, hw, hred⟩
  · exact redIntegerAnnihilator_le_modAnnihilator p E

end Praxis.Algebra.Sat
