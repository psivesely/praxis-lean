import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation
import Praxis.Algebra.DifferenceLattice.Saturation

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open Finset Module Matrix Praxis.Analysis

open Praxis.Algebra.Lattice (IsSaturated)

open scoped BigOperators

namespace Praxis.Algebra.Sat

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def redVec (p : ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ZMod p) where
  toFun x i := (x i : ZMod p)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

def redSpan (p : ℕ) (E : Submodule ℤ (ι → ℤ)) : Submodule (ZMod p) (ι → ZMod p) :=
  Submodule.span (ZMod p) (redVec p '' (E : Set (ι → ℤ)))

def modAnnihilator (p : ℕ) (E : Submodule ℤ (ι → ℤ)) : Submodule (ZMod p) (ι → ZMod p) where
  carrier := {z | KillsSubmodule p z E}
  zero_mem' := by intro x _; simp
  add_mem' := by
    intro z z' hz hz' x hx
    simp only [Pi.add_apply, add_mul, sum_add_distrib, hz x hx, hz' x hx, add_zero]
  smul_mem' := by
    intro c z hz x hx
    change (∑ i, (c * z i) * (x i : ZMod p)) = 0
    calc
      _ = c * ∑ i, z i * (x i : ZMod p) := by
        rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      _ = 0 := by rw [hz x hx, mul_zero]

def intAnnihilator (E : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℤ) where
  carrier := {w | ∀ x ∈ E, ∑ i, w i * x i = 0}
  zero_mem' := by intro x _; simp
  add_mem' := by
    intro w w' hw hw' x hx
    simp only [Pi.add_apply, add_mul, sum_add_distrib, hw x hx, hw' x hx, add_zero]
  smul_mem' := by
    intro a w hw x hx
    change (∑ i, (a * w i) * x i) = 0
    calc
      _ = a * ∑ i, w i * x i := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      _ = 0 := by rw [hw x hx, mul_zero]

def redIntegerAnnihilator (p : ℕ) (E : Submodule ℤ (ι → ℤ)) :
    Submodule (ZMod p) (ι → ZMod p) :=
  redSpan p (intAnnihilator E)

theorem isSaturated_iff_saturation_eq (E : Submodule ℤ (ι → ℤ)) :
    IsSaturated E ↔ saturation E = E := by
  constructor
  · intro h
    apply le_antisymm
    · rintro v ⟨a, ha, hv⟩
      exact h a ha v hv
    · exact Algebra.Lattice.le_saturation E
  · intro h a ha v hv
    have hmem : v ∈ saturation E := ⟨a, ha, hv⟩
    rwa [h] at hmem

end Defs

def SatDirectSummand (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ E : Submodule ℤ (ι → ℤ), IsSaturated E → ∃ F : Submodule ℤ (ι → ℤ), IsCompl E F

def SatAnnihilatorEq (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Submodule ℤ (ι → ℤ)), IsSaturated E →
    modAnnihilator p E = redIntegerAnnihilator p E

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem redIntegerAnnihilator_le_modAnnihilator (p : ℕ) (E : Submodule ℤ (ι → ℤ)) :
    redIntegerAnnihilator p E ≤ modAnnihilator p E := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  change ∀ x ∈ E, ∑ i, ((w i : ℤ) : ZMod p) * (x i : ZMod p) = 0
  intro x hx
  have h := congrArg (fun t : ℤ => (t : ZMod p)) (hw x hx)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero] using h

end Helpers

end Praxis.Algebra.Sat
