import Praxis.Algebra.InverseBranches.NormalBranches
import Praxis.Algebra.DifferenceLattice.Definitions
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Combinatorics.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Praxis.Algebra.InverseBranches.AdditiveChain
import Praxis.Algebra.Conversion.Conversion
import Mathlib.LinearAlgebra.Dimension.Localization
import Praxis.Algebra.DifferenceLattice.Saturation

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.VectorInverse

open Finset Module Praxis.Combinatorics Praxis.Algebra.Lattice Praxis.Algebra.DifferenceLattice

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem basis_evaluation_surjective {k : ℕ} (E : Submodule ℤ (ι → ℤ))
    (hsat : IsSaturated E) (b : Basis (Fin k) ℤ E) :
    Function.Surjective (basisMatrix b).transpose.mulVecLin := by
  let B := basisMatrix b
  let f := B.transpose.mulVecLin
  have hp := primitive_of_saturated_basis E hsat b
  have hle : AddSubgroup.closure (Set.range (fun i => B i)) ≤ f.range.toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    simp [f, B]
  rw [hp] at hle
  intro v
  have hv : v ∈ f.range.toAddSubgroup := hle (by trivial)
  exact hv

theorem basis_evaluation_kernel {k : ℕ} (E : Submodule ℤ (ι → ℤ)) (b : Basis (Fin k) ℤ E) :
    (basisMatrix b).transpose.mulVecLin.ker = normalLattice E := by
  ext w
  constructor
  · intro hw
    have hzero : (basisMatrix b).transpose *ᵥ w = 0 := hw
    let l : E →ₗ[ℤ] ℤ := {
      toFun := fun x => ∑ i, w i * x.val i
      map_add' := by intro x y; simp [mul_add, sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        apply sum_congr rfl
        intro i _
        ring }
    have hl : l = 0 := by
      apply b.ext
      intro j
      have hh := congrFun hzero j
      simpa [l, Matrix.mulVec, dotProduct, basisMatrix, mul_comm] using hh
    intro x hx
    exact LinearMap.congr_fun hl ⟨x, hx⟩
  · intro hw
    change (basisMatrix b).transpose *ᵥ w = 0
    ext j
    have hh := hw (b j).val (b j).property
    simpa [Matrix.mulVec, dotProduct, basisMatrix, mul_comm] using hh

theorem normal_rank_saturated (E : Submodule ℤ (ι → ℤ)) (hsat : IsSaturated E) :
    finrank ℤ (normalLattice E) + finrank ℤ E = Fintype.card ι := by
  classical
  obtain ⟨k, b⟩ := E.basisOfPid (Pi.basisFun ℤ ι)
  let f := (basisMatrix b).transpose.mulVecLin
  have hf : Function.Surjective f := basis_evaluation_surjective E hsat b
  have hdim := f.ker.finrank_quotient_add_finrank
  have he := (f.quotKerEquivOfSurjective hf).finrank_eq
  have hb : finrank ℤ E = k := by simpa using finrank_eq_card_basis b
  rw [he, basis_evaluation_kernel E b] at hdim
  simpa [hb, Nat.add_comm] using hdim

end Praxis.Algebra.VectorInverse
