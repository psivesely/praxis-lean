import Praxis.Algebra.Trim.Definitions
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Praxis.Algebra.TrimAnalysis.GridTrim

set_option autoImplicit false

noncomputable section

open Matrix Praxis.Analysis

open scoped BigOperators

namespace Praxis.Algebra.Trim

variable {ι : Type} [Fintype ι] {d : ℕ}

theorem linearIndependent_real_columns (B : Matrix ι (Fin d) ℤ)
    (hB : LinearIndependent ℤ B.col) :
    LinearIndependent ℝ (B.map (Int.castRingHom ℝ)).col := by
  have h := (linearIndependent_algebraMap_comp_iff
    (R := ℤ) (S := ℝ) (v := B.col)).mpr hB
  have heq : (fun j => algebraMap ℤ ℝ ∘ B.col j) =
      (B.map (Int.castRingHom ℝ)).col := by
    ext j i
    rfl
  rw [heq] at h
  exact h

variable [DecidableEq ι]

theorem gridCovariance_posDef (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin d) ℤ) (hB : LinearIndependent ℤ B.col) :
    (gridCovariance G (B.map (Int.castRingHom ℝ))).PosDef := by
  let C := B.map (Int.castRingHom ℝ)
  have hC : Function.Injective C.mulVec :=
    Matrix.mulVec_injective_iff.mpr (linearIndependent_real_columns B hB)
  have hD : (Matrix.diagonal (fun i => (G i : ℝ) ^ 2 / 12)).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    have hi : (0 : ℝ) < G i := by exact_mod_cast hG i
    positivity
  have hgram : gridCovariance G C =
      Cᴴ * Matrix.diagonal (fun i => (G i : ℝ) ^ 2 / 12) * C := by
    ext j k
    change (∑ i, (G i : ℝ) ^ 2 / 12 * C i j * C i k) =
      ∑ i, (Cᴴ * Matrix.diagonal (fun i => (G i : ℝ) ^ 2 / 12) :
        Matrix (Fin d) ι ℝ) j i * C i k
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hgram]
  exact hD.conjTranspose_mul_mul_same hC

end Praxis.Algebra.Trim
