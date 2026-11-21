import Praxis.Algebra.Basis.Definitions
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Praxis.Algebra.Conversion.L1Minkowski

set_option autoImplicit false

noncomputable section

open Matrix

open scoped BigOperators

namespace Praxis.Algebra.Basis

private theorem cramer_row_dot {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (b y : Fin d → ℝ) :
    (∑ j, (A.updateRow j b).det * (A *ᵥ y) j) = A.det * (b ⬝ᵥ y) := by
  have h := Matrix.mulVec_cramer A.transpose b
  rw [Matrix.mulVec_transpose, Matrix.det_transpose] at h
  calc
    _ = Matrix.cramer A.transpose b ⬝ᵥ (A *ᵥ y) := by
      simp only [dotProduct, Matrix.cramer_transpose_apply]
    _ = (Matrix.cramer A.transpose b ᵥ* A) ⬝ᵥ y :=
      Matrix.dotProduct_mulVec _ _ _
    _ = (A.det • b) ⬝ᵥ y := by rw [h]
    _ = A.det * (b ⬝ᵥ y) := by rw [smul_dotProduct, smul_eq_mul]

private theorem row_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (b y : Fin d → ℝ) (hA : A.det ≠ 0)
    (hb : ∀ j, |(A.updateRow j b).det| ≤ |A.det|) :
    |b ⬝ᵥ y| ≤ HeavyStack.l1 (A *ᵥ y) := by
  apply (mul_le_mul_iff_right₀ (abs_pos.mpr hA)).mp
  calc
    |A.det| * |b ⬝ᵥ y| = |A.det * (b ⬝ᵥ y)| := (abs_mul _ _).symm
    _ = |∑ j, (A.updateRow j b).det * (A *ᵥ y) j| := by rw [cramer_row_dot]
    _ ≤ ∑ j, |(A.updateRow j b).det * (A *ᵥ y) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A.det| * |(A *ᵥ y) j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb j) (abs_nonneg _)
    _ = |A.det| * HeavyStack.l1 (A *ᵥ y) := by
      rw [← Finset.mul_sum]
      rfl

theorem pivotProjectionBound_holds : PivotProjectionBound := by
  intro ι _ _ d B P hP y
  let A : Matrix (Fin d) (Fin d) ℤ := B.submatrix P id
  let R : Matrix ι (Fin d) ℝ := B.map (fun z => (z : ℝ))
  let C : Matrix (Fin d) (Fin d) ℝ := A.map (fun z => (z : ℝ))
  have hC : C.det ≠ 0 := by
    rw [show C.det = (A.det : ℝ) from (Int.cast_det A).symm]
    exact_mod_cast hP.2.1
  apply (pi_norm_le_iff_of_nonneg (HeavyStack.l1_nonneg (C *ᵥ y))).mpr
  intro i
  rw [Real.norm_eq_abs]
  change |R i ⬝ᵥ y| ≤ HeavyStack.l1 (C *ᵥ y)
  apply row_bound C (R i) y hC
  intro j
  have heq : C.updateRow j (R i) =
      (B.submatrix (Function.update P j i) id).map (fun z => (z : ℝ)) := by
    ext k l
    by_cases h : k = j
    · subst k
      simp [Matrix.updateRow_apply, Matrix.submatrix, C, A, R]
    · simp [Matrix.updateRow_apply, Matrix.submatrix, C, A, R, h]
  rw [heq, ← Int.cast_det, show C.det = (A.det : ℝ) from (Int.cast_det A).symm]
  have hmax := hP.2.2 (Function.update P j i)
  have hmax' : ((B.submatrix (Function.update P j i) id).det.natAbs : ℝ) ≤
      (A.det.natAbs : ℝ) := by exact_mod_cast hmax
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hmax'

end Praxis.Algebra.Basis
