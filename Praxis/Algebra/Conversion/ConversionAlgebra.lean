import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

open Matrix

namespace HeavyStack

theorem maximalMinor_coordinate_bound {n d : ℕ}
    (B : Matrix (Fin n) (Fin d) ℝ) (r : Fin d → Fin n)
    (hdet : (B.submatrix r id).det ≠ 0)
    (hmax : ∀ s : Fin d → Fin n,
      |(B.submatrix s id).det| ≤ |(B.submatrix r id).det|)
    (c : Fin d → ℝ) (i : Fin n) :
    |(B *ᵥ c) i| ≤ ∑ j, |(B *ᵥ c) (r j)| := by
  classical
  let A := B.submatrix r id
  let u := Matrix.cramer Aᵀ (B i)
  have hu (j : Fin d) : |u j| ≤ |A.det| := by
    rw [show u j = (A.updateRow j (B i)).det from Matrix.cramer_transpose_apply A (B i) j]
    have heq : A.updateRow j (B i) = B.submatrix (Function.update r j i) id := by
      ext k l
      by_cases h : k = j <;> simp [A, Matrix.updateRow_apply, h]
    rw [heq]
    exact hmax _
  have hid : (∑ j, u j * (A *ᵥ c) j) = A.det * (B *ᵥ c) i := by
    change (Aᵀ.cramer (B i)) ⬝ᵥ (A *ᵥ c) = A.det * ((B i) ⬝ᵥ c)
    rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_cramer,
      Matrix.det_transpose, dotProduct_smul, smul_eq_mul, dotProduct_comm c (B i)]
  have hineq : |A.det| * |(B *ᵥ c) i| ≤
      |A.det| * ∑ j, |(B *ᵥ c) (r j)| := by
    calc
      |A.det| * |(B *ᵥ c) i| = |∑ j, u j * (A *ᵥ c) j| := by
        rw [hid, abs_mul]
      _ ≤ ∑ j, |u j * (A *ᵥ c) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A.det| * |(A *ᵥ c) j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hu j) (abs_nonneg _)
      _ = |A.det| * ∑ j, |(B *ᵥ c) (r j)| := by
        rw [Finset.mul_sum]
        rfl
  have hpos := abs_pos.mpr hdet
  change 0 < |A.det| at hpos
  nlinarith

def lineMatrix {d : ℕ} (p : ℕ) (j : Fin d) (v : Fin d → ℤ) :
    Matrix (Fin d) (Fin d) ℤ :=
  ((p : ℤ) • (1 : Matrix (Fin d) (Fin d) ℤ)).updateCol j v

theorem det_lineMatrix {d p : ℕ} (j : Fin d) (v : Fin d → ℤ) (hv : v j = 1) :
    (lineMatrix p j v).det = (p : ℤ) ^ (d - 1) := by
  have hid : ((1 : Matrix (Fin d) (Fin d) ℤ).updateCol j v).det = v j := by
    simpa [Matrix.one_apply, mul_ite] using
      (Matrix.det_updateCol_sum (1 : Matrix (Fin d) (Fin d) ℤ) j v)
  rw [lineMatrix, Matrix.det_updateCol_smul_left, hid, hv, mul_one, Fintype.card_fin]

theorem exists_lineMatrix {d p : ℕ} [Fact p.Prime]
    (c : Fin d → ZMod p) (j : Fin d) (hc : c j ≠ 0) :
    ∃ T : Matrix (Fin d) (Fin d) ℤ,
      T.det = (p : ℤ) ^ (d - 1) ∧
      ∀ t : Fin d → ℤ, ∃ a : ZMod p,
        ∀ i, ((T *ᵥ t) i : ZMod p) = a * c i := by
  classical
  let v : Fin d → ℤ := fun i => if i = j then 1 else ((c i / c j).val : ℤ)
  have hv : v j = 1 := by simp [v]
  have hvcast (i : Fin d) : (v i : ZMod p) = c i / c j := by
    by_cases h : i = j
    · subst i
      simp [v, hc]
    · simp [v, h]
  refine ⟨lineMatrix p j v, det_lineMatrix j v hv, ?_⟩
  intro t
  refine ⟨(t j : ZMod p) / c j, ?_⟩
  intro i
  have heq : (((lineMatrix p j v) *ᵥ t) i : ZMod p) =
      (v i : ZMod p) * (t j : ZMod p) := by
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
    calc
      _ = ((lineMatrix p j v i j : ℤ) : ZMod p) * (t j : ZMod p) := by
        apply Finset.sum_eq_single j
        · intro k _ hk
          simp only [lineMatrix, Matrix.updateCol_apply, if_neg hk,
            Matrix.smul_apply, smul_eq_mul, Int.cast_mul]
          simp
        · simp
      _ = _ := by simp [lineMatrix, Matrix.updateCol_apply]
  rw [heq, hvcast]
  ring

end HeavyStack
