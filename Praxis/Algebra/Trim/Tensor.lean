import Praxis.Algebra.Trim.Definitions
import Praxis.Algebra.TrimAnalysis.GaussianMoment
import Praxis.Algebra.TrimAnalysis.GridTrim

set_option autoImplicit false

noncomputable section

open Finset Matrix Praxis.Analysis

open scoped BigOperators

namespace Praxis.Algebra.Trim

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem grid_expect_prod (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (f : ∀ i, Fin (G i) → ℝ) :
    (gridLaw G hG).expect (fun r => ∏ i, f i (r i)) =
      ∏ i, (∑ k, f i k) / (G i : ℝ) := by
  unfold FiniteLaw.expect gridLaw FiniteLaw.uniform
  simp only [Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
  rw [← Finset.mul_sum, one_div_mul_eq_div, ← Fintype.prod_sum,
    Finset.prod_div_distrib]

theorem grid_coordinate_mean (G : ι → ℕ) (hG : ∀ i, 0 < G i) (i : ι) :
    (gridLaw G hG).expect (fun r => ((r i : ℕ) : ℝ)) =
      ((G i : ℝ) - 1) / 2 := by
  classical
  let : Nonempty (Grid G) := ⟨fun j => ⟨0, hG j⟩⟩
  let e : Grid G ≃ Grid G := Equiv.piCongrRight (fun _ => Fin.revPerm)
  have hrev (r : Grid G) :
      (((e r) i : ℕ) : ℝ) = (G i : ℝ) - 1 - ((r i : ℕ) : ℝ) := by
    change (((r i).rev : ℕ) : ℝ) = _
    rw [Fin.val_rev, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  have hs := e.sum_comp (fun r : Grid G => ((r i : ℕ) : ℝ))
  simp_rw [hrev, Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card (Grid G) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold FiniteLaw.expect gridLaw FiniteLaw.uniform
  rw [← Finset.mul_sum, one_div_mul_eq_div]
  apply (div_eq_iff hc).mpr
  linarith

theorem grid_mean {d : ℕ} (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin d) ℝ) (j : Fin d) :
    (gridLaw G hG).mean (gridImage G B) j =
      ∑ i, B i j * (((G i : ℝ) - 1) / 2) := by
  unfold FiniteLaw.mean gridImage FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = B i j * (gridLaw G hG).expect (fun r => ((r i : ℕ) : ℝ)) := by
      unfold FiniteLaw.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [grid_coordinate_mean]

theorem grid_centered_direction {d : ℕ} (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin d) ℝ) (u : Fin d → ℝ) (r : Grid G) :
    u ⬝ᵥ (gridImage G B r - (gridLaw G hG).mean (gridImage G B)) =
      ∑ i, (B *ᵥ u) i * (((r i : ℕ) : ℝ) - ((G i : ℝ) - 1) / 2) := by
  simp only [dotProduct, Pi.sub_apply, gridImage, grid_mean, Matrix.mulVec]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem grid_directional_moment {d : ℕ} (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin d) ℝ) (u : Fin d → ℝ) :
    (gridLaw G hG).expect (fun r => Real.exp
      (u ⬝ᵥ (gridImage G B r - (gridLaw G hG).mean (gridImage G B)))) =
      ∏ i, uniformGridMoment (G i) ((B *ᵥ u) i) := by
  simp_rw [grid_centered_direction, Real.exp_sum]
  simpa only [uniformGridMoment] using grid_expect_prod G hG
    (fun i k => Real.exp ((B *ᵥ u) i * (((k : ℕ) : ℝ) - ((G i : ℝ) - 1) / 2)))

theorem grid_covariance_matrix {d : ℕ} (G : ι → ℕ)
    (B : Matrix ι (Fin d) ℝ) :
    gridCovariance G B = B.transpose * Matrix.diagonal (fun i => (G i : ℝ)^2 / 12) * B := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [gridCovariance, Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem grid_covariance_direction {d : ℕ} (G : ι → ℕ)
    (B : Matrix ι (Fin d) ℝ) (u : Fin d → ℝ) :
    (u ⬝ᵥ (gridCovariance G B *ᵥ u)) / 2 =
      ∑ i, (B *ᵥ u) i ^ 2 * (G i : ℝ) ^ 2 / 24 := by
  rw [grid_covariance_matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_diagonal, dotProduct]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gridDirectionalMGF_of_uniformGridMGF
    (hscalar : UniformGridMGF) : GridDirectionalMGF := by
  intro ι _ _ d G hG B u
  rw [grid_directional_moment, grid_covariance_direction, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    unfold uniformGridMoment
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
  · intro i _
    exact hscalar (G i) (hG i) ((B *ᵥ u) i)

end Praxis.Algebra.Trim
