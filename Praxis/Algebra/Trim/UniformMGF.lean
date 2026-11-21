import Praxis.Algebra.Trim.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false

noncomputable section

open Finset

open scoped BigOperators

namespace Praxis.Algebra.Trim

theorem uniformGridSum_mul_sinh (G : ℕ) (t : ℝ) :
    (∑ k : Fin G, Real.exp (t * (((k : ℕ) : ℝ) - ((G : ℝ) - 1) / 2))) *
      Real.sinh (t / 2) = Real.sinh (t * (G : ℝ) / 2) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => Real.exp (t * ((k : ℝ) - ((G : ℝ) - 1) / 2))) G,
    Real.sinh_eq, Real.sinh_eq]
  rw [← mul_div_assoc, sum_mul]
  congr 1
  calc
    (∑ k ∈ range G,
        Real.exp (t * ((k : ℝ) - ((G : ℝ) - 1) / 2)) *
          (Real.exp (t / 2) - Real.exp (-(t / 2)))) =
        ∑ k ∈ range G, (Real.exp (t * (((k + 1 : ℕ) : ℝ) - (G : ℝ) / 2)) -
          Real.exp (t * ((k : ℝ) - (G : ℝ) / 2))) := by
      apply sum_congr rfl
      intro k _hk
      rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
      congr 2 <;> push_cast <;> ring
    _ = Real.exp (t * ((G : ℝ) - (G : ℝ) / 2)) -
        Real.exp (t * ((0 : ℕ) - (G : ℝ) / 2)) :=
      sum_range_sub (fun k : ℕ => Real.exp (t * ((k : ℝ) - (G : ℝ) / 2))) G
    _ = Real.exp (t * (G : ℝ) / 2) - Real.exp (-(t * (G : ℝ) / 2)) := by
      congr 2 <;> push_cast <;> ring

theorem uniformGridMoment_eq_sinh (G : ℕ) (hG : 0 < G) (t : ℝ) (ht : t ≠ 0) :
    uniformGridMoment G t =
      Real.sinh (t * (G : ℝ) / 2) / ((G : ℝ) * Real.sinh (t / 2)) := by
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hG
  have hs : Real.sinh (t / 2) ≠ 0 :=
    Real.sinh_ne_zero.mpr (div_ne_zero ht (by norm_num))
  apply (eq_div_iff (mul_ne_zero hGr hs)).mpr
  unfold uniformGridMoment
  calc
    _ = (∑ k : Fin G,
        Real.exp (t * (((k : ℕ) : ℝ) - ((G : ℝ) - 1) / 2))) *
          Real.sinh (t / 2) := by rw [← mul_assoc, div_mul_cancel₀ _ hGr]
    _ = _ := uniformGridSum_mul_sinh G t

theorem uniformGridMoment_neg (G : ℕ) (hG : 0 < G) (t : ℝ) :
    uniformGridMoment G (-t) = uniformGridMoment G t := by
  by_cases ht : t = 0
  · simp [ht]
  rw [uniformGridMoment_eq_sinh G hG (-t) (neg_ne_zero.mpr ht),
    uniformGridMoment_eq_sinh G hG t ht]
  simp [neg_mul, neg_div, mul_neg, div_neg]

private theorem uniform_grid_mgf_pos (hSinh : SinhDivLeExp)
    (G : ℕ) (hG : 0 < G) (t : ℝ) (ht : 0 < t) :
    uniformGridMoment G t ≤ Real.exp (t ^ 2 * (G : ℝ) ^ 2 / 24) := by
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hhalf : 0 < t / 2 := by positivity
  have hy : 0 < t * (G : ℝ) / 2 := by positivity
  have hden : 0 < (G : ℝ) * (t / 2) := by positivity
  have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr hhalf.le
  calc
    uniformGridMoment G t =
        Real.sinh (t * (G : ℝ) / 2) / ((G : ℝ) * Real.sinh (t / 2)) :=
      uniformGridMoment_eq_sinh G hG t ht.ne'
    _ ≤ Real.sinh (t * (G : ℝ) / 2) / ((G : ℝ) * (t / 2)) :=
      div_le_div_of_nonneg_left (Real.sinh_nonneg_iff.mpr hy.le) hden
        (mul_le_mul_of_nonneg_left hs hGr.le)
    _ = Real.sinh (t * (G : ℝ) / 2) / (t * (G : ℝ) / 2) := by
      congr 1; ring
    _ ≤ Real.exp ((t * (G : ℝ) / 2) ^ 2 / 6) := hSinh _ hy.ne'
    _ = Real.exp (t ^ 2 * (G : ℝ) ^ 2 / 24) := by congr 1; ring

theorem uniform_grid_mgf (hSinh : SinhDivLeExp) : UniformGridMGF := by
  intro G hG t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have h := uniform_grid_mgf_pos hSinh G hG (-t) (neg_pos.mpr ht)
    simpa only [uniformGridMoment_neg G hG, neg_sq] using h
  · subst t
    simp [uniformGridMoment, ne_of_gt hG]
  · exact uniform_grid_mgf_pos hSinh G hG t ht

end Praxis.Algebra.Trim
