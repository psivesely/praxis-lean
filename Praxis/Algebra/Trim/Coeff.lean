import Praxis.Algebra.Trim.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option autoImplicit false

namespace Praxis.Algebra.Trim

theorem six_pow_mul_factorial_le (k : ℕ) :
    6 ^ k * k.factorial ≤ (2 * k + 1).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hstep : 6 * (k + 1) ≤ (2 * k + 3) * (2 * k + 2) := by
      nlinarith
    calc
      6 ^ (k + 1) * (k + 1).factorial =
          (6 * (k + 1)) * (6 ^ k * k.factorial) := by
        rw [pow_succ, Nat.factorial_succ]
        ring
      _ ≤ ((2 * k + 3) * (2 * k + 2)) * (2 * k + 1).factorial :=
        Nat.mul_le_mul hstep ih
      _ = (2 * (k + 1) + 1).factorial := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
          Nat.factorial_succ (2 * k + 2),
          show 2 * k + 2 = (2 * k + 1) + 1 by omega,
          Nat.factorial_succ (2 * k + 1)]
        ring

theorem hasSum_sinh_div (y : ℝ) (hy : y ≠ 0) :
    HasSum (fun k : ℕ => y ^ (2 * k) / ((2 * k + 1).factorial : ℝ))
      (Real.sinh y / y) := by
  have hterm : (fun k : ℕ => (y ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ)) / y) =
      (fun k : ℕ => y ^ (2 * k) / ((2 * k + 1).factorial : ℝ)) := by
    funext k
    rw [pow_succ]
    field_simp
  simpa only [hterm] using (Real.hasSum_sinh y).div_const y

theorem sinh_series_term_le (y : ℝ) (k : ℕ) :
    y ^ (2 * k) / ((2 * k + 1).factorial : ℝ) ≤
      (y ^ 2 / 6) ^ k / (k.factorial : ℝ) := by
  rw [div_pow, ← pow_mul, div_div]
  apply div_le_div_of_nonneg_left (by rw [pow_mul]; positivity) (by positivity)
  exact_mod_cast six_pow_mul_factorial_le k

theorem sinhDivLeExp : SinhDivLeExp := by
  intro y hy
  have hs := hasSum_sinh_div y hy
  have he : HasSum (fun k : ℕ => (y ^ 2 / 6) ^ k / (k.factorial : ℝ))
      (Real.exp (y ^ 2 / 6)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (y ^ 2 / 6)
  rw [← hs.tsum_eq, ← he.tsum_eq]
  exact hs.summable.tsum_le_tsum (sinh_series_term_le y) he.summable

end Praxis.Algebra.Trim
