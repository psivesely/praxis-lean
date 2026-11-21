import Praxis.Algebra.Power.Definitions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Praxis.Algebra.Power

theorem residueFactor_pow_mul_le_one (hCeiling : CeilingPower)
    {L G v : ℕ} (hL : 7 ≤ L) (hG : 2 ^ L ≤ G)
    (hv : 1 ≤ v) (hvG : v < G) :
    ((((G + v - 1) / v : ℕ) : ℝ) / (G : ℝ)) ^ L * (v : ℝ) ^ (L - 1) ≤ 1 := by
  have hGpos : (0 : ℝ) < G := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le v) hvG)
  have hnat : ((G + v - 1) / v) ^ L * v ^ (L - 1) ≤ G ^ L := by
    by_cases hvone : v = 1
    · subst v
      simp
    · exact hCeiling L G v hL hG (by omega) hvG
  have hreal : (((G + v - 1) / v : ℕ) : ℝ) ^ L * (v : ℝ) ^ (L - 1) ≤
      (G : ℝ) ^ L := by
    exact_mod_cast hnat
  rw [div_pow, div_mul_eq_mul_div, div_le_one (pow_pos hGpos L)]
  exact hreal

private theorem mass_height_power_eq {L : ℕ} (hL : 1 ≤ L) (m H : ℝ) :
    (m * H) ^ (L - 1) * m = m ^ L * H ^ (L - 1) := by
  calc
    (m * H) ^ (L - 1) * m = (m ^ (L - 1) * m) * H ^ (L - 1) := by
      rw [mul_pow]
      ring
    _ = m ^ L * H ^ (L - 1) := by
      rw [← pow_succ, Nat.sub_add_cancel hL]

theorem stretch_step (hCeiling : CeilingPower)
    {L G v H H' : ℕ} {m m' : ℝ}
    (hL : 7 ≤ L) (hG : 2 ^ L ≤ G) (hv : 1 ≤ v) (hvG : v < G)
    (hm : 0 ≤ m) (hm' : 0 ≤ m')
    (hstep : m' ≤ m * ((((G + v - 1) / v : ℕ) : ℝ) / (G : ℝ)))
    (hheight : H' = H * v) :
    (m' * (H' : ℝ)) ^ (L - 1) * m' ≤ (m * (H : ℝ)) ^ (L - 1) * m := by
  rw [mass_height_power_eq (L := L) (by omega), mass_height_power_eq (L := L) (by omega)]
  calc
    m' ^ L * (H' : ℝ) ^ (L - 1) ≤
        (m * ((((G + v - 1) / v : ℕ) : ℝ) / (G : ℝ))) ^ L *
          (H' : ℝ) ^ (L - 1) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm' hstep L) (by positivity)
    _ = (m ^ L * (H : ℝ) ^ (L - 1)) *
        (((((G + v - 1) / v : ℕ) : ℝ) / (G : ℝ)) ^ L * (v : ℝ) ^ (L - 1)) := by
      rw [hheight, Nat.cast_mul, mul_pow, mul_pow]
      ring
    _ ≤ (m ^ L * (H : ℝ) ^ (L - 1)) * 1 :=
      mul_le_mul_of_nonneg_left (residueFactor_pow_mul_le_one hCeiling hL hG hv hvG)
        (mul_nonneg (pow_nonneg hm L) (by positivity))
    _ = m ^ L * (H : ℝ) ^ (L - 1) := mul_one _

theorem stretchEstimate_of_ceilingPower (hCeiling : CeilingPower) : StretchEstimate := by
  intro L n G v M m hL hG hv hvG hm hstep hheight
  have hprefix : ∀ k ≤ n,
      (m k * (M k : ℝ)) ^ (L - 1) * m k ≤ (m 0 * (M 0 : ℝ)) ^ (L - 1) * m 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        exact le_rfl
    | succ k ih =>
        intro hk
        have hkn : k < n := Nat.lt_of_succ_le hk
        exact (stretch_step hCeiling hL (hG k hkn) (hv k hkn) (hvG k hkn)
          (hm k (Nat.le_of_lt hkn)) (hm (k + 1) hk) (hstep k hkn) (hheight k hkn)).trans
          (ih (Nat.le_of_succ_le hk))
  exact hprefix n le_rfl

end Praxis.Algebra.Power
