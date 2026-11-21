import Praxis.Algebra.Power.Definitions
import Praxis.Algebra.InverseBranches.JumpFree

set_option autoImplicit false

namespace Praxis.Algebra.Power

private theorem chainExponent_mul_le_one {L G : ℕ} (hL : 7 ≤ L) (hG : 2 ^ L ≤ G) :
    Algebra.VectorInverse.chainExponent (G : ℝ) * (L : ℝ) ≤ 1 := by
  have h128 : 128 ≤ G := by
    calc
      128 = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL
      _ ≤ G := hG
  have hlogG : 0 < Real.log (G : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < G))
  have hlog : (L : ℝ) * Real.log 2 ≤ Real.log (G : ℝ) := by
    calc
      (L : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ L) := (Real.log_pow 2 L).symm
      _ ≤ Real.log (G : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast hG)
  unfold Algebra.VectorInverse.chainExponent
  rw [div_mul_eq_mul_div]
  exact (div_le_one hlogG).mpr (by simpa only [mul_comm] using hlog)

theorem ceiling_power {L G v : ℕ} (hL : 7 ≤ L) (hG : 2 ^ L ≤ G)
    (hv : 2 ≤ v) (hvG : v < G) :
    ((G + v - 1) / v) ^ L * v ^ (L - 1) ≤ G ^ L := by
  have h128 : (128 : ℝ) ≤ G := by
    exact_mod_cast (show 128 ≤ G from
      (show 128 ≤ 2 ^ L from by
        calc
          128 = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL).trans hG)
  have hv2 : (2 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have hG0 : (0 : ℝ) < G := by linarith
  have hvG' : (v : ℝ) ≤ G := by exact_mod_cast hvG.le
  let C : ℕ := (G + v - 1) / v
  have hCv : C * v ≤ G + v :=
    (Nat.div_mul_le_self (G + v - 1) v).trans (Nat.sub_le _ _)
  have hratio : (C : ℝ) * v / G ≤ 1 + (v : ℝ) / G := by
    apply (div_le_iff₀ hG0).mpr
    have hCv' : (C : ℝ) * v ≤ (G : ℝ) + v := by exact_mod_cast hCv
    calc
      (C : ℝ) * v ≤ (G : ℝ) + v := hCv'
      _ = (1 + (v : ℝ) / G) * G := by field_simp
  have hstep := Algebra.VectorInverse.one_add_div_le_rpow h128 hv2 hvG'
  have hpower : ((C : ℝ) * v / G) ^ L ≤ (v : ℝ) := by
    calc
      ((C : ℝ) * v / G) ^ L ≤
          ((v : ℝ) ^ Algebra.VectorInverse.chainExponent G) ^ L :=
        pow_le_pow_left₀ (by positivity) (hratio.trans hstep) L
      _ = (v : ℝ) ^ (Algebra.VectorInverse.chainExponent G * (L : ℝ)) := by
        rw [Real.rpow_mul hv0.le, Real.rpow_natCast]
      _ ≤ (v : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (chainExponent_mul_le_one hL hG)
      _ = (v : ℝ) := Real.rpow_one _
  have hmul : (C : ℝ) ^ L * (v : ℝ) ^ L ≤ (v : ℝ) * (G : ℝ) ^ L := by
    rw [div_pow, mul_pow] at hpower
    exact (div_le_iff₀ (pow_pos hG0 L)).mp hpower
  have hsplit : (v : ℝ) ^ L = (v : ℝ) ^ (L - 1) * v := by
    conv_lhs => rw [show L = (L - 1) + 1 by omega, pow_succ]
  rw [hsplit, ← mul_assoc, mul_comm (v : ℝ) ((G : ℝ) ^ L)] at hmul
  have hfinal := (mul_le_mul_iff_left₀ hv0).mp hmul
  exact_mod_cast hfinal

theorem ceilingPower_holds : CeilingPower := by
  intro L G v hL hG hv hvG
  exact ceiling_power hL hG hv hvG

end Praxis.Algebra.Power
