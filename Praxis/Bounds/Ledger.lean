import Praxis.Ledger
import Mathlib.Tactic
import Praxis.Constants

namespace Praxis.Bounds.Ledger

open Praxis.Constants

theorem ledgerE_quadratic : ∃ b c : ℚ, ∀ w : ℕ,
    Praxis.ledgerE w = (theta + 10 * eps_f) / 2 * (w : ℚ)^2 + b * w + c := by
  refine ⟨((L : ℚ) + 1 / 2) * theta + (4 * (L : ℚ) + 10) * eps_f +
    4 / (N_free : ℚ) + 4 / (2 : ℚ)^126, Praxis.ledgerE 0, ?_⟩
  intro w
  unfold Praxis.ledgerE Praxis.ledgerJ Praxis.choose2
  push_cast
  ring

private theorem quadratic_below_chord {a b c m x : ℚ}
    (ha : 0 ≤ a) (hm : 0 < m) (hx : 0 ≤ x) (hxm : x ≤ m)
    (h0 : c ≤ 2 / (m + 2)) (h1 : a * m ^ 2 + b * m + c ≤ 1) :
    a * x ^ 2 + b * x + c ≤ (x + 2) / (m + 2) := by
  have hgap : 0 ≤ a * m * x * (m - x) :=
    mul_nonneg (mul_nonneg (mul_nonneg ha hm.le) hx) (sub_nonneg.mpr hxm)
  have hcurve : m * (a * x ^ 2 + b * x + c) ≤
      (m - x) * c + x * (a * m ^ 2 + b * m + c) := by
    nlinarith only [hgap]
  have hbound : m * (a * x ^ 2 + b * x + c) ≤ m * ((x + 2) / (m + 2)) := by
    calc
      _ ≤ (m - x) * c + x * (a * m ^ 2 + b * m + c) := hcurve
      _ ≤ (m - x) * (2 / (m + 2)) + x * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hxm))
          (mul_le_mul_of_nonneg_left h1 hx)
      _ = _ := by
        have hm1 : m + 2 ≠ 0 := ne_of_gt (by linarith)
        field_simp [hm1]
        ring
  exact le_of_mul_le_mul_left hbound hm

theorem budgetLine (Q : ℕ) (hQ : 2 * Q + 2 ≤ W_budget) :
    Praxis.ledgerE (2 * Q + 2) ≤ ((Q : ℚ) + 1) / T := by
  obtain ⟨b, c, hpoly⟩ := ledgerE_quadratic
  let a : ℚ := (theta + 10 * eps_f) / 2
  let m : ℚ := (W_budget : ℚ) - 2
  let x : ℚ := 2 * (Q : ℚ)
  have ha : 0 ≤ a := by norm_num [a, theta, eps_f]
  have hm : 0 < m := by norm_num [m, W_budget]
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxm : x ≤ m := by
    dsimp [x, m]
    have h : (2 * (Q : ℚ) + 2) ≤ (W_budget : ℚ) := by exact_mod_cast hQ
    linarith
  have he0 : Praxis.ledgerE 2 ≤ 2 / (W_budget : ℚ) := by
    norm_num [Praxis.ledgerE, Praxis.ledgerJ, Praxis.choose2, L, L1, L2, Constants.LT, T,
      N_free, eps_f, theta, statistical_seed, W_budget]
  have he1 : Praxis.ledgerE W_budget ≤ 1 := by
    norm_num [Praxis.ledgerE, Praxis.ledgerJ, Praxis.choose2, L, L1, L2, Constants.LT, T,
      N_free, eps_f, theta, statistical_seed, W_budget]
  have h0 : a * 2^2 + b * 2 + c ≤ 2 / (m + 2) := by
    have h := hpoly 2
    dsimp [m, a] at *
    norm_num at h
    rw [h] at he0
    norm_num only [sub_add_cancel, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_succ, pow_zero, mul_one] at ⊢
    linarith
  have h1 : a * m ^ 2 + (4*a + b)*m + (a*2^2+b*2+c) ≤ 1 := by
    have h := hpoly W_budget
    dsimp [a, m] at *
    rw [h] at he1
    nlinarith
  have h := quadratic_below_chord ha hm hx hxm h0 h1
  have hp := hpoly (2 * Q + 2)
  dsimp [x, m, a] at *
  push_cast at hp
  have hW : (W_budget : ℚ) = 2 * (T : ℚ) := by norm_num [W_budget, T]
  rw [hW] at h
  simp only [sub_add_cancel] at h
  have heq : (2 * (Q : ℚ) + 2) / (2 * (T : ℚ)) = ((Q : ℚ) + 1) / T := by ring
  rw [heq] at h
  rw [hp]
  nlinarith

end Praxis.Bounds.Ledger
