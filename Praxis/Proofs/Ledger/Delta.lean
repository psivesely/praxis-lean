import Praxis.Proofs.Ledger.Split
import Praxis.Bounds.Ledger
import Praxis.Constants
import Praxis.Games
import Praxis.Ledger

namespace Praxis.Proofs.Ledger

private theorem ledgerE_mono {x y : ℕ} (hxy : x ≤ y) : ledgerE x ≤ ledgerE y := by
  let a : ℚ := (Constants.theta + 10 * Constants.eps_f) / 2
  let b : ℚ := ((Constants.L : ℚ) + 1 / 2) * Constants.theta +
    (4 * (Constants.L : ℚ) + 10) * Constants.eps_f +
    4 / (Constants.N_free : ℚ) + 4 / (2 : ℚ)^126
  have hp (w : ℕ) : ledgerE w = a * (w : ℚ)^2 + b * w + ledgerE 0 := by
    dsimp [a, b]
    unfold ledgerE ledgerJ choose2
    push_cast
    ring
  have ha : 0 ≤ a := by norm_num [a, Constants.theta, Constants.eps_f]
  have hb : 0 ≤ b := by
    dsimp [b]
    have ht : 0 ≤ Constants.theta := by norm_num [Constants.theta]
    have he : 0 ≤ Constants.eps_f := by norm_num [Constants.eps_f]
    positivity
  have hcast : (x : ℚ) ≤ (y : ℚ) := by exact_mod_cast hxy
  have hsquare : (x : ℚ)^2 ≤ (y : ℚ)^2 := by nlinarith [Nat.cast_nonneg (α := ℚ) x]
  rw [hp x, hp y]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hsquare), mul_nonneg hb (sub_nonneg.mpr hcast)]

theorem ledger_le_delta (Q : ℕ) (hQ : Q < Constants.T) :
    ledgerE (simBudget Q) ≤ 1 - Constants.ledger_delta := by
  have hw : simBudget Q ≤ Constants.W_budget := by
    simp only [simBudget, Constants.LT, Constants.W_budget]
    simp only [Constants.T] at hQ
    omega
  have hend : ledgerE Constants.W_budget = 1 - Constants.ledger_delta := by
    norm_num [ledgerE, ledgerJ, choose2, Constants.L, Constants.L1, Constants.L2,
      Constants.LT, Constants.T, Constants.N_free, Constants.eps_f, Constants.theta,
      Constants.statistical_seed, Constants.W_budget, Constants.ledger_delta]
  exact (ledgerE_mono hw).trans_eq hend

theorem ledger_min (Q : ℕ) (hQ : Q < Constants.T) :
    (ledgerE (simBudget Q) : ℝ) ≤
      min (((Q : ℝ) + 1) / (Constants.T : ℝ)) (1 - (Constants.ledger_delta : ℝ)) := by
  apply le_min
  · have hw : 2 * Q + 2 ≤ Constants.W_budget := by
      simp only [Constants.W_budget]
      simp only [Constants.T] at hQ
      omega
    have h := Praxis.Bounds.Ledger.budgetLine Q hw
    have hr := (Rat.cast_le (K := ℝ)).mpr h
    simpa [simBudget, Constants.LT] using hr
  · have hr := (Rat.cast_le (K := ℝ)).mpr (ledger_le_delta Q hQ)
    simpa using hr

end Praxis.Proofs.Ledger
