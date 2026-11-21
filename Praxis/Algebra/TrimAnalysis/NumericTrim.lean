import Praxis.Algebra.TrimAnalysis.GaussianMoment

set_option autoImplicit false

set_option linter.style.haveILetI false

set_option linter.unusedSectionVars false

noncomputable section

open Finset Real

open scoped BigOperators

namespace Praxis.Analysis

variable {Ω : Type*} [Fintype Ω]

def FiniteLaw.prob (P : FiniteLaw Ω) (E : Set Ω) : ℝ := by
  classical
  exact ∑ s, if s ∈ E then P.weight s else 0

theorem FiniteLaw.exp_markov (P : FiniteLaw Ω) (q : Ω → ℝ)
    (b r : ℝ) (hb : 0 ≤ b) :
    P.prob {s | r < q s} ≤
      P.expect (fun s => Real.exp (b * q s / 2)) * Real.exp (-b*r/2) := by
  classical
  have h : P.prob {s | r < q s} * Real.exp (b*r/2) ≤
      P.expect (fun s => Real.exp (b*q s/2)) := by
    unfold FiniteLaw.prob FiniteLaw.expect
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : r < q s
    · simp only [Set.mem_ofPred_eq, hs, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith)) (P.nonneg s)
    · simp only [Set.mem_ofPred_eq, hs, ↓reduceIte, zero_mul]
      exact mul_nonneg (P.nonneg s) (Real.exp_pos _).le
  have hh := (le_div_iff₀ (Real.exp_pos (b*r/2))).mpr h
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_div, neg_mul] using hh

theorem two_lt_exp_694 : (2 : ℝ) < Real.exp (347/500) := by
  have h : (2 : ℝ) < ∑ k ∈ Finset.range 21,
      (347/500 : ℝ)^k / (k.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact h.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 21)

theorem FiniteLaw.event_trim (P : FiniteLaw Ω) (E K : Set Ω) (ε : ℝ)
    (houtside : P.prob Kᶜ ≤ ε) :
    P.prob E - ε ≤ P.prob (E ∩ K) := by
  classical
  have h : P.prob E ≤ P.prob (E ∩ K) + P.prob Kᶜ := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    by_cases hE : s ∈ E <;> by_cases hK : s ∈ K <;>
      simp [hE, hK, P.nonneg]
  linarith

end Praxis.Analysis
