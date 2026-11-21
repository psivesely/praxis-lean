import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Praxis.Constants

set_option autoImplicit false

open Finset Filter Topology

namespace Praxis.Lift

noncomputable def arctanTerm (x : ℝ) (i : ℕ) : ℝ := x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)

theorem arctanTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (arctanTerm x) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  unfold arctanTerm
  have h1 : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have h2 : ((2 * n + 1 : ℕ) : ℝ) ≤ ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega)
  have h3 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  exact div_le_div₀ (pow_nonneg hx0 _) h1 h3 h2

theorem tendsto_arctan_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * arctanTerm x i) atTop
      (𝓝 (Real.arctan x)) := by
  have hs := Real.hasSum_arctan (x := x) (by rwa [Real.norm_eq_abs, abs_of_nonneg hx0])
  have ht := hs.tendsto_sum_nat
  simpa only [arctanTerm, mul_div_assoc] using ht

theorem arctan_le_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    Real.arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * arctanTerm x i :=
  Antitone.tendsto_le_alternating_series (tendsto_arctan_partial hx0 hx1)
    (arctanTerm_antitone hx0 hx1.le) k

theorem partial_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * arctanTerm x i ≤ Real.arctan x :=
  Antitone.alternating_series_le_tendsto (tendsto_arctan_partial hx0 hx1)
    (arctanTerm_antitone hx0 hx1.le) k

theorem pi_lt_pi_up : Real.pi < ((Praxis.Constants.lift_exact_values_pi_up : ℚ) : ℝ) := by
  have hM := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hu := arctan_le_partial (x := (5 : ℝ)⁻¹) (by norm_num) (by norm_num) 18
  have hl := partial_le_arctan (x := (239 : ℝ)⁻¹) (by norm_num) (by norm_num) 6
  have hbound : 16 * (∑ i ∈ range (2 * 18 + 1), (-1 : ℝ) ^ i * arctanTerm (5 : ℝ)⁻¹ i) -
      4 * (∑ i ∈ range (2 * 6), (-1 : ℝ) ^ i * arctanTerm (239 : ℝ)⁻¹ i) <
      ((Praxis.Constants.lift_exact_values_pi_up : ℚ) : ℝ) := by
    simp only [arctanTerm]
    norm_num [Finset.sum_range_succ, Praxis.Constants.lift_exact_values_pi_up]
  linarith

end Praxis.Lift
