import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

set_option autoImplicit false

set_option linter.style.haveILetI false

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Real Finset GaussianFourier

open scoped RealInnerProductSpace BigOperators

namespace Praxis.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem integral_exp_neg_mul_sq_norm_add {a : ℝ} (ha : 0 < a) (c : ℝ) (w : V) :
    (∫ v : V, Real.exp (-a * ‖v‖ ^ 2 + c * ⟪w, v⟫)) =
      (Real.pi / a) ^ ((Module.finrank ℝ V : ℝ) / 2) *
        Real.exp (c ^ 2 * ‖w‖ ^ 2 / (4 * a)) := by
  rw [← Complex.ofReal_inj]
  convert integral_cexp_neg_mul_sq_norm_add
    (show 0 < (a : ℂ).re from ha) (c : ℂ) w using 1
  · change Complex.ofRealLI (∫ v : V, Real.exp (-a * ‖v‖ ^ 2 + c * ⟪w, v⟫)) = _
    rw [← Complex.ofRealLI.integral_comp_comm]
    apply integral_congr_ae
    filter_upwards with v
    change (Real.exp (-a * ‖v‖ ^ 2 + c * ⟪w,v⟫) : ℂ) = _
    push_cast
    rfl
  · rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl

theorem integrable_exp_neg_mul_sq_norm_add {a : ℝ} (ha : 0 < a) (c : ℝ) (w : V) :
    Integrable (fun v : V => Real.exp (-a * ‖v‖ ^ 2 + c * ⟪w, v⟫)) := by
  by_contra h
  have heq := integral_exp_neg_mul_sq_norm_add ha c w
  rw [integral_undef h] at heq
  have : 0 < (Real.pi / a) ^ ((Module.finrank ℝ V : ℝ) / 2) *
      Real.exp (c ^ 2 * ‖w‖ ^ 2 / (4 * a)) := by positivity
  linarith

variable {Ω : Type*} [Fintype Ω]

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1

def FiniteLaw.expect (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ s, P.weight s * f s

omit [MeasurableSpace V] [BorelSpace V]

theorem quadratic_exp_moment_inner (P : FiniteLaw Ω) (X : Ω → V)
    (hmgf : ∀ u : V, P.expect (fun s => Real.exp ⟪u, X s⟫) ≤
      Real.exp (‖u‖ ^ 2 / 2)) (b : ℝ) (hb : 0 < b ∧ b < 1) :
    P.expect (fun s => Real.exp (b * ‖X s‖ ^ 2 / 2)) ≤
      (1-b) ^ (-(Module.finrank ℝ V : ℝ) / 2) := by
  classical
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  let a : ℝ := (Module.finrank ℝ V : ℝ) / 2
  let C : ℝ := (Real.pi / (1/2 : ℝ)) ^ a
  have hC : 0 < C := by dsimp [C]; positivity
  have hsqrt : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.1.le
  have hpoint (v : V) :
      (∑ s, P.weight s * Real.exp (-(1/2 : ℝ) * ‖v‖ ^ 2 +
        Real.sqrt b * ⟪X s, v⟫)) ≤
      Real.exp (-((1-b)/2) * ‖v‖ ^ 2) := by
    calc
      _ = Real.exp (-(1/2 : ℝ) * ‖v‖ ^ 2) *
          P.expect (fun s => Real.exp ⟪Real.sqrt b • v, X s⟫) := by
        simp only [FiniteLaw.expect, Real.exp_add, real_inner_smul_left,
          real_inner_comm v, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ ≤ Real.exp (-(1/2 : ℝ) * ‖v‖ ^ 2) *
          Real.exp (‖Real.sqrt b • v‖ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg b), mul_pow, hsqrt]
        congr 1
        ring
  have hint (s : Ω) : Integrable (fun v : V => P.weight s *
      Real.exp (-(1/2 : ℝ) * ‖v‖ ^ 2 + Real.sqrt b * ⟪X s, v⟫)) :=
    (integrable_exp_neg_mul_sq_norm_add (by norm_num : (0:ℝ)<1/2)
      (Real.sqrt b) (X s)).const_mul _
  have hrint : Integrable (fun v : V => Real.exp (-((1-b)/2) * ‖v‖ ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq_norm_add
      (show 0 < (1-b)/2 by linarith) 0 (0 : V)
  have hle := integral_mono (integrable_finsetSum _ (fun s _ => hint s)) hrint hpoint
  have hleft : (∫ v : V, ∑ s, P.weight s * Real.exp
      (-(1/2 : ℝ) * ‖v‖ ^ 2 + Real.sqrt b * ⟪X s, v⟫)) =
      C * P.expect (fun s => Real.exp (b * ‖X s‖ ^ 2 / 2)) := by
    rw [integral_finsetSum _ (fun s _ => hint s)]
    simp_rw [integral_const_mul, integral_exp_neg_mul_sq_norm_add
      (by norm_num : (0:ℝ)<1/2), hsqrt]
    simp only [FiniteLaw.expect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [C, a]
    norm_num
    ring
  have hright : (∫ v : V, Real.exp (-((1-b)/2) * ‖v‖ ^ 2)) =
      C * (1-b)^(-(Module.finrank ℝ V : ℝ)/2) := by
    rw [integral_rexp_neg_mul_sq_norm (show 0 < (1-b)/2 by linarith)]
    have hbase : Real.pi / ((1-b)/2) = (Real.pi / (1/2 : ℝ)) / (1-b) := by
      field_simp
    rw [hbase, Real.div_rpow (by positivity) (by linarith)]
    dsimp [C, a]
    rw [div_eq_mul_inv, ← Real.rpow_neg (show 0 ≤ 1-b by linarith)]
    congr 2
    ring
  rw [hleft, hright] at hle
  exact (mul_le_mul_iff_right₀ hC).mp hle

end Praxis.Analysis
