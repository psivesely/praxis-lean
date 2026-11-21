import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false

namespace Praxis.Algebra.VectorInverse

open Set Finset

open scoped BigOperators NNReal

private lemma nnreal_strictConcave_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ≥0 Set.univ fun x : ℝ≥0 ↦ x ^ p := by
  have hp₀' : 0 < 1 / p := div_pos zero_lt_one hp₀
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  have h₁ : StrictConvexOn ℝ≥0 Set.univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow hp₁').2 x.2 y.2 (by simp [hxy]) ha hb (by simp; norm_cast)
  have h₂ : ∀ x, f.symm x = x ^ p := by simp [f, NNReal.orderIsoRpow_symm_eq]
  refine ⟨convex_univ, fun x mx y my hxy a b ha hb hab => ?_⟩
  simp only [← h₂]
  exact (f.strictConcaveOn_symm h₁).2 mx my hxy ha hb hab

private lemma real_strictConcave_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ p := by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let x' : ℝ≥0 := .mk x hx
  let y' : ℝ≥0 := .mk y hy
  let a' : ℝ≥0 := .mk a ha.le
  let b' : ℝ≥0 := .mk b hb.le
  have hxy' : x' ≠ y' := Subtype.coe_ne_coe.1 hxy
  have hab' : a' + b' = 1 := by ext; simp [a', b', hab]
  exact_mod_cast (nnreal_strictConcave_rpow hp₀ hp₁).2 (Set.mem_univ x') (Set.mem_univ y')
    hxy' (mod_cast ha) (mod_cast hb) hab'

noncomputable def chainExponent (g : ℝ) : ℝ := Real.log 2 / Real.log g

theorem two_endpoint {g : ℝ} (hg : 128 ≤ g) :
    1 + 2 / g ≤ (2 : ℝ) ^ chainExponent g := by
  have hg0 : 0 < g := by linarith
  have hlg : 0 < Real.log g := Real.log_pos (by linarith)
  have hl2 : (1 : ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h
    linarith
  have hl2u : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    linarith
  have hl128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlgub : Real.log g ≤ g / 8 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hg0 (by norm_num : (0 : ℝ) < 128))
    rw [Real.log_div hg0.ne' (by norm_num), hl128] at h
    linarith
  have hsq : (1 : ℝ)/4 ≤ Real.log 2 * Real.log 2 := by nlinarith
  have he : 2 / g ≤ Real.log 2 * chainExponent g := by
    unfold chainExponent
    apply (div_le_iff₀ hg0).mpr
    rw [show Real.log 2 * (Real.log 2 / Real.log g) * g =
      (Real.log 2 * Real.log 2 * g) / Real.log g by ring]
    apply (le_div_iff₀ hlg).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsq hg0.le]
  calc
    1 + 2 / g ≤ Real.exp (Real.log 2 * chainExponent g) :=
      (by linarith [Real.add_one_le_exp (2 / g)] : 1 + 2 / g ≤ Real.exp (2 / g)).trans
        (Real.exp_le_exp.mpr he)
    _ = _ := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm

theorem one_add_div_le_rpow {g v : ℝ} (hg : 128 ≤ g) (hv : 2 ≤ v) (hvg : v ≤ g) :
    1 + v / g ≤ v ^ chainExponent g := by
  have hg0 : 0 < g := by linarith
  have hlg : 0 < Real.log g := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log 2 < Real.log g := Real.log_lt_log (by norm_num) (by linarith)
  have ha0 : 0 < chainExponent g := div_pos hl2 hlg
  have ha1 : chainExponent g < 1 := (div_lt_one hlg).mpr hlog
  have hgg : g ^ chainExponent g = 2 := by
    rw [Real.rpow_def_of_pos hg0]
    unfold chainExponent
    rw [mul_div_cancel₀ _ hlg.ne', Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  let A := (g-v)/(g-2)
  let B := (v-2)/(g-2)
  have hA : 0 ≤ A := div_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ B := div_nonneg (by linarith) (by linarith)
  have hsum : A+B=1 := by dsimp [A,B]; field_simp [show g-2 ≠ 0 by linarith]; ring
  have hab : A*2+B*g=v := by dsimp [A,B]; field_simp [show g-2 ≠ 0 by linarith]; ring
  have hc := (real_strictConcave_rpow ha0 ha1).concaveOn.2
    (show (2 : ℝ) ∈ Set.Ici 0 by norm_num) (show g ∈ Set.Ici 0 from hg0.le) hA hB hsum
  simp only [smul_eq_mul, hab, hgg] at hc
  have hend := two_endpoint hg
  have hlin : A*(1+2/g)+B*2 = 1+v/g := by
    dsimp [A,B]
    field_simp [show g-2 ≠ 0 by linarith, hg0.ne']
    ring
  rw [← hlin]
  linarith [mul_le_mul_of_nonneg_left hend hA]

end Praxis.Algebra.VectorInverse
