import Praxis.Combinatorics.Chain
import Praxis.Combinatorics.Mass

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Combinatorics.UnequalChain

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def correction (g : ℕ) : ℝ := 1 + 2 / (g : ℝ)

theorem merging_reciprocal {g a b : ℝ} (hg : 0 < g) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 / a + 1 / g) * (1 / b + 1 / g) ≤
      (1 + 2 / g) * (1 / (a * b) + 1 / g) := by
  have h := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  apply (mul_le_mul_iff_left₀ (show 0 < a * b * g ^ 2 by positivity)).mp
  field_simp
  nlinarith

theorem ceil_factor_le {G v g : ℕ} (hg : 0 < g) (hG : g ≤ G) (hv : 0 < v) :
    (((G + v - 1) / v : ℕ) : ℝ) / G ≤ 1 / (v : ℝ) + 1 / (g : ℝ) := by
  have hG0 : (0 : ℝ) < G := by exact_mod_cast lt_of_lt_of_le hg hG
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hc : (((G + v - 1) / v : ℕ) : ℝ) * v ≤ G + v := by
    exact_mod_cast (Nat.div_mul_le_self (G + v - 1) v).trans (show G + v - 1 ≤ G + v by omega)
  have hGG : (g : ℝ) ≤ G := by exact_mod_cast hG
  have hinv : 1 / (G : ℝ) ≤ 1 / (g : ℝ) := one_div_le_one_div_of_le hg0 hGG
  calc
    (((G + v - 1) / v : ℕ) : ℝ) / G ≤ 1 / (v : ℝ) + 1 / (G : ℝ) := by
      apply (mul_le_mul_iff_left₀ (show 0 < (v : ℝ) * G by positivity)).mp
      field_simp
      nlinarith
    _ ≤ _ := add_le_add le_rfl hinv

def maxNorm (y : ι → ℤ) : ℕ := univ.sup fun i => (y i).natAbs

theorem natAbs_le_maxNorm (y : ι → ℤ) (i : ι) : (y i).natAbs ≤ maxNorm y :=
  le_sup (f := fun i => (y i).natAbs) (mem_univ i)

end Praxis.Combinatorics.UnequalChain
