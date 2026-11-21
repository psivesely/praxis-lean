import Praxis.Algebra.Rank3Branch.RankThreeLattice
import Praxis.Algebra.Conversion.Conversion
import Praxis.Combinatorics.Mass
import Mathlib.Data.Matrix.Mul
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Combinatorics.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.RankThree

open Finset Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def xi (g : ℕ) : ℝ := correction g ^ 254

noncomputable def heightBound (g : ℕ) (δ : ℝ) : ℝ := xi g / (δ - xi g / (g : ℝ))

theorem height_lt_of_chain {g : ℕ} {δ M : ℝ} (hg : 0 < g) (hM : 0 < M)
    (hδ : xi g / (g : ℝ) < δ)
    (h : δ / (g : ℝ) ^ 3 <
      (1 / (g : ℝ) ^ 3) * xi g * (1 / M + 1 / (g : ℝ))) :
    M < heightBound g δ := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hh : δ < xi g * (1 / M + 1 / (g : ℝ)) := by
    have he : (1 / (g : ℝ) ^ 3) * xi g * (1 / M + 1 / (g : ℝ)) =
        (xi g * (1 / M + 1 / (g : ℝ))) / (g : ℝ) ^ 3 := by ring
    rw [he, div_lt_div_iff_of_pos_right (pow_pos hg0 3)] at h
    exact h
  apply (lt_div_iff₀ (sub_pos.mpr hδ)).mpr
  have h' : δ - xi g / (g : ℝ) < xi g / M := by
    have he : xi g * (1 / M + 1 / (g : ℝ)) = xi g / M + xi g / (g : ℝ) := by ring
    rw [he] at hh
    linarith
  have := (lt_div_iff₀ hM).mp h'
  nlinarith

end Praxis.Algebra.RankThree
