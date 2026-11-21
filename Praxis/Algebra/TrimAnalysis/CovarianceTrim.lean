import Praxis.Algebra.TrimAnalysis.GaussianMoment
import Praxis.Algebra.TrimAnalysis.NumericTrim

set_option autoImplicit false

set_option linter.style.haveILetI false

set_option linter.unusedSectionVars false

noncomputable section

open Finset Real Matrix

open scoped BigOperators RealInnerProductSpace

namespace Praxis.Analysis

variable {Ω : Type*} [Fintype Ω] {d : ℕ}

def mahalanobisSq (S : Matrix (Fin d) (Fin d) ℝ)
    (m x : Fin d → ℝ) : ℝ :=
  (x-m) ⬝ᵥ (S⁻¹ *ᵥ (x-m))

def DirectionalMGF (P : FiniteLaw Ω) (X : Ω → Fin d → ℝ)
    (m : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ u : Fin d → ℝ,
    P.expect (fun s => Real.exp (u ⬝ᵥ (X s - m))) ≤
      Real.exp ((u ⬝ᵥ (S *ᵥ u))/2)

theorem quadratic_exp_moment_covariance (P : FiniteLaw Ω)
    (X : Ω → Fin d → ℝ) (m : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (hmgf : DirectionalMGF P X m S)
    (b : ℝ) (hb : 0 < b ∧ b < 1) :
    P.expect (fun s => Real.exp (b * mahalanobisSq S m (X s) / 2)) ≤
      (1-b)^(-(d:ℝ)/2) := by
  have hi : S⁻¹.PosDef := Matrix.posDef_inv_iff.mpr hS
  letI : NormedAddCommGroup (Fin d → ℝ) := S⁻¹.toNormedAddCommGroup hi
  letI : SeminormedAddCommGroup (Fin d → ℝ) := S⁻¹.toSeminormedAddCommGroup hi.posSemidef
  letI : InnerProductSpace ℝ (Fin d → ℝ) := S⁻¹.toInnerProductSpace hi.posSemidef
  letI : Norm (Fin d → ℝ) := (S⁻¹.toSeminormedAddCommGroup hi.posSemidef).toNorm
  have hn (x : Fin d → ℝ) : ‖x‖^2 = x ⬝ᵥ (S⁻¹ *ᵥ x) := by
    rw [← real_inner_self_eq_norm_sq]
    change (S⁻¹ *ᵥ x) ⬝ᵥ star x = _
    simp [dotProduct_comm]
  have hin (u x : Fin d → ℝ) : ⟪u,x⟫ = (S⁻¹ *ᵥ u) ⬝ᵥ x := by
    rw [real_inner_comm]
    change (S⁻¹ *ᵥ u) ⬝ᵥ star x = _
    simp
  have hcancel (u : Fin d → ℝ) : S *ᵥ (S⁻¹ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hS.det_pos.ne'), Matrix.one_mulVec]
  have hdir (u : Fin d → ℝ) :
      P.expect (fun s => Real.exp ⟪u, X s-m⟫) ≤ Real.exp (‖u‖^2/2) := by
    simpa only [hin, hcancel, hn, dotProduct_comm] using hmgf (S⁻¹ *ᵥ u)
  have h := quadratic_exp_moment_inner P (fun s => X s-m) hdir b hb
  simpa only [hn, mahalanobisSq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h

theorem ellipsoid_tail (P : FiniteLaw Ω) (X : Ω → Fin d → ℝ)
    (m : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (hmgf : DirectionalMGF P X m S) (b R : ℝ) (hb : 0 < b ∧ b < 1) :
    P.prob {s | R^2 < mahalanobisSq S m (X s)} ≤
      (1-b)^(-(d:ℝ)/2) * Real.exp (-b*R^2/2) := by
  exact (P.exp_markov _ b (R^2) hb.1.le).trans
    (mul_le_mul_of_nonneg_right
      (quadratic_exp_moment_covariance P X m S hS hmgf b hb) (Real.exp_pos _).le)

end Praxis.Analysis
