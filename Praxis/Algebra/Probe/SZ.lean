import Praxis.Algebra.Stmt.ProbeSZ
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

namespace Praxis.Algebra.ProbeSZ

open scoped BigOperators

theorem mulVec_columns {F m n : Type} [CommRing F] [Fintype n]
    (M : Matrix m n F) (v : n → F) :
    M.mulVec v = ∑ j, v j • (fun i => M i j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem uniformProb_mono {Ω : Type} [Fintype Ω] {E G : Ω → Prop}
    (h : ∀ x, E x → G x) : uniformProb E ≤ uniformProb G := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_subtype_mono E G h

theorem uniformProb_equiv {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (E : Ξ → Prop) : uniformProb (fun x => E (e x)) = uniformProb E := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl)), Fintype.card_congr e]

theorem uniformProb_polynomial_zero {p k d : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin k) (ZMod p)) (hP : P ≠ 0) (hd : P.totalDegree ≤ d) :
    uniformProb (fun x : Fin k → ZMod p => MvPolynomial.eval x P = 0) ≤
      (d : ℝ) / p := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := MvPolynomial.schwartz_zippel_totalDegree hP (Finset.univ : Finset (ZMod p))
  rw [Fintype.piFinset_univ, Finset.card_univ, ZMod.card] at h
  have hcount :
      (Finset.univ.filter (fun x : Fin k → ZMod p => MvPolynomial.eval x P = 0)).card * p ≤
        P.totalDegree * p ^ k := by
    have hh := (div_le_div_iff₀ (show (0 : ℚ≥0) < (p : ℚ≥0) ^ k by positivity)
      (show (0 : ℚ≥0) < p by exact_mod_cast hp)).mp h
    exact_mod_cast hh
  have hcount' :
      (Nat.card {x : Fin k → ZMod p // MvPolynomial.eval x P = 0}) * p ≤ d * p ^ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hcount.trans (Nat.mul_le_mul_right _ hd)
  unfold uniformProb
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  apply (div_le_div_iff₀ (show (0 : ℝ) < (p ^ k : ℕ) by positivity)
    (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
  exact_mod_cast hcount'

end Praxis.Algebra.ProbeSZ
