import Praxis.Proofs.Monitor.Stop.Numerator
import Mathlib.Algebra.MvPolynomial.CommRing
import Praxis.Enc
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Proofs.Monitor.Stop.RightPoly
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open MvPolynomial

noncomputable section

variable {P : Params} [Fact (Nat.Prime P.q)]

private theorem degree_list_sum {α : Type} (xs : List α) (f : α → MonPoly P) (d : ℕ)
    (h : ∀ a ∈ xs, (f a).totalDegree ≤ d) : (xs.map f).sum.totalDegree ≤ d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact h x (by simp)
    · exact ih (fun a ha => h a (by simp [ha]))

theorem degree_comparisonPoly_of_leaf_bounds (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (D : ExprT P) (ι : Fq P)
    (dL dR dK : ℕ)
    (hL : ∀ a, (leftPoly pp a).totalDegree ≤ dL)
    (hR : ∀ b, (rightPoly pp v b).totalDegree ≤ dR)
    (hK : (keyPoly pp).totalDegree ≤ dK)
    (hbound : dK + 1 ≤ dL + dR) :
    (comparisonPoly pp v D ι).totalDegree ≤ dL + dR := by
  have hp : ∀ a b, (C (D.1 (a, b)) * leftPoly pp a * rightPoly pp v b).totalDegree ≤
      dL + dR := by
    intro a b
    have h₁ := MvPolynomial.totalDegree_mul (C (D.1 (a, b))) (leftPoly pp a)
    have h₂ := MvPolynomial.totalDegree_mul (C (D.1 (a, b)) * leftPoly pp a)
      (rightPoly pp v b)
    simp only [MvPolynomial.totalDegree_C, zero_add] at h₁
    exact h₂.trans (Nat.add_le_add (h₁.trans (hL a)) (hR b))
  have hsum : (((keys1 P).map fun a => ((keys2 P).map fun b =>
      C (D.1 (a, b)) * leftPoly pp a * rightPoly pp v b).sum).sum).totalDegree ≤ dL + dR := by
    apply degree_list_sum
    intro a _
    apply degree_list_sum
    intro b _
    exact hp a b
  have hkey : (C D.2 * scalarX .alpha * keyPoly pp).totalDegree ≤ dL + dR := by
    have h₁ := MvPolynomial.totalDegree_mul (C D.2 : MonPoly P) (scalarX .alpha)
    have h₂ := MvPolynomial.totalDegree_mul (C D.2 * scalarX .alpha : MonPoly P) (keyPoly pp)
    simp only [MvPolynomial.totalDegree_C, zero_add, scalarX, MvPolynomial.totalDegree_X] at h₁
    simp only [scalarX] at h₂ ⊢
    omega
  have hι : (C ι * keyPoly pp).totalDegree ≤ dL + dR := by
    have h := MvPolynomial.totalDegree_mul (C ι : MonPoly P) (keyPoly pp)
    simp only [MvPolynomial.totalDegree_C, zero_add] at h
    omega
  unfold comparisonPoly
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_add _ _).trans (max_le hsum hkey)
  · exact hι

end

end Praxis.Proofs.Monitor
