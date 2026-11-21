import Praxis.Proofs.Monitor.Stop.RightPoly
import Praxis.Enc
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open MvPolynomial

noncomputable section

variable {P : Params} [Fact (Nat.Prime P.q)]

def coinDelta (c : Coins P) : Fq P :=
  coin c .Om22 * coin c .zeta * coin c .zeta' * coin c .zeta4 * coin c .eps

theorem coinDelta_ne_zero (pp : PublicParams P) (c : Coins P) (h : ValidCoins pp.qap c) :
    coinDelta c ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (h.2.1 .Om22 rfl) (h.2.1 .zeta rfl)
      · exact h.2.1 .zeta' rfl
    · exact h.2.1 .zeta4 rfl
  · exact h.2.2.1

def comparisonPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (D : ExprT P) (ι : Fq P) : MonPoly P :=
  ((keys1 P).map fun a => ((keys2 P).map fun b =>
    C (D.1 (a, b)) * leftPoly pp a * rightPoly pp v b).sum).sum +
    C D.2 * scalarX .alpha * keyPoly pp - C ι * keyPoly pp

private theorem eval_list_sum {α : Type} (ω : Assign P) (xs : List α) (f : α → MonPoly P) :
    MvPolynomial.eval (assignmentCoords ω) (xs.map f).sum =
      (xs.map fun x => MvPolynomial.eval (assignmentCoords ω) (f x)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

private theorem list_mul_sum {α : Type} (xs : List α) (a : Fq P) (f : α → Fq P) :
    (xs.map fun x => a * f x).sum = a * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

theorem eval_comparisonPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (D : ExprT P) (ι : Fq P) :
    MvPolynomial.eval (assignmentCoords ω) (comparisonPoly pp v D ι) =
      coinDelta ω.coins * (valT pp v ω D - ι * kappa pp ω.coins) := by
  simp only [comparisonPoly, map_sub, map_add, map_mul, eval_list_sum,
    MvPolynomial.eval_C, eval_leftPoly, eval_rightPoly pp v ω h, eval_keyPoly,
    scalarX, MvPolynomial.eval_X, assignmentCoords]
  change ((keys1 P).map fun a => ((keys2 P).map fun b =>
    D.1 (a, b) * e1At pp ω a * (coinDelta ω.coins * e2At pp v ω b)).sum).sum +
    D.2 * coin ω.coins .alpha * (coinDelta ω.coins * kappa pp ω.coins) -
      ι * (coinDelta ω.coins * kappa pp ω.coins) = _
  have hr : ∀ a b, D.1 (a, b) * e1At pp ω a * (coinDelta ω.coins * e2At pp v ω b) =
      coinDelta ω.coins * (D.1 (a, b) * (e1At pp ω a * e2At pp v ω b)) := by
    intros; ring
  simp_rw [hr, list_mul_sum]
  simp only [valT, gtExp]
  ring

theorem comparisonPoly_ne_zero (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (D : ExprT P) (ι : Fq P)
    (h : ¬ ∀ ω, ValidCoins pp.qap ω.coins →
      valT pp v ω D = ι * kappa pp ω.coins) : comparisonPoly pp v D ι ≠ 0 := by
  classical
  push Not at h
  obtain ⟨ω, hv, hne⟩ := h
  intro hz
  have he := eval_comparisonPoly pp v ω hv D ι
  rw [hz, map_zero] at he
  exact hne (sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left (coinDelta_ne_zero pp ω.coins hv)))

end

end Praxis.Proofs.Monitor
