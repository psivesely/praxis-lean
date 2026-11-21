import Praxis.Proofs.View.ForwardCells
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open Polynomial

section Linear

variable {P : Params} [Fact (Nat.Prime P.q)]

noncomputable def cellForm (Dm : QAPData P) (W : Mat (Fq P) P.N)
    (s r y : Vec (Fq P) P.N) : Polynomial (Fq P) :=
  (∑ i, ∑ j, C (W i j) * (C (y i) * (C (r j) + Dm.A j) + Dm.A i * (Dm.B j - C (y j)))) +
    ∑ i, C (y i) * C (s i)

lemma cellForm_normal (Dm : QAPData P) (W : Mat (Fq P) P.N) (s r y : Vec (Fq P) P.N) :
    cellForm Dm W s r y =
      (∑ i, C (y i) * (C (W.mulVec r i + s i) + ∑ j, C (W i j - W j i) * Dm.A j)) +
        Dm.qapPoly W := cell_algebra Dm W s r y

lemma cellForm_zero (Dm : QAPData P) (W : Mat (Fq P) P.N) (s r : Vec (Fq P) P.N) :
    cellForm Dm W s r 0 = Dm.qapPoly W := by
  simp [cellForm_normal]

lemma cellForm_single (Dm : QAPData P) (W : Mat (Fq P) P.N) (s r : Vec (Fq P) P.N)
    (i : Fin (P.N + 1)) :
    cellForm Dm W s r (Pi.single i 1) =
      (C (W.mulVec r i + s i) + ∑ j, C (W i j - W j i) * Dm.A j) + Dm.qapPoly W := by
  classical
  simp [cellForm_normal, Pi.single_apply, ite_mul, apply_ite C]

lemma linear_poly_degree_le (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (c : Fq P) (f : Fin (P.N+1) → Fq P) :
    (C c + ∑ j, C (f j) * Dm.A j).natDegree ≤ P.D := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_le _ _).trans (Nat.le_of_lt (hD.A_degree j))

lemma symm_search_of_cellForm (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (hsize : Fintype.card (QAPIndex P) = P.D) (hsmall : P.D < P.q - P.D)
    (W : Mat (Fq P) P.N) (s r : Vec (Fq P) P.N) (b : Fq P → Fq P)
    (h : ∀ y τ, (∀ k, τ ≠ Dm.point k) → (cellForm Dm W s r y).eval τ + b τ = 0) :
    W.IsSymm ∧ W.mulVec r = -s := by
  classical
  have ha (i : Fin (P.N+1)) : W.mulVec r i + s i = 0 ∧ (fun j => W i j - W j i) = 0 := by
    apply A_indep Dm S hD
    apply tau_poly_zero Dm hsize
    · exact (linear_poly_degree_le Dm S hD _ _).trans_lt hsmall
    · intro τ hτ
      have hp := h (Pi.single i 1) τ hτ
      have hz := h 0 τ hτ
      rw [cellForm_single, eval_add] at hp
      rw [cellForm_zero] at hz
      linear_combination hp - hz
  refine ⟨?_, ?_⟩
  · change W.transpose = W
    ext i j
    exact (sub_eq_zero.mp (congrFun (ha i).2 j)).symm
  · ext i
    change W.mulVec r i = -(s i)
    linear_combination (ha i).1

lemma matrix_zero_of_quad (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (hsize : Fintype.card (QAPIndex P) = P.D) (hsmall : P.D < P.q - P.D)
    (htwo : (2 : Fq P) ≠ 0) (M : Mat (Fq P) P.N)
    (h : ∀ (y : Vec (Fq P) P.N) τ, (∀ k, τ ≠ Dm.point k) →
      ∑ i, ∑ j, M i j * y i * ((Dm.B j).eval τ - y j) = 0) : M = 0 := by
  classical
  ext i j
  have hp : (∑ j, C (M i j) * Dm.B j : Polynomial (Fq P)) = 0 := by
    apply tau_poly_zero Dm hsize
    · apply (natDegree_sum_le_of_forall_le _ _ (fun j _ =>
        (natDegree_C_mul_le _ _).trans (Nat.le_of_lt (hD.B_degree j)))).trans_lt hsmall
    · intro τ hτ
      have hh := quad_odd M (fun j => (Dm.B j).eval τ) htwo (fun y => h y τ hτ) i
      simpa only [eval_finsetSum, eval_mul, eval_C] using hh
  exact congrFun (B_indep Dm S hD (fun j => M i j) hp) j

end Linear

end Praxis.Proofs.View
