import Praxis.Algebra.Trans.AlgModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Praxis.Algebra.Trans

variable {R : Type*} [CommRing R]

private def cofactorTerm (A B : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  !![A 1 1 * B 2 2 - A 1 2 * B 2 1,
    -(A 0 1 * B 2 2) + A 0 2 * B 2 1,
    A 0 1 * B 1 2 - A 0 2 * B 1 1;
    -(A 1 0 * B 2 2) + A 1 2 * B 2 0,
    A 0 0 * B 2 2 - A 0 2 * B 2 0,
    -(A 0 0 * B 1 2) + A 0 2 * B 1 0;
    A 1 0 * B 2 1 - A 1 1 * B 2 0,
    -(A 0 0 * B 2 1) + A 0 1 * B 2 0,
    A 0 0 * B 1 1 - A 0 1 * B 1 0]

private def rowOuter (w : R) (u : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun a b => w * u a * u b

private theorem adjugate_sum {ι : Type*} [Fintype ι]
    (M : ι → Matrix (Fin 3) (Fin 3) R) :
    Matrix.adjugate (∑ l, M l) = ∑ l, ∑ j, cofactorTerm (M l) (M j) := by
  rw [Matrix.adjugate_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cofactorTerm, Matrix.sum_apply, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_neg_distrib] <;>
    simp_rw [Finset.sum_mul, Finset.mul_sum]

private theorem cofactorTerm_row_self (w : R) (u v : Fin 3 → R) :
    quadratic (cofactorTerm (rowOuter w u) (rowOuter w u)) v = 0 := by
  simp [quadratic, cofactorTerm, rowOuter, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

private theorem cofactorTerm_row_pair (w t : R) (u z v : Fin 3 → R) :
    quadratic (cofactorTerm (rowOuter w u) (rowOuter t z)) v +
      quadratic (cofactorTerm (rowOuter t z) (rowOuter w u)) v =
      w * t * detRows3 v u z ^ 2 := by
  unfold detRows3
  erw [Matrix.det_fin_three]
  simp [quadratic, cofactorTerm, rowOuter, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

private theorem sum_pair_orientations {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → R) (hdiag : ∀ l, f l l = 0) :
    (∑ l, ∑ j, f l j) =
      ∑ l, ∑ j ∈ Finset.univ.filter (fun j => l < j), (f l j + f j l) := by
  have split (l j : ι) : f l j =
      (if l < j then f l j else 0) + (if j < l then f l j else 0) := by
    rcases lt_trichotomy l j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j
      simp [hdiag]
    · simp [h, not_lt_of_gt h]
  calc
    (∑ l, ∑ j, f l j) = ∑ l, ∑ j,
        ((if l < j then f l j else 0) + (if j < l then f l j else 0)) := by
      exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => split l j))
    _ = (∑ l, ∑ j, if l < j then f l j else 0) +
        (∑ l, ∑ j, if j < l then f l j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ l, ∑ j, if l < j then f l j else 0) +
        (∑ l, ∑ j, if l < j then f j l else 0) := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ l, ∑ j ∈ Finset.univ.filter (fun j => l < j), (f l j + f j l) := by
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp

private theorem weightedGram_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι (Fin 3) R) (sigma : ι → R) :
    weightedGram B sigma = ∑ l, rowOuter (sigma l ^ 2) (B l) := by
  unfold weightedGram
  ext a b
  rw [Matrix.mul_apply]
  simp [rowOuter, Matrix.transpose_apply, Matrix.sum_apply,
    mul_comm, mul_left_comm]

private theorem quadratic_sum {ι : Type*} [Fintype ι]
    (M : ι → Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    quadratic (∑ l, M l) v = ∑ l, quadratic (M l) v := by
  simp only [quadratic, Matrix.sum_mulVec, dotProduct_sum]

theorem weightedPairs3 {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : Matrix ι (Fin 3) R) (sigma : ι → R) : WeightedPairs3 B sigma := by
  intro i
  rw [weightedGram_eq_sum, adjugate_sum, quadratic_sum]
  simp_rw [quadratic_sum]
  rw [sum_pair_orientations (ι := ι) _
    (fun l => cofactorTerm_row_self (sigma l ^ 2) (B l) (B i))]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  exact cofactorTerm_row_pair _ _ _ _ _

end Praxis.Algebra.Trans
