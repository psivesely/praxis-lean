import Praxis.Algebra.Trans.AlgModel
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Praxis.Algebra.Trans

variable {R : Type*} [CommRing R]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem gram_entry (B : Matrix ι (Fin 2) R) (sigma : ι → R)
    (a b : Fin 2) :
    weightedGram B sigma a b = ∑ l, B l a * sigma l ^ 2 * B l b := by
  unfold weightedGram
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

private theorem quadratic_adjugate_two (A : Matrix (Fin 2) (Fin 2) R)
    (v : Fin 2 → R) :
    quadratic (Matrix.adjugate A) v =
      v 0 * (A 1 1 * v 0 + -A 0 1 * v 1) +
      v 1 * (-A 1 0 * v 0 + A 0 0 * v 1) := by
  simp [quadratic, Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

private theorem det_rows_two (u v : Fin 2 → R) :
    detRows2 u v = u 0 * v 1 - u 1 * v 0 := by
  exact Matrix.det_fin_two (Matrix.of ![u, v])

theorem weightedAdj2 (B : Matrix ι (Fin 2) R) (sigma : ι → R) :
    WeightedAdj2 B sigma := by
  intro i
  rw [quadratic_adjugate_two]
  simp only [gram_entry]
  simp only [Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [det_rows_two]
  ring

end Praxis.Algebra.Trans
