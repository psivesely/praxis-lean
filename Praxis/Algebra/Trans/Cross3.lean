import Praxis.Algebra.Trans.AlgModel

open scoped BigOperators

namespace Praxis.Algebra.Trans

variable {R : Type*} [CommRing R]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quadratic_weightedGram {r : ℕ} (B : Matrix ι (Fin r) R)
    (sigma : ι → R) (v : Fin r → R) :
    quadratic (weightedGram B sigma) v =
      ∑ l, sigma l ^ 2 * dotProduct (B l) v ^ 2 := by
  unfold quadratic weightedGram
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro l _
  change dotProduct (B l) v * (sigma l ^ 2 * dotProduct (B l) v) =
    sigma l ^ 2 * dotProduct (B l) v ^ 2
  ring

theorem dotProduct_crossProduct_eq_detRows3 (u v w : Fin 3 → R) :
    dotProduct w (crossProduct u v) = detRows3 u v w := by
  rw [triple_product_permutation, triple_product_eq_det]
  rfl

theorem weightedCross3 (B : Matrix ι (Fin 3) R) (sigma : ι → R) :
    WeightedCross3 B sigma := by
  intro i j
  rw [quadratic_weightedGram]
  simp only [dotProduct_crossProduct_eq_detRows3]

end Praxis.Algebra.Trans
