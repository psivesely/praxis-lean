import Praxis.Proofs.Classification.Annihilate
import Praxis.Proofs.Classification.Squares

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {d : ℕ}

def bilinEval (l h : Fin d → F) : Matrix (Fin d) (Fin d) F →ₗ[F] F :=
  ∑ i, ∑ j, (l i * h j) • matrixEntry i j

theorem bilinEval_apply (l h : Fin d → F) (M : Matrix (Fin d) (Fin d) F) :
    bilinEval l h M = rowForm l M h := by
  simp only [bilinEval, LinearMap.sum_apply, LinearMap.smul_apply, matrixEntry_apply,
    smul_eq_mul, rowForm_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem bilinEval_outer (l h ξ : Fin d → F) :
    bilinEval l h (Matrix.vecMulVec ξ ξ) = dotProduct l ξ * dotProduct h ξ := by
  simp only [bilinEval, LinearMap.sum_apply, LinearMap.smul_apply, matrixEntry_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem map_square_sum {ι : Type*} (xs : Finset ι) (e : ι → k) (ξ : ι → Fin d → k) :
    (∑ x ∈ xs, e x • Matrix.vecMulVec (ξ x) (ξ x)).map (algebraMap k F) =
      ∑ x ∈ xs, algebraMap k F (e x) •
        Matrix.vecMulVec (fun i => algebraMap k F (ξ x i)) (fun i => algebraMap k F (ξ x i)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, map_sum, map_mul]

theorem rowForm_square_sum {ι : Type*} (xs : Finset ι) (e : ι → k) (ξ : ι → Fin d → k)
    (l h : Fin d → F) :
    rowForm l ((∑ x ∈ xs, e x • Matrix.vecMulVec (ξ x) (ξ x)).map (algebraMap k F)) h =
      ∑ x ∈ xs, algebraMap k F (e x) *
        dotProduct l (fun i => algebraMap k F (ξ x i)) *
        dotProduct h (fun i => algebraMap k F (ξ x i)) := by
  rw [map_square_sum, ← bilinEval_apply, map_sum]
  simp only [map_smul, bilinEval_outer, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

end

end

end Praxis.Proofs.Classification
