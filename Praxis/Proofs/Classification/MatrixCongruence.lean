import Praxis.Proofs.Basic

namespace Praxis.Proofs.Classification

noncomputable section

section

variable {F : Type*} [Field F] {I J : Type*} [Fintype J]

def matrixCongruence (B : Matrix I J F) : Matrix J J F →ₗ[F] Matrix I I F where
  toFun M := B * M * B.transpose
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r M := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem matrixCongruence_apply (B : Matrix I J F) (M : Matrix J J F) :
    matrixCongruence B M = B * M * B.transpose := rfl

theorem matrixCongruence_outer (B : Matrix I J F) (ξ : J → F) :
    matrixCongruence B (Matrix.vecMulVec ξ ξ) = Matrix.vecMulVec (B.mulVec ξ) (B.mulVec ξ) := by
  rw [matrixCongruence_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem mulVec_bijective_of_inverse {d : ℕ} (T U : Matrix (Fin d) (Fin d) F)
    (hTU : T * U = 1) (hUT : U * T = 1) : Function.Bijective T.mulVec := by
  constructor
  · intro x y h
    have h' := congrArg U.mulVec h
    simpa only [Matrix.mulVec_mulVec, hUT, Matrix.one_mulVec] using h'
  · intro x
    refine ⟨U.mulVec x, ?_⟩
    rw [Matrix.mulVec_mulVec, hTU, Matrix.one_mulVec]

end

end

end Praxis.Proofs.Classification
