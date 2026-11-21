import Praxis.Proofs.Classification.Coordinates

namespace Praxis.Proofs.Classification

noncomputable section

section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {d : ℕ}

def equivMatrix (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) : Matrix (Fin d) (Fin d) k :=
  LinearMap.toMatrix' e.toLinearMap

theorem equivMatrix_symm (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) :
    equivMatrix e * equivMatrix e.symm = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, equivMatrix, equivMatrix, Matrix.toLin'_toMatrix',
    Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  apply LinearMap.ext
  intro x
  exact e.apply_symm_apply x

theorem equivMatrix_map_symm (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) :
    (equivMatrix e).map (algebraMap k F) * (equivMatrix e.symm).map (algebraMap k F) = 1 := by
  rw [← Matrix.map_mul, equivMatrix_symm, Matrix.map_one] <;> simp only [map_zero, map_one]

def extendEquiv (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) : (Fin d → F) ≃ₗ[F] (Fin d → F) where
  __ := ((equivMatrix e).map (algebraMap k F)).mulVecLin
  invFun := ((equivMatrix e.symm).map (algebraMap k F)).mulVec
  left_inv x := by
    change ((equivMatrix e.symm).map (algebraMap k F)).mulVec
      (((equivMatrix e).map (algebraMap k F)).mulVec x) = x
    rw [Matrix.mulVec_mulVec]
    have h := equivMatrix_map_symm (F := F) e.symm
    simp only [LinearEquiv.symm_symm] at h
    rw [h, Matrix.one_mulVec]
  right_inv x := by
    change ((equivMatrix e).map (algebraMap k F)).mulVec
      (((equivMatrix e.symm).map (algebraMap k F)).mulVec x) = x
    rw [Matrix.mulVec_mulVec, equivMatrix_map_symm, Matrix.one_mulVec]

theorem extendEquiv_apply (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) (x : Fin d → F) :
    extendEquiv (F := F) e x = ((equivMatrix e).map (algebraMap k F)).mulVec x := by
  rfl

theorem extendEquiv_apply_cast (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) (x : Fin d → k) :
    extendEquiv (F := F) e (fun i => algebraMap k F (x i)) =
      (fun i => algebraMap k F (e x i)) := by
  funext i
  change ((equivMatrix e).map (algebraMap k F)).mulVec _ i = _
  have h := (algebraMap k F).map_mulVec (equivMatrix e) x i
  rw [equivMatrix, LinearMap.toMatrix'_mulVec] at h
  simpa only [Function.comp_def, equivMatrix, LinearEquiv.coe_coe] using h.symm

end

end

end Praxis.Proofs.Classification
