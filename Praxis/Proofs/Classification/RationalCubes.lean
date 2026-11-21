import Praxis.Proofs.Classification.FrameCubes
import Praxis.Proofs.Classification.Extend
import Praxis.Proofs.Classification.Pullback
import Praxis.Proofs.Classification.MatrixCongruence
import Praxis.Proofs.Classification.Cubic

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {d : ℕ}

def frameMatrix (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) : Matrix (Fin d) (Fin d) F :=
  (equivMatrix e).map (algebraMap k F)

def framePoint (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) (s : Fin (2 ^ (d - 1))) : Fin d → k :=
  e.symm (boolPoint s)

theorem frame_point_equations (e : (Fin d → k) ≃ₗ[k] (Fin d → k))
    (s : Fin (2 ^ (d - 1))) : e (framePoint e s) = boolPoint s := e.apply_symm_apply _

theorem boolPoint_cast (s : Fin (2 ^ (d - 1))) :
    (fun i => algebraMap k F (boolPoint (F := k) s i)) = boolPoint (F := F) s := by
  funext i
  unfold boolPoint
  split_ifs <;> simp

theorem frame_matrix_point (e : (Fin d → k) ≃ₗ[k] (Fin d → k))
    (s : Fin (2 ^ (d - 1))) :
    (frameMatrix (F := F) e.symm).mulVec (boolPoint s) =
      fun i => algebraMap k F (framePoint e s i) := by
  rw [← boolPoint_cast (k := k) (F := F) s]
  have h := extendEquiv_apply_cast (F := F) e.symm (boolPoint s)
  simpa only [extendEquiv_apply, frameMatrix, framePoint] using h

theorem frame_matrix_image (e : (Fin d → k) ≃ₗ[k] (Fin d → k))
    (s : Fin (2 ^ (d - 1))) :
    (frameMatrix (F := F) e).mulVec (fun i => algebraMap k F (framePoint e s i)) = boolPoint s := by
  have h := extendEquiv_apply_cast (F := F) e (framePoint e s)
  rw [frame_point_equations, boolPoint_cast] at h
  simpa only [extendEquiv_apply, frameMatrix] using h

theorem frame_squares_independent (hd : 0 < d) (hdim : d ≤ 3)
    (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) :
    LinearIndependent F (fun s : Fin (2 ^ (d - 1)) =>
      Matrix.vecMulVec (fun i => algebraMap k F (framePoint e s i))
        (fun i => algebraMap k F (framePoint e s i))) := by
  apply LinearIndependent.of_comp (matrixCongruence (frameMatrix (F := F) e))
  change LinearIndependent F (fun s => matrixCongruence (frameMatrix (F := F) e)
    (Matrix.vecMulVec (fun i => algebraMap k F (framePoint e s i))
      (fun i => algebraMap k F (framePoint e s i))))
  simp_rw [matrixCongruence_outer, frame_matrix_image]
  exact standard_frame_squares hd hdim

theorem rational_frame_cubes (hd : 0 < d) (hdim : d ≤ 3)
    (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) (Ξ : Tri F d) (hsym : SymTri Ξ)
    (hb : ∀ h (j : Fin d), Ξ h (frameMatrix (F := F) e j)
      (frameMatrix (F := F) e j - frameMatrix (F := F) e ⟨0, hd⟩) = 0) :
    ∃ c : Fin (2 ^ (d - 1)) → F,
      Ξ = ∑ s, c s • cube (fun i => algebraMap k F (framePoint e s i)) := by
  let R := frameMatrix (F := F) e
  let S := frameMatrix (F := F) e.symm
  let Ψ := pullTri R.transpose Ξ
  have hΨ : SymTri Ψ := pullTri_symm _ _ hsym
  have hbΨ : ∀ h (j : Fin d), Ψ h (Pi.single j 1)
      (Pi.single j 1 - Pi.single ⟨0, hd⟩ 1) = 0 := by
    intro h j
    rw [pullTri_apply]
    rw [Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    exact hb _ j
  obtain ⟨c, hc⟩ := standard_frame_cubes hd hdim Ψ hΨ hbΨ
  have hRS : R * S = 1 := equivMatrix_map_symm e
  have hSR : S * R = 1 := by
    simpa only [S, R, frameMatrix, LinearEquiv.symm_symm] using equivMatrix_map_symm (F := F) e.symm
  have heq : pullTri S.transpose Ψ = Ξ := by
    change pullTri S.transpose (pullTri R.transpose Ξ) = Ξ
    rw [pullTri_comp, ← Matrix.transpose_mul, hSR, Matrix.transpose_one, pullTri_one]
  refine ⟨c, ?_⟩
  rw [← heq, hc, pullTri_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [pullTri_smul, pullTri_cube, Matrix.transpose_transpose, frame_matrix_point]

end

end

end Praxis.Proofs.Classification
