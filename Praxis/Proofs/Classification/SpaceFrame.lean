import Praxis.Proofs.Classification.FinFrame
import Praxis.Proofs.Classification.RationalCubes
import Praxis.Proofs.Classification.Coordinates
import Praxis.Proofs.Classification.Extend
import Praxis.Proofs.Classification.Frame
import Praxis.Proofs.Classification.FrameCubes

namespace Praxis.Proofs.Classification

noncomputable section

section

variable {k : Type*} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    (V : Submodule k (I → k))

theorem coordinate_frame (i₀ : I) (h₀ : evalAt V i₀ ≠ 0) :
    ∃ (e : (Fin (Module.finrank k V) → k) ≃ₗ[k] (Fin (Module.finrank k V) → k))
      (idx : Fin (Module.finrank k V) → I) (j₀ : Fin (Module.finrank k V)),
      j₀.val = 0 ∧ idx j₀ = i₀ ∧ ∀ a j, e a j = coordIn V a (idx j) := by
  classical
  obtain ⟨d, hd, b, idx, hidx₀, hb⟩ := fin_coordinate_dual_basis V i₀ h₀
  let ef := finCongr hd
  let b' := b.reindex ef
  let idx' := fun j => idx (ef.symm j)
  let j₀ := ef (0 : Fin (d + 1))
  let e := (Module.finBasis k V).equivFun.symm.trans (frameEquiv V b')
  refine ⟨e, idx', j₀, ?_, ?_, ?_⟩
  · exact finCongr_apply_coe hd (0 : Fin (d + 1))
  · dsimp only [idx', j₀]
    rw [Equiv.symm_apply_apply, hidx₀]
  · intro a j
    simp only [e, LinearEquiv.trans_apply, frameEquiv_apply, b', Module.Basis.reindex_apply, hb,
      evalAt_apply, coordIn, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rfl

theorem frame_matrix_entry
    (e : (Fin (Module.finrank k V) → k) ≃ₗ[k] (Fin (Module.finrank k V) → k))
    (idx : Fin (Module.finrank k V) → I)
    (he : ∀ a j, e a j = coordIn V a (idx j)) (j r : Fin (Module.finrank k V)) :
    equivMatrix e j r = basisMat V (idx j) r := by
  rw [equivMatrix, LinearMap.toMatrix'_apply]
  simp only [LinearEquiv.coe_coe]
  rw [he]
  have h := congrFun (basisMat_mulVec V (Pi.single r 1)).symm (idx j)
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem frame_point_normalized (i₀ : I)
    (e : (Fin (Module.finrank k V) → k) ≃ₗ[k] (Fin (Module.finrank k V) → k))
    (idx : Fin (Module.finrank k V) → I) (j₀ : Fin (Module.finrank k V))
    (hj₀ : j₀.val = 0) (hidx : idx j₀ = i₀)
    (he : ∀ a j, e a j = coordIn V a (idx j))
    (s : Fin (2 ^ (Module.finrank k V - 1))) :
    coordIn V (framePoint e s) i₀ = 1 := by
  have h := congrFun (frame_point_equations e s) j₀
  rw [he, hidx] at h
  simpa [boolPoint, hj₀] using h

end

end

end Praxis.Proofs.Classification
