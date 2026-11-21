import Praxis.Proofs.Classification.RationalCubes
import Praxis.Proofs.Classification.Triangle
import Praxis.Proofs.Classification.Cubic
import Praxis.Proofs.Classification.Extend
import Praxis.Proofs.Classification.MatrixCongruence
import Praxis.Proofs.Classification.Pullback
import Praxis.Proofs.Classification.Tensor

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {d : ℕ}

theorem pullTri_base_fixed (φ : F →ₐ[k] F) (T : Matrix (Fin d) (Fin d) k) (Ξ : Tri F d)
    (hΞ : mapTri φ.toRingHom Ξ = Ξ) :
    mapTri φ.toRingHom (pullTri (T.map (algebraMap k F)) Ξ) = pullTri (T.map (algebraMap k F)) Ξ := by
  have hvec (i : Fin d) :
      (fun r => φ.toRingHom (((T.map (algebraMap k F)).mulVec (Pi.single i 1)) r)) =
        (T.map (algebraMap k F)).mulVec (Pi.single i 1) := by
    rw [Matrix.mulVec_single_one]
    funext r
    simp only [Matrix.col_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgHom.commutes]
  apply tri_ext
  intro i j l
  simp only [mapTri_single, pullTri_apply]
  have h := mapTri_apply φ.toRingHom Ξ
    ((T.map (algebraMap k F)).mulVec (Pi.single i 1))
    ((T.map (algebraMap k F)).mulVec (Pi.single j 1))
    ((T.map (algebraMap k F)).mulVec (Pi.single l 1))
  rw [hvec, hvec, hvec, hΞ] at h
  exact h.symm

theorem rational_zero_shape (hd : 0 < d) (hdim : d ≤ 3)
    (e : (Fin d → k) ≃ₗ[k] (Fin d → k)) (Ξ : Tri F d) (hsym : SymTri Ξ)
    (hb : ∀ h (j : Fin d), Ξ h (frameMatrix (F := F) e j) (frameMatrix (F := F) e j) = 0) :
    Ξ = 0 ∨ ∃ (t : F) (M : Tri F d), d = 3 ∧ Ξ = t • M ∧ Function.Injective (slice M) ∧
      ∀ φ : F →ₐ[k] F, mapTri φ.toRingHom M = M := by
  let R := frameMatrix (F := F) e
  let S := frameMatrix (F := F) e.symm
  let Ψ := pullTri R.transpose Ξ
  have hΨ : SymTri Ψ := pullTri_symm _ _ hsym
  have hbΨ : ∀ h (j : Fin d), Ψ h (Pi.single j 1) (Pi.single j 1) = 0 := by
    intro h j
    rw [pullTri_apply, Matrix.mulVec_single_one]
    exact hb _ j
  have hRS : R * S = 1 := equivMatrix_map_symm e
  have hSR : S * R = 1 := by
    simpa only [S, R, frameMatrix, LinearEquiv.symm_symm] using equivMatrix_map_symm (F := F) e.symm
  have heq : pullTri S.transpose Ψ = Ξ := by
    change pullTri S.transpose (pullTri R.transpose Ξ) = Ξ
    rw [pullTri_comp, ← Matrix.transpose_mul, hSR, Matrix.transpose_one, pullTri_one]
  by_cases hsmall : d ≤ 2
  · left
    rw [← heq, standard_zero_small hsmall Ψ hΨ hbΨ, pullTri_zero]
  · have hd3 : d = 3 := by omega
    subst d
    obtain ⟨t, ht⟩ := standard_zero3_shape Ψ hΨ hbΨ
    right
    refine ⟨t, pullTri S.transpose triangle, rfl, ?_, ?_, ?_⟩
    · rw [← heq, ht, pullTri_smul]
    · apply slice_pullback_injective _ _ _ slice_triangle_injective
      apply mulVec_bijective_of_inverse S.transpose R.transpose
      · rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
      · rw [← Matrix.transpose_mul, hSR, Matrix.transpose_one]
    · intro φ
      have hS : S.transpose = ((equivMatrix e.symm).transpose).map (algebraMap k F) := by
        change ((equivMatrix e.symm).map (algebraMap k F)).transpose = _
        rw [Matrix.transpose_map]
      rw [hS]
      exact pullTri_base_fixed φ _ _ (triangle_fixed φ.toRingHom)

end

end

end Praxis.Proofs.Classification
