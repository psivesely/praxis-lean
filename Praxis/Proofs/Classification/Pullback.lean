import Praxis.Proofs.Classification.Tensor
import Praxis.Proofs.Classification.Annihilate
import Praxis.Proofs.Classification.Cubic

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {F : Type*} [Field F] {d : ℕ}

def pullTri (T : Matrix (Fin d) (Fin d) F) (Ξ : Tri F d) : Tri F d where
  toFun h :=
    { toFun u := (Ξ (T.mulVecLin h) (T.mulVecLin u)) ∘ₗ T.mulVecLin
      map_add' u v := by ext w; simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply, LinearMap.comp_apply]
      map_smul' r u := by
        ext w
        simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply, LinearMap.comp_apply, RingHom.id_apply] }
  map_add' h h' := by
    ext u w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply, LinearMap.comp_apply]
  map_smul' r h := by
    ext u w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply, LinearMap.comp_apply, RingHom.id_apply]

theorem pullTri_apply (T : Matrix (Fin d) (Fin d) F) (Ξ : Tri F d) (h u w : Fin d → F) :
    pullTri T Ξ h u w = Ξ (T.mulVec h) (T.mulVec u) (T.mulVec w) := by
  simp only [pullTri, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Matrix.mulVecLin_apply]

theorem pullTri_symm (T : Matrix (Fin d) (Fin d) F) (Ξ : Tri F d) (h : SymTri Ξ) :
    SymTri (pullTri T Ξ) := by
  constructor
  · intro x u w
    simp only [pullTri_apply]
    exact h.1 _ _ _
  · intro x u w
    simp only [pullTri_apply]
    exact h.2 _ _ _

theorem pullTri_comp (S T : Matrix (Fin d) (Fin d) F) (Ξ : Tri F d) :
    pullTri S (pullTri T Ξ) = pullTri (T * S) Ξ := by
  apply tri_ext
  intro i j k
  simp only [pullTri_apply, Matrix.mulVec_mulVec]

theorem pullTri_one (Ξ : Tri F d) : pullTri 1 Ξ = Ξ := by
  apply tri_ext
  intro i j k
  simp only [pullTri_apply, Matrix.one_mulVec]

theorem pullTri_sum {A : Type*} (T : Matrix (Fin d) (Fin d) F) (s : Finset A) (Ξ : A → Tri F d) :
    pullTri T (∑ a ∈ s, Ξ a) = ∑ a ∈ s, pullTri T (Ξ a) := by
  apply tri_ext
  intro i j k
  simp only [pullTri_apply, LinearMap.sum_apply]

theorem pullTri_smul (T : Matrix (Fin d) (Fin d) F) (r : F) (Ξ : Tri F d) :
    pullTri T (r • Ξ) = r • pullTri T Ξ := by
  apply tri_ext
  intro i j k
  simp only [pullTri_apply, LinearMap.smul_apply]

theorem pullTri_cube (T : Matrix (Fin d) (Fin d) F) (ξ : Fin d → F) :
    pullTri T (cube ξ) = cube (T.transpose.mulVec ξ) := by
  apply tri_ext
  intro i j k
  simp only [pullTri_apply, cube_apply]
  have hd (v : Fin d → F) : dotProduct (T.mulVec v) ξ = dotProduct v (T.transpose.mulVec ξ) := by
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hd, hd, hd]

theorem pullTri_zero (T : Matrix (Fin d) (Fin d) F) : pullTri T (0 : Tri F d) = 0 := by
  apply tri_ext
  intro i j k
  simp only [pullTri_apply, LinearMap.zero_apply]

theorem slice_argument_smul (Ξ : Tri F d) (r : F) (h : Fin d → F) :
    slice Ξ (r • h) = r • slice Ξ h := by
  ext i j
  simp only [slice_apply, map_smul, LinearMap.smul_apply, Matrix.smul_apply]

theorem slice_pullback_injective (T : Matrix (Fin d) (Fin d) F) (hT : Function.Bijective T.mulVec)
    (Ξ : Tri F d) (hΞ : Function.Injective (slice Ξ)) : Function.Injective (slice (pullTri T Ξ)) := by
  intro h h' heq
  apply hT.1
  apply hΞ
  ext i j
  obtain ⟨u, hu⟩ := hT.2 (Pi.single i 1)
  obtain ⟨w, hw⟩ := hT.2 (Pi.single j 1)
  have hh := congrArg (fun M => rowForm u M w) heq
  rw [← tri_slice_eval, ← tri_slice_eval, pullTri_apply, pullTri_apply, hu, hw] at hh
  exact hh

end

end

end Praxis.Proofs.Classification
