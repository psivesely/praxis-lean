import Praxis.Proofs.Classification.Tensor
import Praxis.Proofs.Classification.Cubic

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {d : ℕ} {S : Type*} [Fintype S]

theorem mapTri_base_cube (φ : F →ₐ[k] F) (ξ : Fin d → k) :
    mapTri φ.toRingHom (cube (fun i => algebraMap k F (ξ i))) =
      cube (fun i => algebraMap k F (ξ i)) := by
  apply tri_ext
  intro i j l
  rw [mapTri_single]
  simp only [cube_apply, single_dotProduct, one_mul, map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]

theorem mapTri_base_sum (φ : F →ₐ[k] F) (c : S → F) (ξ : S → Fin d → k) :
    mapTri φ.toRingHom (∑ s, c s • cube (fun i => algebraMap k F (ξ s i))) =
      ∑ s, φ (c s) • cube (fun i => algebraMap k F (ξ s i)) := by
  rw [mapTri_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [mapTri_smul, mapTri_base_cube]
  rfl

theorem cube_edge_coefficients (φ : F →ₐ[k] F) (c : S → F) (ξ : S → Fin d → k)
    (hli : LinearIndependent F (fun s => Matrix.vecMulVec
      (fun i => algebraMap k F (ξ s i)) (fun i => algebraMap k F (ξ s i))))
    (Ξ : Tri F d) (hΞ : Ξ = ∑ s, c s • cube (fun i => algebraMap k F (ξ s i)))
    (l₀ l : Fin d → F)
    (hedge : slice Ξ l = slice (mapTri φ.toRingHom Ξ) l₀) :
    ∀ s, c s * dotProduct l (fun i => algebraMap k F (ξ s i)) =
      φ (c s) * dotProduct l₀ (fun i => algebraMap k F (ξ s i)) := by
  rw [hΞ, mapTri_base_sum, slice_sum, slice_sum] at hedge
  simp only [slice_smul, slice_cube, smul_smul] at hedge
  have hz : ∑ s,
      (c s * dotProduct l (fun i => algebraMap k F (ξ s i)) -
        φ (c s) * dotProduct l₀ (fun i => algebraMap k F (ξ s i))) •
      Matrix.vecMulVec (fun i => algebraMap k F (ξ s i))
        (fun i => algebraMap k F (ξ s i)) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hedge
  intro s
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ hz s)

end

end

end Praxis.Proofs.Classification
