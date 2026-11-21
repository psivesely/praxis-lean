import Praxis.Proofs.Classification.Transport
import Praxis.Proofs.Classification.Tensor
import Praxis.Proofs.Classification.MatrixCongruence
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Compress
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Coordinates
import Praxis.Proofs.Classification.Cubic
import Praxis.Proofs.Classification.Serialization
import Praxis.Proofs.Classification.WeightEquations
import Praxis.Proofs.Classification.ZCoordinates
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

open Praxis.Algebra (Vec)

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

theorem coordinate_field_image (V : Submodule (Fq P0) (Vec (Fq P0) P0.N))
    (ξ : Fin (Module.finrank (Fq P0) V) → Fq P0) :
    ((basisMat V).map (algebraMap (Fq P0) (KummerField P0))).mulVec
      (fun r => algebraMap (Fq P0) (KummerField P0) (ξ r)) =
      (fun i => algebraMap (Fq P0) (KummerField P0) (coordIn V ξ i)) := by
  funext i
  have h := (algebraMap (Fq P0) (KummerField P0)).map_mulVec (basisMat V) ξ i
  rw [basisMat_mulVec] at h
  simpa only [Function.comp_def] using h.symm

theorem Bext_coordinate_dot (W : Stack P0)
    (ξ : Fin (Module.finrank (Fq P0) (jointSpace W)) → Fq P0) (i : Fin (P0.N + 1)) :
    dotProduct (Bext W i) (fun r => algebraMap (Fq P0) (KummerField P0) (ξ r)) =
      algebraMap (Fq P0) (KummerField P0) (coordIn (jointSpace W) ξ i) := by
  have h := congrFun (coordinate_field_image (jointSpace W) ξ) i
  simpa only [Bext, Matrix.mulVec] using h

theorem coordinate_zeta_dot (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (ξ : Fin (Module.finrank (Fq P0) (jointSpace W)) → Fq P0) (s : ℕ) :
    dotProduct (zeta v W s) (fun i => algebraMap (Fq P0) (KummerField P0) (ξ i)) =
      kConj s (Z v (coordIn (jointSpace W) ξ)) := by
  unfold zeta
  have h := Z_conj_coordinate_sum v (jointSpace W) ξ s
  simpa only [dotProduct, mul_comm] using h.symm

theorem reconstruct_decomposition {S : Type*} [Fintype S]
    (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (hsym : ∀ c, (W c).IsSymm)
    (Ξ : Tri (KummerField P0) (Module.finrank (Fq P0) (jointSpace W)))
    (hu : slice Ξ (zeta v W (P0.m - 1)) = CU W)
    (hv : slice Ξ (zeta v W P0.m) = CV W)
    (ξ : S → Fin (Module.finrank (Fq P0) (jointSpace W)) → Fq P0) (r : S → Fq P0)
    (hΞ : Ξ = ∑ s,
      (algebraMap (Fq P0) (KummerField P0) (r s) * Z v (coordIn (jointSpace W) (ξ s))) •
        cube (fun i => algebraMap (Fq P0) (KummerField P0) (ξ s i))) :
    W = ∑ s, r s • honestStack v (coordIn (jointSpace W) (ξ s)) := by
  have hC (s : ℕ) : slice Ξ (zeta v W s) =
      ∑ a, (algebraMap (Fq P0) (KummerField P0) (r a) * Z v (coordIn (jointSpace W) (ξ a)) *
        kConj s (Z v (coordIn (jointSpace W) (ξ a)))) •
      Matrix.vecMulVec (fun i => algebraMap (Fq P0) (KummerField P0) (ξ a i))
        (fun i => algebraMap (Fq P0) (KummerField P0) (ξ a i)) := by
    rw [hΞ, slice_sum]
    simp only [slice_smul, slice_cube, coordinate_zeta_dot, smul_smul]
  have hU : UField W = ∑ s, r s • UField (honestStack v (coordIn (jointSpace W) (ξ s))) := by
    calc
      UField W = matrixCongruence (Bext W) (CU W) := UField_factor W hsym
      _ = ∑ s, (algebraMap (Fq P0) (KummerField P0) (r s) * Z v (coordIn (jointSpace W) (ξ s)) *
          kConj (P0.m - 1) (Z v (coordIn (jointSpace W) (ξ s)))) •
          Matrix.vecMulVec
            (fun i => algebraMap (Fq P0) (KummerField P0) (coordIn (jointSpace W) (ξ s) i))
            (fun i => algebraMap (Fq P0) (KummerField P0) (coordIn (jointSpace W) (ξ s) i)) := by
        rw [← hu, hC, map_sum]
        simp only [map_smul, matrixCongruence_outer, Bext, coordinate_field_image]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        rw [UField_honest]
        rw [← smul_assoc]
        ext i j
        simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
          smul_eq_mul]
        ring
  have hV : VField W = ∑ s, r s • VField (honestStack v (coordIn (jointSpace W) (ξ s))) := by
    calc
      VField W = matrixCongruence (Bext W) (CV W) := VField_factor W hsym
      _ = ∑ s, (algebraMap (Fq P0) (KummerField P0) (r s) * Z v (coordIn (jointSpace W) (ξ s)) *
          kConj P0.m (Z v (coordIn (jointSpace W) (ξ s)))) •
          Matrix.vecMulVec
            (fun i => algebraMap (Fq P0) (KummerField P0) (coordIn (jointSpace W) (ξ s) i))
            (fun i => algebraMap (Fq P0) (KummerField P0) (coordIn (jointSpace W) (ξ s) i)) := by
        rw [← hv, hC, map_sum]
        simp only [map_smul, matrixCongruence_outer, Bext, coordinate_field_image]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        rw [VField_honest]
        rw [← smul_assoc]
        ext i j
        simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
          smul_eq_mul]
        ring
  apply serialization_injective
  · rw [← ULinear_apply W, ← ULinear_apply (∑ s, r s • honestStack v (coordIn (jointSpace W) (ξ s))), map_sum]
    simp only [map_smul, ULinear_apply]
    exact hU
  · rw [← VLinear_apply W, ← VLinear_apply (∑ s, r s • honestStack v (coordIn (jointSpace W) (ξ s))), map_sum]
    simp only [map_smul, VLinear_apply]
    exact hV

end

end Praxis.Proofs.Classification
