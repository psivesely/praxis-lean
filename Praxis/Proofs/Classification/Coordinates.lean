import Praxis.Proofs.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Praxis.Grid
import Praxis.Kummer
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section Coordinates

variable {k : Type*} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    (V : Submodule k (I → k))

def coordIn : (Fin (Module.finrank k V) → k) →ₗ[k] (I → k) :=
  V.subtype ∘ₗ (Module.finBasis k V).equivFun.symm.toLinearMap

def basisMat : Matrix I (Fin (Module.finrank k V)) k := LinearMap.toMatrix' (coordIn V)

theorem basisMat_mulVec (a : Fin (Module.finrank k V) → k) :
    (basisMat V).mulVec a = coordIn V a := LinearMap.toMatrix'_mulVec _ _

theorem coordIn_injective : Function.Injective (coordIn V) :=
  V.subtype_injective.comp (Module.finBasis k V).equivFun.symm.injective

theorem coordIn_range : LinearMap.range (coordIn V) = V := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ((Module.finBasis k V).equivFun.symm a).property
  · intro hx
    refine ⟨(Module.finBasis k V).equivFun ⟨x, hx⟩, ?_⟩
    change ((Module.finBasis k V).equivFun.symm ((Module.finBasis k V).equivFun ⟨x, hx⟩) : I → k) = x
    simp

def coordOut : (I → k) →ₗ[k] (Fin (Module.finrank k V) → k) :=
  Classical.choose ((coordIn V).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (coordIn_injective V)))

theorem coordOut_coordIn : coordOut V ∘ₗ coordIn V = LinearMap.id :=
  Classical.choose_spec ((coordIn V).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (coordIn_injective V)))

theorem coordIn_coordOut (x : I → k) (hx : x ∈ V) : coordIn V (coordOut V x) = x := by
  obtain ⟨a, rfl⟩ := (coordIn_range V).symm ▸ hx
  have h := LinearMap.congr_fun (coordOut_coordIn V) a
  change coordOut V (coordIn V a) = a at h
  rw [h]

def leftMat : Matrix (Fin (Module.finrank k V)) I k := LinearMap.toMatrix' (coordOut V)

theorem leftMat_mulVec (x : I → k) :
    (leftMat V).mulVec x = coordOut V x := LinearMap.toMatrix'_mulVec _ _

theorem leftMat_basisMat : leftMat V * basisMat V = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, leftMat, basisMat, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  exact coordOut_coordIn V

theorem basis_projection_matrix (M : Matrix I I k)
    (hM : LinearMap.range M.mulVecLin ≤ V) :
    basisMat V * leftMat V * M = M := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  funext i
  change ((basisMat V * leftMat V * M).mulVec x) i = (M.mulVec x) i
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, leftMat_mulVec, basisMat_mulVec,
    coordIn_coordOut V (M.mulVec x) (hM ⟨x, rfl⟩)]

theorem symmetric_factorization_explicit (M : Matrix I I k) (hsym : M.IsSymm)
    (hM : LinearMap.range M.mulVecLin ≤ V) :
    M = basisMat V * (leftMat V * M * (leftMat V).transpose) * (basisMat V).transpose := by
  have hproj := basis_projection_matrix V M hM
  have hright : M * (leftMat V).transpose * (basisMat V).transpose = M := by
    have h := congrArg Matrix.transpose hproj
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym.eq,
      Matrix.mul_assoc] using h
  calc
    M = basisMat V * leftMat V * M := hproj.symm
    _ = basisMat V * leftMat V * (M * (leftMat V).transpose * (basisMat V).transpose) := by rw [hright]
    _ = _ := by simp only [Matrix.mul_assoc]

end Coordinates

theorem cell_range_le {P : Params} (W : Stack P) (c : Cell P) :
    LinearMap.range (W c).mulVecLin ≤ jointSpace W := by
  unfold jointSpace
  exact le_iSup (fun c => LinearMap.range (W c).mulVecLin) c

theorem zLin_eq_zOf {P : Params} (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (x : Algebra.Vec (Fq P) P.N) : zLin v x = zOf v x := rfl

end

end Praxis.Proofs.Classification
