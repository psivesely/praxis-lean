import Praxis.Proofs.Classification.LocalCubic
import Praxis.Proofs.Classification.RationalZero
import Praxis.Proofs.Classification.MooreIndep
import Praxis.Proofs.Classification.Reconstruct
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Compress
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Cubic
import Praxis.Proofs.Classification.MatrixCongruence
import Praxis.Proofs.Classification.Moore
import Praxis.Proofs.Classification.MooreSpan
import Praxis.Proofs.Classification.Pullback
import Praxis.Proofs.Classification.Serialization
import Praxis.Proofs.Classification.Tensor
import Praxis.Proofs.Classification.Transport
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

section Generic

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {d : ℕ}

theorem scalar_edge_relation (φ : F →ₐ[k] F) (M : Tri F d)
    (hM : Function.Injective (slice M)) (hfix : mapTri φ.toRingHom M = M)
    (t : F) (l₀ l : Fin d → F)
    (he : slice (t • M) l = slice (mapTri φ.toRingHom (t • M)) l₀) :
    t • l = φ t • l₀ := by
  apply hM
  rw [slice_argument_smul, slice_argument_smul]
  rw [mapTri_smul, hfix, slice_smul, slice_smul] at he
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using he

theorem eliminate_scalar_edges (t a b : F) (ht : t ≠ 0) (l₀ l₁ l₂ : Fin d → F)
    (h₁ : t • l₁ = a • l₀) (h₂ : t • l₂ = b • l₀) :
    b • l₁ - a • l₂ = 0 := by
  have hz : t • (b • l₁ - a • l₂) = 0 := by
    rw [smul_sub, smul_comm t b, smul_comm t a, h₁, h₂,
      smul_smul, smul_smul, mul_comm b a, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left ht

end Generic

theorem cubic_triangle_zero (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin v) = ⊥)
    (hd : Module.finrank (Fq P0) (jointSpace W) = 3)
    (M : Tri (KummerField P0) (Module.finrank (Fq P0) (jointSpace W)))
    (hM : Function.Injective (slice M))
    (hfix : ∀ φ : KummerField P0 →ₐ[Fq P0] KummerField P0, mapTri φ.toRingHom M = M)
    (t : KummerField P0)
    (he₁ : slice (t • M) (zeta v W (P0.m - 1)) =
      slice (mapTri (kConj (P0.m - 1)).toRingHom (t • M)) (zeta v W 0))
    (he₂ : slice (t • M) (zeta v W P0.m) =
      slice (mapTri (kConj P0.m).toRingHom (t • M)) (zeta v W 0)) : t = 0 := by
  by_contra ht
  have h₁ := scalar_edge_relation (kConj (P0.m - 1)) M hM (hfix _) t _ _ he₁
  have h₂ := scalar_edge_relation (kConj P0.m) M hM (hfix _) t _ _ he₂
  have hrel := eliminate_scalar_edges t _ _ ht _ _ _ h₁ h₂
  let i : Fin (Module.finrank (Fq P0) (jointSpace W)) := ⟨0, by omega⟩
  let j : Fin (Module.finrank (Fq P0) (jointSpace W)) := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp only [i, j] at this; omega
  have hli := moore_consecutive_independent (basisForms v (jointSpace W))
    (basisForms_independent v (jointSpace W) hinj) (P0.m - 1)
  unfold zeta at hrel
  have hrel' : (kConj P0.m t) •
      (fun r => toK (sigma P0 (P0.m - 1 + i.val) (basisForms v (jointSpace W) r))) -
      (kConj (P0.m - 1) t) •
      (fun r => toK (sigma P0 (P0.m - 1 + j.val) (basisForms v (jointSpace W) r))) = 0 := by
    simpa only [i, j, Nat.add_zero, show P0.m - 1 + 1 = P0.m by decide, zeta] using hrel
  have hb := independent_two_relation _ hli i j hij _ _ hrel'
  exact ((map_ne_zero (kConj P0.m)).mpr ht) hb

theorem stack_zero_of_cubic_zero (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (hsym : ∀ c, (W c).IsSymm)
    (Ξ : Tri (KummerField P0) (Module.finrank (Fq P0) (jointSpace W)))
    (hu : slice Ξ (zeta v W (P0.m - 1)) = CU W)
    (hv : slice Ξ (zeta v W P0.m) = CV W) (hΞ : Ξ = 0) : W = 0 := by
  apply serialization_injective
  · calc
      UField W = matrixCongruence (Bext W) (CU W) := UField_factor W hsym
      _ = 0 := by rw [← hu, hΞ, slice_zero, map_zero]
      _ = UField 0 := by rw [← ULinear_apply, map_zero]
  · calc
      VField W = matrixCongruence (Bext W) (CV W) := VField_factor W hsym
      _ = 0 := by rw [← hv, hΞ, slice_zero, map_zero]
      _ = VField 0 := by rw [← VLinear_apply, map_zero]

end

end Praxis.Proofs.Classification
