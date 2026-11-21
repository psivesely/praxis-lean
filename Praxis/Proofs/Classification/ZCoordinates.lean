import Praxis.Proofs.Classification.WeightEquations
import Praxis.Proofs.Classification.MooreSpan
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Coeff
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Coordinates
import Praxis.Proofs.Classification.Moore
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

open Praxis.Algebra (Vec)

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

def ZLinear (v : Fin P0.n → Vec (Fq P0) P0.N) :
    Vec (Fq P0) P0.N →ₗ[Fq P0] KummerField P0 :=
  coeffEquiv.toLinearMap ∘ₗ zLin v

theorem ZLinear_apply (v : Fin P0.n → Vec (Fq P0) P0.N) (x : Vec (Fq P0) P0.N) :
    ZLinear v x = Z v x := by
  simp only [ZLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, coeffEquiv_apply,
    zLin_eq_zOf, Z]

theorem Z_coordinate_sum (v : Fin P0.n → Vec (Fq P0) P0.N)
    (V : Submodule (Fq P0) (Vec (Fq P0) P0.N))
    (ξ : Fin (Module.finrank (Fq P0) V) → Fq P0) :
    Z v (coordIn V ξ) = ∑ r, algebraMap (Fq P0) (KummerField P0) (ξ r) *
      toK (basisForms v V r) := by
  rw [← ZLinear_apply]
  change (ZLinear v ∘ₗ V.subtype) ((Module.finBasis (Fq P0) V).equivFun.symm ξ) = _
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul, Algebra.smul_def]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, ZLinear, LinearEquiv.coe_coe,
    coeffEquiv_apply, basisForms, restrictedForms]

theorem Z_conj_coordinate_sum (v : Fin P0.n → Vec (Fq P0) P0.N)
    (V : Submodule (Fq P0) (Vec (Fq P0) P0.N))
    (ξ : Fin (Module.finrank (Fq P0) V) → Fq P0) (s : ℕ) :
    kConj s (Z v (coordIn V ξ)) = ∑ r, algebraMap (Fq P0) (KummerField P0) (ξ r) *
      toK (sigma P0 s (basisForms v V r)) := by
  rw [Z_coordinate_sum, map_sum]
  simp only [map_mul, AlgHom.commutes, kConj_toK]

theorem Z_eq_zero_of_injective (v : Fin P0.n → Vec (Fq P0) P0.N)
    (V : Submodule (Fq P0) (Vec (Fq P0) P0.N))
    (hinj : V ⊓ LinearMap.ker (zLin v) = ⊥)
    (x : Vec (Fq P0) P0.N) (hx : x ∈ V) (hz : Z v x = 0) : x = 0 := by
  have hz' : zLin v x = 0 := by
    apply toK_injective
    simpa only [zLin_eq_zOf, toK_zero, Z] using hz
  have h : x ∈ V ⊓ LinearMap.ker (zLin v) := ⟨hx, hz'⟩
  rw [hinj] at h
  exact (Submodule.mem_bot _).mp h

end

end Praxis.Proofs.Classification
