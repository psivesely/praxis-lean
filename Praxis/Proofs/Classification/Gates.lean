import Praxis.Proofs.Classification.Bool
import Praxis.Proofs.Classification.Gates.Geometry
import Praxis.Proofs.Classification.Gates.Moment
import Praxis.Proofs.Classification.Gates.Moore
import Praxis.Forms
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Gates.Algebra
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open Praxis.Algebra (Vec)

namespace GateAlgebra

lemma zLin_eq_zOf {P : Params} (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) :
    zLin v x = zOf v x := rfl

lemma space_square_moments (v : Fin P0.n → Vec k P0.N) (W : Stack P0)
    (xs : Finset (Vec k P0.N)) (e : Vec k P0.N → k)
    (hxV : ∀ x ∈ xs, x ∈ jointSpace W)
    (hd : Module.finrank k (jointSpace W) ≤ 3)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin v) = ⊥)
    (hcell : ∀ c, ∑ x ∈ xs, e x * weight v x c = 0) :
    ∀ i j, ∑ x ∈ xs, e x * x i * x j = 0 := by
  classical
  let V := jointSpace W
  let d := Module.finrank k V
  let b : Module.Basis (Fin d) k V := Module.finBasis k V
  let f : V →ₗ[k] KPoly k P0.n := (zLin v).domRestrict V
  let a : Fin d → KPoly k P0.n := fun r => f (b r)
  have hf : Function.Injective f :=
    LinearMap.injective_domRestrict_iff.mpr (disjoint_iff.mpr hinj)
  have ha : LinearIndependent k a :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  let u : Vec k P0.N → Fin d → k := fun x r =>
    if hx : x ∈ V then b.repr ⟨x, hx⟩ r else 0
  have hrepr (x : Vec k P0.N) (hx : x ∈ xs) :
      ∑ r, u x r • (b r : Vec k P0.N) = x := by
    have hx' : x ∈ V := hxV x hx
    have hh := congrArg V.subtype (b.sum_repr ⟨x, hx'⟩)
    simpa only [map_sum, map_smul, u, dif_pos hx', Submodule.subtype_apply] using hh
  have hz (x : Vec k P0.N) (hx : x ∈ xs) :
      zOf v x = ∑ r, u x r • a r := by
    have hh := congrArg (zLin v) (hrepr x hx)
    have hax (r : Fin d) : zLin v (b r : Vec k P0.N) = a r := by
      simp only [a, f, LinearMap.domRestrict_apply]
    simp only [map_sum, map_smul, hax, zLin_eq_zOf] at hh
    exact hh.symm
  have hp := scalar_partners v xs e hcell
  have hcoord : ∀ i j, ∑ x ∈ xs, e x * u x i * u x j = 0 := by
    apply two_moore a ha hd xs u e
    intro r
    convert hp r using 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [← hz x hx]
  apply GateGeometry.transport_squares xs e u (fun r => (b r : Vec k P0.N)) hcoord
  intro x hx i
  have hh := congrFun (hrepr x hx) i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh.symm

end GateAlgebra

theorem classification_gates (A : FormMatrix P0) (S : Relation P0) (hS : InShape P0 S) (W : Stack P0)
    (xs : Finset (Vec (Fq P0) P0.N)) (ρ : Vec (Fq P0) P0.N → Fq P0)
    (hxs : ∀ x ∈ xs, x ∈ jointSpace W ∧ x 0 = 1 ∧ ∀ j : Fin P0.N, x j.succ = 0 ∨ x j.succ = 1)
    (hW : W = ∑ x ∈ xs, ρ x • honestStack (formVec A) x)
    (hgates : ∀ c t, Algebra.MomentGate (S t) (W c) = 0)
    (hdim : Module.finrank (Fq P0) (jointSpace W) ≤ dimMax)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin (formVec A)) = ⊥) :
    ∃ (xs' : Finset (Vec (Fq P0) P0.N)) (ρ' : Vec (Fq P0) P0.N → Fq P0),
      (∀ x ∈ xs', x ∈ jointSpace W ∧ IsWitness S x) ∧
      W = ∑ x ∈ xs', ρ' x • honestStack (formVec A) x := by
  classical
  have hboolean : ∀ x ∈ xs, x ∈ jointSpace W ∧ x 0 = 1 ∧
      ∀ i : Fin (P0.N+1), x i = 0 ∨ x i = 1 := by
    intro x hx
    refine ⟨(hxs x hx).1, (hxs x hx).2.1, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => (hxs x hx).2.2 j) i
    exact Or.inr (hxs x hx).2.1
  have hcoeff (t : Fin P0.gatesMax) :
      ∀ x ∈ xs, ρ x * GateMoment.defect (S t) x = 0 := by
    apply GateGeometry.boolean_squares (jointSpace W) (0 : Fin (P0.N+1)) hdim
      xs hboolean (fun x => ρ x * GateMoment.defect (S t) x)
    exact GateAlgebra.space_square_moments (formVec A) W xs
      (fun x => ρ x * GateMoment.defect (S t) x)
      (fun x hx => (hxs x hx).1) hdim hinj
      (GateMoment.cells A S W xs ρ hW hgates t)
  have hwitness : ∀ x ∈ xs, ρ x ≠ 0 → IsWitness S x := by
    intro x hx hρ
    refine ⟨(hxs x hx).2.1, (hxs x hx).2.2, ?_⟩
    intro t
    exact sub_eq_zero.mp ((mul_eq_zero.mp (hcoeff t x hx)).resolve_left hρ)
  refine ⟨xs.filter (fun x => IsWitness S x), ρ, ?_, ?_⟩
  · intro x hx
    exact ⟨(hxs x (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩
  · rw [hW]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hn
    have hρ : ρ x = 0 := by
      by_contra hρ
      exact hn (Finset.mem_filter.mpr ⟨hx, hwitness x hx hρ⟩)
    rw [hρ, zero_smul]

end Praxis.Proofs.Classification
