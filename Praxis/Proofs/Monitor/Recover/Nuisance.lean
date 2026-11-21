import Praxis.Proofs.Monitor.Recover.Quadratic
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Recover.Boundary
import Praxis.Proofs.Monitor.Recover.Collect
import Praxis.Proofs.View.ForwardCells
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardIndependence
import Praxis.Proofs.View.ForwardLinear
import Praxis.Proofs.View.SZ.Model
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open Praxis.Proofs.View Praxis.Proofs.View.SZ

noncomputable section

attribute [local irreducible] keys1 keys2

lemma slope_pi_zero (c : Coins P0) (a : Option (G1Idx P0)) :
    leftSlope (setCoin c .pi 0) a = 0 := by
  cases a with
  | none => rfl
  | some a => cases a <;> simp [leftSlope, piAt]

lemma nuisance_pi (D : ExprT P0) (c : Coins P0) (x : F) (σ : Sector) (l : Leg P0) (j : I) :
    nuisance D (setCoin c .pi x) σ l j = nuisance D c σ l j := by
  simp [nuisance]

lemma legScale_pi (c : Coins P0) (x : F) (l : Leg P0) :
    legScale (setCoin c .pi x) l = legScale c l := by
  cases l.1 <;> simp [legScale, legScaleAt, bOf]

lemma legScale_alpha (c : Coins P0) (x : F) (l : Leg P0) :
    legScale (setCoin c .alpha x) l = legScale c l := by
  cases l.1 <;> simp [legScale, legScaleAt, bOf]

lemma base_pi_zero (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0)
    (σ : Sector) (l : Leg P0) (j : I) :
    ((keys1 P0).map fun a => leftBase pp (setCoin c .pi 0) a *
      (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l)))).sum =
        nuisance D c σ l j := by
  rw [base_collect]
  simp only [piAt, coin_setCoin, reduceCtorEq, ite_true, ite_false,
    zero_mul, Finset.sum_const_zero, zero_add, nuisance_pi]

def nuisanceValue (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0) (σ : Sector) : F :=
  ∑ l : Leg P0, legScale c l * ∑ j : I,
    nuisance D c σ l j * ((pp.qap.B j).eval (coin c .tau) - c.1 j)

lemma nuisanceValue_alpha (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0) (x : F) (σ : Sector) :
    nuisanceValue pp D (setCoin c .alpha x) σ = nuisanceValue pp D c σ := by
  simp [nuisanceValue, nuisance, legScale_alpha]

lemma rcv_sum_sub_zero {R α : Type*} [CommRing R] (l : List α) (f g : α → R)
    (hf : ∀ a, f a = 0) (h : (l.map fun a => f a - g a).sum = 0) :
    (l.map g).sum = 0 := by
  simpa only [hf, zero_sub, list_sum_neg, neg_eq_zero] using h

lemma nuisanceValue_zero (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (c : Coins P0)
    (hc : boundaryFactor c ≠ 0) (σ : Sector) : nuisanceValue pp D c σ = 0 := by
  apply sector_separate (nuisanceValue pp D) (nuisanceValue_alpha pp D) _ c hc σ
  intro c hc
  have hh := rcv_sum_sub_zero (keys1 P0)
    (fun a => leftSlope (setCoin c .pi 0) a * rightTwo pp (setCoin c .pi 0) D a)
    (fun a => leftBase pp (setCoin c .pi 0) a * rightOne pp (setCoin c .pi 0) D a)
    (fun a => by rw [slope_pi_zero, zero_mul])
    (boundary_linear pp v r D ι h (setCoin c .pi 0))
  rw [contraction_collect] at hh
  simp only [base_pi_zero, boundaryFactor, coin_setCoin, reduceCtorEq, ite_false,
    sectorScale, legScale_pi, nuisance_pi, setCoin_fst] at hh
  exact (mul_eq_zero.mp hh).resolve_left hc

lemma leg_separate (Dm : QAPData P0) (y : Vec F P0.N) (τ : F) (a : Leg P0 → F)
    (h : ∀ c, ValidCoins Dm c → c.1 = y → coin c .tau = τ →
      ∑ l : Leg P0, legScale c l * a l = 0)
    (hτ : ∀ k, τ ≠ Dm.point k) : a = 0 := by
  have hh : (fun cl : Cell P0 => if cl.1 = 0 then a cl.2 else 0) = 0 := by
    apply cell_sep Dm y τ _ _ hτ
    intro c hc hy ht
    rw [Fintype.sum_prod_type]
    simp only [gamma, mul_ite, mul_zero]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc]
    have he := h c hc hy ht
    rw [← Finset.mul_sum, he, mul_zero]
  ext l
  have he := congrFun hh (0,l)
  simpa only [ite_true, Pi.zero_apply] using he

def tagCoins (c : Coins P0) (z z' z4 : F) : Coins P0 :=
  setCoin (setCoin (setCoin c .zeta z) .zeta' z') .zeta4 z4

lemma tagCoins_leg (c : Coins P0) (z z' z4 : F) (l : Leg P0) :
    legScale (tagCoins c z z' z4) l = legScale c l := by
  cases l.1 <;> simp [tagCoins, legScale, legScaleAt, bOf]

def nuisanceAt (D : ExprT P0) (σ : Sector) (l : Leg P0) (j : I)
    (y : Vec F P0.N) (τ z z' z4 : F) : F :=
  bc D σ l j none +
    z * ∑ s : Fin P0.E1, bc D σ l j (some (.QP s)) * τ ^ s.val +
    z' * ∑ s : RemExp P0, bc D σ l j (some (.RP s)) * τ ^ s.1.val +
    z4 * ∑ i : I, bc D σ l j (some (.GY i)) * y i

lemma nuisance_tags (D : ExprT P0) (c : Coins P0) (z z' z4 : F)
    (σ : Sector) (l : Leg P0) (j : I) :
    nuisance D (tagCoins c z z' z4) σ l j = nuisanceAt D σ l j c.1 (coin c .tau) z z' z4 := by
  simp [nuisance, nuisanceAt, tagCoins]

lemma nuisance_leg_identity (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (σ : Sector) (l : Leg P0)
    (y : Vec F P0.N) (τ z z' z4 : F) (hτ : ∀ k, τ ≠ pp.qap.point k)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hz4 : z4 ≠ 0) :
    ∑ j : I, nuisanceAt D σ l j y τ z z' z4 * ((pp.qap.B j).eval τ - y j) = 0 := by
  have hh : (fun l : Leg P0 => ∑ j : I,
      nuisanceAt D σ l j y τ z z' z4 * ((pp.qap.B j).eval τ - y j)) = 0 := by
    apply leg_separate pp.qap y τ _ _ hτ
    intro c hc hy ht
    have hn : boundaryFactor (tagCoins c z z' z4) ≠ 0 := by
      have heps : coin c .eps ≠ 0 := hc.2.2.1
      simpa only [boundaryFactor, tagCoins, coin_setCoin, reduceCtorEq, ite_false,
        ite_true] using mul_ne_zero (mul_ne_zero (mul_ne_zero hz hz') hz4) heps
    have he := nuisanceValue_zero pp v r D ι h (tagCoins c z z' z4) hn σ
    simp only [nuisanceValue, tagCoins_leg, nuisance_tags] at he
    simpa only [tagCoins, setCoin_fst,
      coin_setCoin, reduceCtorEq, ite_false, hy, ht] using he
  exact congrFun hh l

def gc (D : ExprT P0) (σ : Sector) (l : Leg P0) (i j : I) : F :=
  bc D σ l j (some (.GY i))

def nuisanceConst (D : ExprT P0) (σ : Sector) (l : Leg P0) (j : I)
    (τ z z' : F) : F :=
  bc D σ l j none +
    z * ∑ s : Fin P0.E1, bc D σ l j (some (.QP s)) * τ ^ s.val +
    z' * ∑ s : RemExp P0, bc D σ l j (some (.RP s)) * τ ^ s.1.val

lemma nuisance_split (pp : PublicParams P0) (D : ExprT P0) (σ : Sector) (l : Leg P0)
    (y : Vec F P0.N) (τ z z' z4 : F) :
    (∑ j : I, nuisanceAt D σ l j y τ z z' z4 * ((pp.qap.B j).eval τ - y j)) =
      (∑ j : I, nuisanceConst D σ l j τ z z' * ((pp.qap.B j).eval τ - y j)) +
        z4 * ∑ i : I, ∑ j : I, gc D σ l i j * y i * ((pp.qap.B j).eval τ - y j) := by
  change (∑ j : I, (nuisanceConst D σ l j τ z z' + z4 * ∑ i : I, gc D σ l i j * y i) *
    ((pp.qap.B j).eval τ - y j)) = _
  rw [show (∑ j : I, (nuisanceConst D σ l j τ z z' + z4 * ∑ i : I, gc D σ l i j * y i) *
      ((pp.qap.B j).eval τ - y j)) =
      (∑ j : I, nuisanceConst D σ l j τ z z' * ((pp.qap.B j).eval τ - y j)) +
      (∑ j : I, (z4 * ∑ i : I, gc D σ l i j * y i) * ((pp.qap.B j).eval τ - y j)) by
        simp only [add_mul, Finset.sum_add_distrib]]
  apply congrArg (fun x => (∑ j : I, nuisanceConst D σ l j τ z z' *
    ((pp.qap.B j).eval τ - y j)) + x)
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma gc_zero (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec F P0.N) (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (σ : Sector) (l : Leg P0) : gc D σ l = 0 := by
  apply matrix_zero_of_quad pp.qap S hD View.qapIndex_card (by decide) (by decide)
  intro y τ hτ
  have h1 := nuisance_leg_identity pp v r D ι h σ l y τ 1 1 1 hτ
    one_ne_zero one_ne_zero one_ne_zero
  have h2 := nuisance_leg_identity pp v r D ι h σ l y τ 1 1 2 hτ
    one_ne_zero one_ne_zero (by decide)
  rw [nuisance_split] at h1 h2
  linear_combination h2 - h1

lemma rcv_affine_sum_coeff {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (a b : α → R) (h : ∀ y : α → R, ∑ k, a k * (b k - y k) = 0) (j : α) :
    a j = 0 := by
  have h0 := h 0
  have hj := h (Pi.single j 1)
  simp only [Pi.zero_apply, sub_zero] at h0
  simp only [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hj
  linear_combination h0 - hj

lemma nuisanceConst_zero (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec F P0.N) (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (σ : Sector) (l : Leg P0)
    (τ z z' : F) (hτ : ∀ k, τ ≠ pp.qap.point k) (hz : z ≠ 0) (hz' : z' ≠ 0) (j : I) :
    nuisanceConst D σ l j τ z z' = 0 := by
  have hG := gc_zero pp S hD v r D ι h σ l
  have hh (y : Vec F P0.N) :
      ∑ k : I, nuisanceConst D σ l k τ z z' * ((pp.qap.B k).eval τ - y k) = 0 := by
    have he := nuisance_leg_identity pp v r D ι h σ l y τ z z' 1 hτ hz hz' one_ne_zero
    rw [nuisance_split] at he
    simpa only [hG, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] using he
  exact rcv_affine_sum_coeff (fun k => nuisanceConst D σ l k τ z z')
    (fun k => (pp.qap.B k).eval τ) hh j

lemma nuisance_zero (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec F P0.N) (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (c : Coins P0) (hc : ValidCoins pp.qap c)
    (σ : Sector) (l : Leg P0) (j : I) : nuisance D c σ l j = 0 := by
  have hG := gc_zero pp S hD v r D ι h σ l
  have hC := nuisanceConst_zero pp S hD v r D ι h σ l (coin c .tau)
    (coin c .zeta) (coin c .zeta') hc.1 (hc.2.1 .zeta rfl) (hc.2.1 .zeta' rfl) j
  change nuisanceConst D σ l j (coin c .tau) (coin c .zeta) (coin c .zeta') +
    coin c .zeta4 * ∑ i : I, gc D σ l i j * c.1 i = 0
  simp only [hC, hG, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]

end

end Praxis.Proofs.Monitor
