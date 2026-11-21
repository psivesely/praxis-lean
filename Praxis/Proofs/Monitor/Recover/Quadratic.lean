import Praxis.Proofs.Monitor.Recover.Collect
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Recover.Boundary
import Praxis.Proofs.View.ForwardCells
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardHelpers
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

def quadValue (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0) (σ : Sector) : F :=
  ∑ cl : Cell P0, gamma c cl * ∑ i : I, ∑ j : I,
    vc D σ cl i j * c.1 i * ((pp.qap.B j).eval (coin c .tau) - c.1 j)

lemma slope_legs (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0) (σ : Sector) :
    (∑ l : Leg P0, legScale c l * ∑ j : I,
      (∑ k : Fin P0.K1, piAt c k.val * ∑ i : I, vc D σ (k,l) i j * c.1 i) *
        ((pp.qap.B j).eval (coin c .tau) - c.1 j)) = quadValue pp D c σ := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [quadValue, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [gamma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma slope_global (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0) :
    ((keys1 P0).map fun a => leftSlope c a * rightOne pp c D a).sum =
      boundaryFactor c * ∑ σ : Sector, sectorScale c σ * quadValue pp D c σ := by
  rw [contraction_collect]
  simp only [slope_collect, slope_legs]

lemma boundaryFactor_alpha (c : Coins P0) (x : F) :
    boundaryFactor (setCoin c .alpha x) = boundaryFactor c := by
  simp [boundaryFactor]

lemma gamma_alpha (c : Coins P0) (x : F) (cl : Cell P0) :
    gamma (setCoin c .alpha x) cl = gamma c cl := by
  cases cl.2.1 <;> simp [gamma, piAt, legScale, legScaleAt, bOf]

lemma quadValue_alpha (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0) (x : F) (σ : Sector) :
    quadValue pp D (setCoin c .alpha x) σ = quadValue pp D c σ := by
  simp only [quadValue, gamma_alpha, setCoin_fst, coin_setCoin, reduceCtorEq, ite_false]

lemma sector_separate (g : Coins P0 → Sector → F)
    (hg : ∀ c x σ, g (setCoin c .alpha x) σ = g c σ)
    (h : ∀ c, boundaryFactor c ≠ 0 → ∑ σ : Sector, sectorScale c σ * g c σ = 0)
    (c : Coins P0) (hc : boundaryFactor c ≠ 0) : ∀ σ, g c σ = 0 := by
  have h0 := h (setCoin c .alpha 0) (by rwa [boundaryFactor_alpha])
  have h1 := h (setCoin c .alpha 1) (by rwa [boundaryFactor_alpha])
  simp only [sum_sector, sectorScale, hg, coin_setCoin, ite_true, one_mul,
    zero_mul, add_zero] at h0 h1
  intro σ
  cases σ
  · exact h0
  · linear_combination h1 - h0

lemma quadValue_zero (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (c : Coins P0)
    (hc : boundaryFactor c ≠ 0) (σ : Sector) : quadValue pp D c σ = 0 := by
  apply sector_separate (quadValue pp D) (quadValue_alpha pp D) _ c hc σ
  intro c hc
  have hh := boundary_quadratic pp v r D ι h c
  rw [slope_global] at hh
  exact (mul_eq_zero.mp hh).resolve_left hc

lemma boundaryFactor_ne_zero (pp : PublicParams P0) (c : Coins P0)
    (hc : ValidCoins pp.qap c) : boundaryFactor c ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hc.2.1 .zeta rfl)
    (hc.2.1 .zeta' rfl)) (hc.2.1 .zeta4 rfl)) hc.2.2.1

lemma vc_zero (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec F P0.N) (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (σ : Sector) (cl : Cell P0) : vc D σ cl = 0 := by
  apply matrix_zero_of_quad pp.qap S hD View.qapIndex_card (by decide) (by decide)
  intro y τ hτ
  have hh : (fun cl : Cell P0 => ∑ i : I, ∑ j : I,
      vc D σ cl i j * y i * ((pp.qap.B j).eval τ - y j)) = 0 := by
    apply cell_sep pp.qap y τ _ _ hτ
    intro c hc hy ht
    have he := quadValue_zero pp v r D ι h c (boundaryFactor_ne_zero pp c hc) σ
    simpa only [quadValue, hy, ht] using he
  exact congrFun hh cl

end

end Praxis.Proofs.Monitor
