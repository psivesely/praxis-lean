import Praxis.Proofs.View.ForwardEvaluation
import Praxis.Proofs.View.ForwardIndependence
import Praxis.Proofs.View.ForwardLinear
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardCells
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardMain
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open Polynomial

set_option maxRecDepth 2048

section Omega

variable {P : Params} [Fact (Nat.Prime P.q)]

@[simp] lemma piAt_setOm12 (c : Coins P) (x : Fq P) (k : ℕ) :
    piAt (setCoin c .Om12 x) k = piAt c k := by simp [piAt]

@[simp] lemma legScale_setOm12 (c : Coins P) (x : Fq P) (l : Leg P) :
    legScale (setCoin c .Om12 x) l = legScale c l := by
  cases l.1 <;> simp [legScale, legScaleAt, bOf]

@[simp] lemma gamma_setOm12 (c : Coins P) (x : Fq P) (cl : Cell P) :
    gamma (setCoin c .Om12 x) cl = gamma c cl := by simp [gamma]

@[simp] lemma legMask_setOm12 (c : Coins P) (x : Fq P)
    (v : Fin P.n → Vec (Fq P) P.N) (l : Leg P) :
    legMask v (setCoin c .Om12 x) l = legMask v c l := by simp [legMask]

@[simp] lemma H2_setOm12 (c : Coins P) (x : Fq P) (pp : PublicParams P)
    (l : Leg P) (j : Fin (P.N+1)) : H2 pp (setCoin c .Om12 x) l j = H2 pp c l j := by simp [H2]

@[simp] lemma kappa_setOm12 (c : Coins P) (x : Fq P) (pp : PublicParams P) :
    kappa pp (setCoin c .Om12 x) = kappa pp c := by
  simp [kappa, gammaKey, legScaleAt, bOf]

@[simp] lemma crossVal_setOm12 (c : Coins P) (x : Fq P) (g : CrossIdx) :
    crossVal (setCoin c .Om12 x) g = crossVal c g := by cases g <;> simp [crossVal]

@[simp] lemma cTie_setOm12 (c : Coins P) (x : Fq P) (s : TieIdx) :
    cTie (setCoin c .Om12 x) s = cTie c s := by cases s <;> simp [cTie]

@[simp] lemma kummerAtU_setOm12 (c : Coins P) (x : Fq P) :
    kummerAtU (setCoin c .Om12 x) = kummerAtU c := by simp [kummerAtU]

lemma r1ExpAt_Om12_diff (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (c : Coins P) (hΩ : coin c .Om22 ≠ 0) (l : Leg P) (j : Fin (P.N+1)) :
    r1ExpAt pp v ⟨setCoin c .Om12 (coin c .Om22), r⟩ l j -
      r1ExpAt pp v ⟨setCoin c .Om12 0, r⟩ l j = -H2 pp c l j := by
  simp [r1ExpAt, hΩ]

set_option maxHeartbeats 1000000 in
lemma mainValue_diff_Om12 (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hΩ : coin c .Om22 ≠ 0) :
    mainValue pp v r E σ (setCoin c .Om12 (coin c .Om22)) -
      mainValue pp v r E σ (setCoin c .Om12 0) =
    ∑ cl, gamma c cl * ∑ i, ∑ j, (dC E σ cl i j - aC E σ cl i j) * c.1 i *
      ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  have hw : (∑ cl, ∑ i, ∑ j, aC E σ cl i j * piAt c cl.1.val * c.1 i *
      r1ExpAt pp v ⟨setCoin c .Om12 (coin c .Om22),r⟩ cl.2 j) -
      (∑ cl, ∑ i, ∑ j, aC E σ cl i j * piAt c cl.1.val * c.1 i *
      r1ExpAt pp v ⟨setCoin c .Om12 0,r⟩ cl.2 j) =
      ∑ cl, ∑ i, ∑ j, -aC E σ cl i j * piAt c cl.1.val * c.1 i * H2 pp c cl.2 j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro cl _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_sub, r1ExpAt_Om12_diff _ _ _ _ hΩ]
    ring
  have hd : (∑ cl, ∑ i, ∑ j, dC E σ cl i j * piAt c cl.1.val *
      (coin c .Om22 * c.1 i + coin c .Om22 * (pp.qap.A i).eval (coin c .tau)) *
      (H2 pp c cl.2 j / coin c .Om22)) -
      (∑ cl, ∑ i, ∑ j, dC E σ cl i j * piAt c cl.1.val *
      (0 * c.1 i + coin c .Om22 * (pp.qap.A i).eval (coin c .tau)) *
      (H2 pp c cl.2 j / coin c .Om22)) =
      ∑ cl, ∑ i, ∑ j, dC E σ cl i j * piAt c cl.1.val * c.1 i * H2 pp c cl.2 j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro cl _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hΩ] <;> ring
  have hsum : (∑ cl, ∑ i, ∑ j, -aC E σ cl i j * piAt c cl.1.val * c.1 i * H2 pp c cl.2 j) +
      (∑ cl, ∑ i, ∑ j, dC E σ cl i j * piAt c cl.1.val * c.1 i * H2 pp c cl.2 j) =
      ∑ cl, gamma c cl * ∑ i, ∑ j, (dC E σ cl i j - aC E σ cl i j) * c.1 i *
        ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cl _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [H2, gamma]
    ring
  rw [← hsum, ← hw, ← hd]
  simp only [mainValue, piAt_setOm12, gamma_setOm12, legScale_setOm12, H2_setOm12,
    crossVal_setOm12, cTie_setOm12, kummerAtU_setOm12, setCoin_fst, coin_setCoin,
    reduceCtorEq, ite_true, ite_false]
  ring

end Omega

lemma matrix_coeffs_equal (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec (Fq P0) P0.N) (r : Vec (Fq P0) P0.N) (E : ExprT P0)
    (σ : Sector) (ι : Fq P0)
    (h : ∀ c, ValidCoins pp.qap c → mainValue pp v r E σ c = ι * kappa pp c) :
    dC E σ = aC E σ := by
  classical
  have hcell (y : Vec (Fq P0) P0.N) (τ : Fq P0) (hτ : ∀ k, τ ≠ pp.qap.point k) :
      (fun cl => ∑ i, ∑ j, (dC E σ cl i j - aC E σ cl i j) * y i *
        ((pp.qap.B j).eval τ - y j)) = 0 := by
    apply cell_sep pp.qap y τ _ _ hτ
    intro c hc hy hct
    have h1 := h (setCoin c .Om12 (coin c .Om22)) (setOm12_valid pp.qap c hc _)
    have h0 := h (setCoin c .Om12 0) (setOm12_valid pp.qap c hc _)
    rw [kappa_setOm12] at h1 h0
    have hh := mainValue_diff_Om12 pp v r E σ c (hc.2.1 .Om22 rfl)
    rw [h1, h0, sub_self] at hh
    simpa only [hy, hct] using hh.symm
  ext cl i j
  have hm := matrix_zero_of_quad pp.qap S hD qapIndex_card (by decide) (by decide)
    (dC E σ cl - aC E σ cl) (fun y τ hτ => congrFun (hcell y τ hτ) cl)
  have he := congrFun (congrFun hm i) j
  exact sub_eq_zero.mp he

end Praxis.Proofs.View
