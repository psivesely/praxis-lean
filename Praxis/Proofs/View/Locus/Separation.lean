import Praxis.Proofs.View.Locus.Rows
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardAlgebra
import Praxis.Proofs.View.ForwardCells
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardLinear
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View.Locus

open Praxis.Algebra (Vec Mat)

variable {P : Params} [Fact (Nat.Prime P.q)]

def mixingCoeff (E : ExprT P) (c : Coins P) (i j : Fin (P.N+1)) : Fq P :=
  ∑ k, piAt c k.val * rowCoeff E c (some (.L2 k i)) j

def constantCoeff (E : ExprT P) (c : Coins P) (j : Fin (P.N+1)) : Fq P :=
  rowCoeff E c none j +
    (∑ s, (coin c .zeta * coin c .tau ^ s.val) * rowCoeff E c (some (.QP s)) j) +
    (∑ s, (coin c .zeta' * coin c .tau ^ s.1.val) * rowCoeff E c (some (.RP s)) j)

lemma mixing_difference (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (hΩ : coin c .Om22 ≠ 0) :
    valT pp v ⟨setCoin c .Om12 (coin c .Om22),r⟩ (rowExpr .mixing E) +
      valT pp v ⟨setCoin c .Om12 (-coin c .Om22),r⟩ (rowExpr .mixing E) -
      2 * valT pp v ⟨setCoin c .Om12 0,r⟩ (rowExpr .mixing E) =
      (-2 * coin c .Om22) * ∑ i, ∑ j,
        mixingCoeff E c i j * c.1 i * ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  simp only [mixing_value, piAt_setOm12, coin_setCoin, setCoin_fst,
    reduceCtorEq, ite_true, ite_false, rowValue_plus _ _ _ _ _ hΩ,
    rowValue_minus _ _ _ _ _ hΩ]
  conv_lhs =>
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have he : (∑ i, ∑ j, mixingCoeff E c i j * c.1 i *
      ((pp.qap.B j).eval (coin c .tau) - c.1 j)) =
      ∑ k, ∑ i, (piAt c k.val * c.1 i) *
        ∑ j, rowCoeff E c (some (.L2 k i)) j * ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
    simp only [mixingCoeff, Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ k, ∑ j, piAt c k.val * rowCoeff E c (some (.L2 k i)) j * c.1 i *
          ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [he]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma linear_difference (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (hΩ : coin c .Om22 ≠ 0) :
    valT pp v ⟨setCoin c .Om12 (coin c .Om22),r⟩ (rowExpr .linear E) -
      valT pp v ⟨setCoin c .Om12 0,r⟩ (rowExpr .linear E) =
      -coin c .zeta4 * ∑ i, ∑ j,
        rowCoeff E c (some (.GY i)) j * c.1 i * ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  simp only [linear_value, coin_setCoin, setCoin_fst, reduceCtorEq, ite_false,
    rowValue_plus _ _ _ _ _ hΩ, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_sub, sub_sub_cancel_left]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma constantCoeff_sum (E : ExprT P) (c : Coins P) (f : Fin (P.N+1) → Fq P) :
    (∑ j, constantCoeff E c j * f j) = (∑ j, rowCoeff E c none j * f j) +
      (∑ s, (coin c .zeta * coin c .tau ^ s.val) * ∑ j, rowCoeff E c (some (.QP s)) j * f j) +
      (∑ s, (coin c .zeta' * coin c .tau ^ s.1.val) * ∑ j, rowCoeff E c (some (.RP s)) j * f j) := by
  simp only [constantCoeff, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun (j : Fin (P.N+1)) (s : Fin P.E1) =>
    (coin c .zeta * coin c .tau ^ s.val) * rowCoeff E c (some (.QP s)) j * f j)]
  rw [Finset.sum_comm (f := fun (j : Fin (P.N+1)) (s : RemExp P) =>
    (coin c .zeta' * coin c .tau ^ s.1.val) * rowCoeff E c (some (.RP s)) j * f j)]
  simp only [mul_assoc]

lemma constant_difference (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (hΩ : coin c .Om22 ≠ 0) :
    valT pp v ⟨setCoin c .Om12 (coin c .Om22),r⟩ (rowExpr .constant E) -
      valT pp v ⟨setCoin c .Om12 0,r⟩ (rowExpr .constant E) =
      -∑ j, constantCoeff E c j * ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  rw [constantCoeff_sum]
  simp only [constant_value, coin_setCoin, reduceCtorEq, ite_false,
    rowValue_plus _ _ _ _ _ hΩ, mul_sub, Finset.sum_sub_distrib]
  ring

def atYTau (c : Coins P) (y : Vec (Fq P) P.N) (τ : Fq P) : Coins P :=
  (y, (setCoin c .tau τ).2)

@[simp] lemma atYTau_fst (c : Coins P) (y : Vec (Fq P) P.N) (τ : Fq P) :
    (atYTau c y τ).1 = y := rfl

@[simp] lemma coin_atYTau (c : Coins P) (y : Vec (Fq P) P.N) (τ : Fq P) (s : ScalarCoin) :
    coin (atYTau c y τ) s = if s = .tau then τ else coin c s := by
  change coin (setCoin c .tau τ) s = _
  simp

lemma atYTau_valid (Dm : QAPData P) (c : Coins P) (hc : ValidCoins Dm c)
    (y : Vec (Fq P) P.N) (τ : Fq P) (hτ : ∀ k, τ ≠ Dm.point k) :
    ValidCoins Dm (atYTau c y τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [atYTau, setCoin] using hτ
  · intro s hs
    have hn : s ≠ .tau := by intro h; subst s; contradiction
    simpa [atYTau, setCoin, Function.update_of_ne hn] using hc.2.1 s hs
  · simpa [atYTau, setCoin] using hc.2.2.1
  · simpa [atYTau, setCoin] using hc.2.2.2

@[simp] lemma sectorScale_atYTau (c : Coins P) (y : Vec (Fq P) P.N) (τ : Fq P) (σ : Sector) :
    sectorScale (atYTau c y τ) σ = sectorScale c σ := by cases σ <;> simp [sectorScale]

@[simp] lemma legScale_atYTau (c : Coins P) (y : Vec (Fq P) P.N) (τ : Fq P) (l : Leg P) :
    legScale (atYTau c y τ) l = legScale c l := by
  cases l.1 <;> simp [legScale, legScaleAt, bOf]

@[simp] lemma piAt_atYTau (c : Coins P) (y : Vec (Fq P) P.N) (τ : Fq P) (k : ℕ) :
    piAt (atYTau c y τ) k = piAt c k := by simp [piAt]

@[simp] lemma rowCoeff_atYTau (E : ExprT P) (c : Coins P) (y : Vec (Fq P) P.N)
    (τ : Fq P) (a : Option (G1Idx P)) (j : Fin (P.N+1)) :
    rowCoeff E (atYTau c y τ) a j = rowCoeff E c a j := by simp [rowCoeff]

@[simp] lemma mixingCoeff_atYTau (E : ExprT P) (c : Coins P) (y : Vec (Fq P) P.N)
    (τ : Fq P) : mixingCoeff E (atYTau c y τ) = mixingCoeff E c := by
  funext i j
  simp [mixingCoeff]

lemma constantCoeff_atY (E : ExprT P) (c : Coins P) (y : Vec (Fq P) P.N) :
    constantCoeff E (atYTau c y (coin c .tau)) = constantCoeff E c := by
  funext j
  simp [constantCoeff]

lemma mixingCoeff_zero (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec (Fq P0) P0.N) (r : Vec (Fq P0) P0.N) (E : ExprT P0)
    (h : IdentityAtR pp v r (rowExpr .mixing E) 0) (c : Coins P0) (hc : ValidCoins pp.qap c) :
    mixingCoeff E c = 0 := by
  apply matrix_zero_of_quad pp.qap S hD qapIndex_card (by decide) (by decide)
  intro y τ hτ
  let d := atYTau c y τ
  have hd := atYTau_valid pp.qap c hc y τ hτ
  have hh := mixing_difference pp v r E d (hd.2.1 .Om22 rfl)
  rw [h _ (setOm12_valid pp.qap d hd _), h _ (setOm12_valid pp.qap d hd _),
    h _ (setOm12_valid pp.qap d hd _)] at hh
  simp only [zero_mul, zero_add, mul_zero, sub_self] at hh
  have hz : (-2 * coin d .Om22 : Fq P0) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (by decide)) (hd.2.1 .Om22 rfl)
  have hq := (mul_eq_zero.mp hh.symm).resolve_left hz
  simpa [d] using hq

lemma linearCoeff_zero (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec (Fq P0) P0.N) (r : Vec (Fq P0) P0.N) (E : ExprT P0)
    (h : IdentityAtR pp v r (rowExpr .linear E) 0) (c : Coins P0) (hc : ValidCoins pp.qap c) :
    (fun i j => rowCoeff E c (some (.GY i)) j) = 0 := by
  apply matrix_zero_of_quad pp.qap S hD qapIndex_card (by decide) (by decide)
  intro y τ hτ
  let d := atYTau c y τ
  have hd := atYTau_valid pp.qap c hc y τ hτ
  have hh := linear_difference pp v r E d (hd.2.1 .Om22 rfl)
  rw [h _ (setOm12_valid pp.qap d hd _), h _ (setOm12_valid pp.qap d hd _)] at hh
  simp only [zero_mul, sub_self] at hh
  have hq := (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr (hd.2.1 .zeta4 rfl))
  simpa [d] using hq

lemma constantCoeff_zero (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P)
    (h : IdentityAtR pp v r (rowExpr .constant E) 0) (c : Coins P) (hc : ValidCoins pp.qap c) :
    constantCoeff E c = 0 := by
  classical
  have he (y : Vec (Fq P) P.N) :
      ∑ j, constantCoeff E c j * ((pp.qap.B j).eval (coin c .tau) - y j) = 0 := by
    let d := atYTau c y (coin c .tau)
    have hd := atYTau_valid pp.qap c hc y (coin c .tau) hc.1
    have hh := constant_difference pp v r E d (hd.2.1 .Om22 rfl)
    rw [h _ (setOm12_valid pp.qap d hd _), h _ (setOm12_valid pp.qap d hd _)] at hh
    simp only [zero_mul, sub_self, zero_eq_neg] at hh
    simpa only [d, constantCoeff_atY, coin_atYTau, ite_true, atYTau_fst] using hh
  have h0 := he 0
  simp only [Pi.zero_apply, sub_zero] at h0
  funext j
  have hj := he (Pi.single j 1)
  simp only [mul_sub, Finset.sum_sub_distrib, h0, zero_sub, neg_eq_zero] at hj
  simpa [Pi.single_apply] using hj

end Praxis.Proofs.View.Locus
