import Praxis.Proofs.View.ForwardAlgebra
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardEvaluation
import Praxis.Proofs.View.ForwardIndependence
import Praxis.Proofs.View.ForwardLinear
import Praxis.Proofs.View.ForwardMain
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open Polynomial

set_option maxRecDepth 2048

section Lines

variable {P : Params} [Fact (Nat.Prime P.q)]

noncomputable def braceVal (pp : PublicParams P) (r : Vec (Fq P) P.N) (E : ExprT P)
    (σ : Sector) (cl : Cell P) (y : Vec (Fq P) P.N) (τ : Fq P) : Fq P :=
  (cellForm pp.qap (aC E σ cl) (sC E σ cl) r y).eval τ +
    (pp.qap.zCell cl).eval τ * (hC E σ cl).eval τ + pp.qap.Z0.eval τ * (RC E σ cl).eval τ

noncomputable def cellTerm (pp : PublicParams P) (r : Vec (Fq P) P.N) (E : ExprT P)
    (σ : Sector) (c : Coins P) : Fq P :=
  ∑ cl, gamma c cl * braceVal pp r E σ cl c.1 (coin c .tau)

noncomputable def maskTerm (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P)
    (σ : Sector) (c : Coins P) : Fq P :=
  (∑ cl, piAt c cl.1.val * dot c.1 (Matrix.mulVec (aC E σ cl) (legMask v c cl.2))) +
  (∑ k, ∑ i, lC E σ k i * piAt c k.val * c.1 i) +
  coin c .pi * (∑ i, c.1 i * ∑ g, crossVal c g * ∑ e, gbC E σ i g e * coin c .u ^ e.val) +
  coin c .pi * kummerAtU c * (∑ i, c.1 i * ∑ s, cTie c s * ∑ e, gmC E σ i s e * coin c .u ^ e.val)

lemma r1ExpAt_Om12_zero (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (c : Coins P) (l : Leg P) (j : Fin (P.N+1)) :
    r1ExpAt pp v ⟨setCoin c .Om12 0,r⟩ l j =
      legScale c l * (r j + (pp.qap.A j).eval (coin c .tau)) + legMask v c l j := by
  simp [r1ExpAt]

lemma cell_pairing_sum (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hΩ : coin c .Om22 ≠ 0) :
    (∑ cl, ∑ i, ∑ j, aC E σ cl i j * piAt c cl.1.val * c.1 i *
      (legScale c cl.2 * (r j + (pp.qap.A j).eval (coin c .tau)) + legMask v c cl.2 j)) +
    (∑ cl, ∑ i, ∑ j, aC E σ cl i j * piAt c cl.1.val *
      (coin c .Om22 * (pp.qap.A i).eval (coin c .tau)) * (H2 pp c cl.2 j / coin c .Om22)) =
    (∑ cl, gamma c cl * ∑ i, ∑ j, aC E σ cl i j *
      (c.1 i * (r j + (pp.qap.A j).eval (coin c .tau)) +
        (pp.qap.A i).eval (coin c .tau) * ((pp.qap.B j).eval (coin c .tau) - c.1 j))) +
    ∑ cl, piAt c cl.1.val * dot c.1 (Matrix.mulVec (aC E σ cl) (legMask v c cl.2)) := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro cl _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [gamma, H2]
  field_simp [hΩ] <;> ring

lemma sc_pairing_sum (pp : PublicParams P) (E : ExprT P) (σ : Sector) (c : Coins P) :
    (∑ cl, ∑ i, sC E σ cl i * piAt c cl.1.val * c.1 i * legScale c cl.2) =
      ∑ cl, gamma c cl * ∑ i, c.1 i * sC E σ cl i := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cl _
  apply Finset.sum_congr rfl
  intro i _
  simp only [gamma]
  ring

set_option maxHeartbeats 1000000 in
lemma mainValue_lines (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hΩ : coin c .Om22 ≠ 0)
    (hd : dC E σ = aC E σ) :
    mainValue pp v r E σ (setCoin c .Om12 0) = cellTerm pp r E σ c + maskTerm v E σ c := by
  simp only [mainValue, piAt_setOm12, gamma_setOm12, legScale_setOm12, H2_setOm12,
    crossVal_setOm12, cTie_setOm12, kummerAtU_setOm12, setCoin_fst, coin_setCoin,
    reduceCtorEq, ite_true, ite_false, zero_mul, zero_add, r1ExpAt_Om12_zero, hd]
  rw [cell_pairing_sum _ _ _ _ _ _ hΩ, sc_pairing_sum pp E σ c]
  simp only [cellTerm, braceVal, maskTerm, cellForm, eval_add, eval_finsetSum, eval_mul,
    eval_sub, eval_C, mul_add, add_mul, mul_sub, sub_mul, Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, mul_comm, mul_left_comm]
  abel

def scaleB (t : Fq P) (c : Coins P) : Coins P :=
  setCoin (setCoin (setCoin c .bE (t * coin c .bE)) .bO (t * coin c .bO)) .bV (t * coin c .bV)

@[simp] lemma scaleB_fst (t : Fq P) (c : Coins P) : (scaleB t c).1 = c.1 := rfl

@[simp] lemma coin_scaleB (t : Fq P) (c : Coins P) (s : ScalarCoin) :
    coin (scaleB t c) s = if s = .bE ∨ s = .bO ∨ s = .bV then t * coin c s else coin c s := by
  cases s <;> simp [scaleB]

lemma scaleB_valid (t : Fq P) (c : Coins P) (Dm : QAPData P) (ht : t ≠ 0)
    (hc : ValidCoins Dm c) : ValidCoins Dm (scaleB t c) := by
  have hE := setCoin_valid Dm c hc .bE (t * coin c .bE) (by decide) (by decide)
    (fun _ => mul_ne_zero ht (hc.2.1 .bE rfl))
  have hO := setCoin_valid Dm _ hE .bO (t * coin c .bO) (by decide) (by decide)
    (fun _ => mul_ne_zero ht (hc.2.1 .bO rfl))
  exact setCoin_valid Dm _ hO .bV (t * coin c .bV) (by decide) (by decide)
    (fun _ => mul_ne_zero ht (hc.2.1 .bV rfl))

@[simp] lemma piAt_scaleB (t : Fq P) (c : Coins P) (k : ℕ) : piAt (scaleB t c) k = piAt c k := by
  simp [piAt]

@[simp] lemma bOf_scaleB (t : Fq P) (c : Coins P) (X : LegKind) :
    bOf (scaleB t c) X = t * bOf c X := by cases X <;> simp [bOf]

@[simp] lemma legScale_scaleB (t : Fq P) (c : Coins P) (l : Leg P) :
    legScale (scaleB t c) l = t * legScale c l := by simp [legScale, legScaleAt, mul_assoc]

@[simp] lemma gamma_scaleB (t : Fq P) (c : Coins P) (cl : Cell P) :
    gamma (scaleB t c) cl = t * gamma c cl := by simp [gamma]; ring

@[simp] lemma kappa_scaleB (t : Fq P) (c : Coins P) (pp : PublicParams P) :
    kappa pp (scaleB t c) = t * kappa pp c := by
  simp [kappa, gammaKey, legScaleAt, mul_assoc]
  ring

@[simp] lemma legMask_scaleB (t : Fq P) (c : Coins P) (v : Fin P.n → Vec (Fq P) P.N) (l : Leg P) :
    legMask v (scaleB t c) l = legMask v c l := by simp [legMask]

@[simp] lemma crossVal_scaleB (t : Fq P) (c : Coins P) (g : CrossIdx) :
    crossVal (scaleB t c) g = crossVal c g := by cases g <;> simp [crossVal]

@[simp] lemma cTie_scaleB (t : Fq P) (c : Coins P) (s : TieIdx) :
    cTie (scaleB t c) s = cTie c s := by cases s <;> simp [cTie]

@[simp] lemma kummerAtU_scaleB (t : Fq P) (c : Coins P) :
    kummerAtU (scaleB t c) = kummerAtU c := by simp [kummerAtU]

lemma cellTerm_scaleB (pp : PublicParams P) (r : Vec (Fq P) P.N) (E : ExprT P)
    (σ : Sector) (t : Fq P) (c : Coins P) :
    cellTerm pp r E σ (scaleB t c) = t * cellTerm pp r E σ c := by
  simp [cellTerm, Finset.mul_sum, mul_assoc]

lemma maskTerm_scaleB (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P)
    (σ : Sector) (t : Fq P) (c : Coins P) : maskTerm v E σ (scaleB t c) = maskTerm v E σ c := by
  simp [maskTerm]

end Lines

lemma split_cell_mask {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N) (r : Vec (Fq P) P.N)
    (E : ExprT P) (σ : Sector) (ι : Fq P) (htwo : (2 : Fq P) ≠ 0)
    (hd : dC E σ = aC E σ)
    (h : ∀ c, ValidCoins pp.qap c → mainValue pp v r E σ c = ι * kappa pp c)
    (c : Coins P) (hc : ValidCoins pp.qap c) :
    cellTerm pp r E σ c = ι * kappa pp c ∧ maskTerm v E σ c = 0 := by
  have hb := h (setCoin c .Om12 0) (setOm12_valid pp.qap c hc 0)
  rw [mainValue_lines _ _ _ _ _ _ (hc.2.1 .Om22 rfl) hd, kappa_setOm12] at hb
  have hc2 := scaleB_valid 2 c pp.qap htwo hc
  have ht := h (setCoin (scaleB 2 c) .Om12 0) (setOm12_valid pp.qap _ hc2 0)
  rw [mainValue_lines _ _ _ _ _ _ (hc2.2.1 .Om22 rfl) hd, kappa_setOm12,
    cellTerm_scaleB, maskTerm_scaleB, kappa_scaleB] at ht
  constructor
  · linear_combination ht - hb
  · linear_combination 2 * hb - ht

lemma isKeyCell_iff_eq {P : Params} [NeZero P.K1] [NeZero P.K2] (cl : Cell P) :
    IsKeyCell cl ↔ cl = keyCell := by
  rcases cl with ⟨k,X,j⟩
  constructor
  · rintro ⟨hk, hX, hj⟩
    exact Prod.ext (Fin.ext hk) (Prod.ext hX (Fin.ext hj))
  · intro hkey
    rw [hkey]
    simp [IsKeyCell, keyCell]

lemma key_gamma_sum {P : Params} [Fact (Nat.Prime P.q)] [NeZero P.K1] [NeZero P.K2]
    (pp : PublicParams P) (c : Coins P) (ι : Fq P) :
    (∑ cl, gamma c cl * (if IsKeyCell cl then ι * pp.qap.Lrho.eval (coin c .tau) else 0)) =
      ι * kappa pp c := by
  classical
  simp only [isKeyCell_iff_eq, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [gamma, keyCell, legScale, gammaKey, kappa, Fin.val_zero]
  ring

lemma cell_evaluations (pp : PublicParams P0) (r : Vec (Fq P0) P0.N) (E : ExprT P0)
    (σ : Sector) (ι : Fq P0)
    (h : ∀ c, ValidCoins pp.qap c → cellTerm pp r E σ c = ι * kappa pp c)
    (y : Vec (Fq P0) P0.N) (τ : Fq P0) (hτ : ∀ k, τ ≠ pp.qap.point k) (cl : Cell P0) :
    braceVal pp r E σ cl y τ = if IsKeyCell cl then ι * pp.qap.Lrho.eval τ else 0 := by
  have hh : (fun cl => braceVal pp r E σ cl y τ -
      (if IsKeyCell cl then ι * pp.qap.Lrho.eval τ else 0)) = 0 := by
    apply cell_sep pp.qap y τ _ _ hτ
    intro c hc hy hcτ
    calc
      _ = cellTerm pp r E σ c -
          ∑ cl, gamma c cl * (if IsKeyCell cl then ι * pp.qap.Lrho.eval (coin c .tau) else 0) := by
        simp only [cellTerm, mul_sub, Finset.sum_sub_distrib, hy, hcτ]
      _ = 0 := by rw [key_gamma_sum, h c hc, sub_self]
  exact sub_eq_zero.mp (congrFun hh cl)

end Praxis.Proofs.View
