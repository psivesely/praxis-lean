import Praxis.Proofs.View.SZ.Model
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Proofs.View.SZ.Grid
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View.SZ

open Praxis.Algebra (Vec)

open MvPolynomial

@[simp] theorem eval_xs (c : Coins P0) (s : ScalarCoin) :
    eval (coinVar c) (xs s) = coin c s := by simp [xs, coinVar, coin]

@[simp] theorem eval_xy (c : Coins P0) (i : Fin (P0.N + 1)) :
    eval (coinVar c) (xy i) = c.1 i := by simp [xy, coinVar]

@[simp] theorem eval_tauP (c : Coins P0) (p : Polynomial (Fq P0)) :
    eval (coinVar c) (tauP p) = p.eval (coin c .tau) := by
  rw [tauP, Polynomial.hom_eval₂]
  have h : (eval (coinVar c)).comp C = RingHom.id (Fq P0) := by
    ext x
    simp
  rw [h]
  simp

@[simp] theorem eval_lamP (c : Coins P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Poly) (j : Fin (P0.N + 1)) :
    eval (coinVar c) (lamP v x j) = lam v (eval (coinVar c) x) j := by
  simp [lamP, lam, mul_comm]

@[simp] theorem eval_piP (c : Coins P0) (k : ℕ) :
    eval (coinVar c) (piP k) = piAt c k := by simp [piP, piAt, thetaAt]

@[simp] theorem eval_legP (c : Coins P0) (l : Leg P0) :
    eval (coinVar c) (legP l) = legScale c l := by
  rcases l with ⟨k, j⟩
  cases k <;> simp [legP, bP, legScale, legScaleAt, legExp, bOf]

@[simp] theorem eval_gammaP (c : Coins P0) (cl : Cell P0) :
    eval (coinVar c) (gammaP cl) = gamma c cl := by simp [gammaP, gamma]

@[simp] theorem eval_sectorP (c : Coins P0) (σ : Sector) :
    eval (coinVar c) (sectorP σ) = sectorScale c σ := by
  cases σ <;> simp [sectorP, sectorScale]

def denom (c : Coins P0) : Fq P0 :=
  coin c .Om22 * coin c .zeta * coin c .zeta' * coin c .zeta4 * coin c .eps

@[simp] theorem eval_denomP (c : Coins P0) : eval (coinVar c) denomP = denom c := by
  simp [denomP, denom]

theorem denom_ne_zero (Dm : QAPData P0) (c : Coins P0) (hc : ValidCoins Dm c) :
    denom c ≠ 0 := by
  unfold denom
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (hc.2.1 .Om22 rfl) (hc.2.1 .zeta rfl)) (hc.2.1 .zeta' rfl))
    (hc.2.1 .zeta4 rfl)) hc.2.2.1

@[simp] theorem eval_kappaP (pp : PublicParams P0) (c : Coins P0) :
    eval (coinVar c) (kappaP pp) = kappa pp c := by
  simp [kappaP, kappa, gammaKey, legScaleAt, bOf, LegKind.base]

@[simp] theorem eval_e1P (pp : PublicParams P0) (c : Coins P0)
    (r : Vec (Fq P0) P0.N) (a : Option (G1Idx P0)) :
    eval (coinVar c) (e1P pp a) = e1At pp ⟨c, r⟩ a := by
  cases a with
  | none => simp [e1P, e1At]
  | some a => cases a <;> simp [e1P, e1At, g1Exp]

theorem eval_maskP (c : Coins P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (l : Leg P0) (j : Fin (P0.N + 1)) (he : coin c .eps ≠ 0) :
    eval (coinVar c) (maskP v l j) = coin c .eps * legMask v c l j := by
  rcases l with ⟨k, a⟩
  cases k <;> simp [maskP, legMask, legExp, smul_eq_mul] <;> field_simp <;> ring

theorem eval_r1P (pp : PublicParams P0) (c : Coins P0)
    (v : Fin P0.n → Vec (Fq P0) P0.N) (r : Vec (Fq P0) P0.N)
    (l : Leg P0) (j : Fin (P0.N + 1)) (hc : ValidCoins pp.qap c) :
    eval (coinVar c) (r1P pp v r l j) = denom c * r1ExpAt pp v ⟨c, r⟩ l j := by
  have h22 := hc.2.1 .Om22 rfl
  change coin c .Om22 ≠ 0 at h22
  have he := hc.2.2.1
  simp [r1P, eval_maskP c v l j he, denom, r1ExpAt, H2]
  field_simp <;> ring

theorem eval_r2P (pp : PublicParams P0) (c : Coins P0)
    (l : Leg P0) (j : Fin (P0.N + 1)) (hc : ValidCoins pp.qap c) :
    eval (coinVar c) (r2P pp l j) = denom c * r2Exp pp c l j := by
  have h22 := hc.2.1 .Om22 rfl
  change coin c .Om22 ≠ 0 at h22
  simp [r2P, denom, r2Exp, H2]
  field_simp <;> ring

@[simp] theorem eval_crossP (c : Coins P0) (g : CrossIdx) (he : coin c .eps ≠ 0) :
    eval (coinVar c) (crossP g) = coin c .eps * crossVal c g := by
  cases g <;> simp [crossP, crossVal] <;> field_simp <;> ring

@[simp] theorem eval_tieP (c : Coins P0) (s : TieIdx) :
    eval (coinVar c) (tieP s) = cTie c s := by
  cases s <;> simp [tieP, cTie]

set_option maxRecDepth 4096 in
theorem eval_e2P (pp : PublicParams P0) (c : Coins P0)
    (v : Fin P0.n → Vec (Fq P0) P0.N) (r : Vec (Fq P0) P0.N)
    (a : Option (G2Idx P0)) (hc : ValidCoins pp.qap c) :
    eval (coinVar c) (e2P pp v r a) = denom c * e2At pp v ⟨c, r⟩ a := by
  have h22 := hc.2.1 .Om22 rfl
  have hz := hc.2.1 .zeta rfl
  have hz' := hc.2.1 .zeta' rfl
  have hz4 := hc.2.1 .zeta4 rfl
  have he := hc.2.2.1
  change coin c .Om22 ≠ 0 at h22
  change coin c .zeta ≠ 0 at hz
  change coin c .zeta' ≠ 0 at hz'
  change coin c .zeta4 ≠ 0 at hz4
  change coin c .eps ≠ 0 at he
  cases a with
  | none => simp [e2P, e2At]
  | some a =>
    cases a <;> simp [e2P, e2At, g2Exp, eval_r1P pp c v r _ _ hc,
      eval_r2P pp c _ _ hc, eval_crossP c _ he, denom, Finset.mul_sum,
      kummerAtU] <;> try (field_simp <;> ring)
    all_goals (apply Finset.sum_congr rfl <;> intro i hi <;> ring)

theorem eval_differenceP (pp : PublicParams P0) (c : Coins P0)
    (v : Fin P0.n → Vec (Fq P0) P0.N) (r : Vec (Fq P0) P0.N)
    (D : ExprT P0) (ι : Fq P0) (hc : ValidCoins pp.qap c) :
    eval (coinVar c) (differenceP pp v r D ι) =
      denom c * (valT pp v ⟨c, r⟩ D - ι * kappa pp c) := by
  simp only [differenceP, map_sub, map_add, map_mul, eval_C, eval_denomP,
    eval_xs, eval_kappaP, map_list_sum, List.map_map, Function.comp_def,
    eval_e1P pp c r _, eval_e2P pp c v r _ hc, valT, gtExp]
  have hs : ((keys1 P0).map fun a => ((keys2 P0).map fun b =>
      D.1 (a, b) * (e1At pp ⟨c, r⟩ a * (denom c * e2At pp v ⟨c, r⟩ b))).sum).sum =
      denom c * ((keys1 P0).map fun a => ((keys2 P0).map fun b =>
        D.1 (a, b) * (e1At pp ⟨c, r⟩ a * e2At pp v ⟨c, r⟩ b)).sum).sum := by
    simp only [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    ring
  rw [hs]
  ring

end Praxis.Proofs.View.SZ
