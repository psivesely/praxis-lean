import Praxis.Proofs.Reduction.Complete.Locus
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.View.ForwardCells
import Praxis.Proofs.View.ForwardSeparation
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Reduction

open Polynomial

noncomputable section

set_option maxRecDepth 4096

def shiftScalars {P : Params} (c : Coins P) (t : Fq P) : Coins P :=
  (c.1, c.2.1, fun s => coin c s + t)

section Generic

variable {P : Params} [Fact (Nat.Prime P.q)]

def scalarPoly (c : Coins P) (s : ScalarCoin) : Polynomial (Fq P) :=
  C (coin c s) + X

def piPoly (c : Coins P) (k : ℕ) : Polynomial (Fq P) :=
  scalarPoly c .pi * scalarPoly c .u ^ (2 * k) *
    (1 + scalarPoly c .eps * C (thetaAt k))

def legPoly (c : Coins P) (l : Leg P) : Polynomial (Fq P) :=
  (match l.1 with
    | .E => scalarPoly c .bE
    | .O => scalarPoly c .bO
    | .V => scalarPoly c .bV) * scalarPoly c .u ^ legExp l

def leftPoly (pp : PublicParams P) (c : Coins P) : Option (G1Idx P) → Polynomial (Fq P)
  | none => 1
  | some (.L1 k i) => piPoly c k.val * C (c.1 i)
  | some (.L2 k i) => piPoly c k.val *
      (scalarPoly c .Om12 * C (c.1 i) +
        scalarPoly c .Om22 * (pp.qap.A i).comp (scalarPoly c .tau))
  | some (.totL1 k) => ∑ i, piPoly c k.val * C (c.1 i)
  | some (.totL2 k) => ∑ i, piPoly c k.val *
      (scalarPoly c .Om12 * C (c.1 i) +
        scalarPoly c .Om22 * (pp.qap.A i).comp (scalarPoly c .tau))
  | some (.QP s) => scalarPoly c .zeta * scalarPoly c .tau ^ s.val
  | some (.RP s) => scalarPoly c .zeta' * scalarPoly c .tau ^ s.1.val
  | some (.GY i) => scalarPoly c .zeta4 * C (c.1 i)

def plainGradientPoly (pp : PublicParams P) (c : Coins P) (D : ExprT P)
    (x : Algebra.Vec (Fq P) P.N) : Polynomial (Fq P) :=
  ∑ j, ((legList P).map fun l => legPoly c l *
    ((keys1 P).map fun a => leftPoly pp c a *
      C (D.1 (a, some (.ZeroCoordinate .plain l j)) + D.1 (a, some (.totR1 .plain l)))).sum).sum * C (x j)

@[simp] theorem eval_scalarPoly (c : Coins P) (s : ScalarCoin) (t : Fq P) :
    (scalarPoly c s).eval t = coin (shiftScalars c t) s := by
  simp [scalarPoly, shiftScalars, coin]

theorem eval_piPoly (c : Coins P) (k : ℕ) (t : Fq P) :
    (piPoly c k).eval t = piAt (shiftScalars c t) k := by
  simp [piPoly, piAt]

theorem eval_legPoly (c : Coins P) (l : Leg P) (t : Fq P) :
    (legPoly c l).eval t = legScale (shiftScalars c t) l := by
  rcases l with ⟨k, i⟩
  cases k <;> simp [legPoly, legScale, legScaleAt, legExp, bOf]

theorem eval_leftPoly (pp : PublicParams P) (c : Coins P) (r : Algebra.Vec (Fq P) P.N)
    (a : Option (G1Idx P)) (t : Fq P) :
    (leftPoly pp c a).eval t = e1At pp ⟨shiftScalars c t, r⟩ a := by
  cases a with
  | none => simp [leftPoly, e1At]
  | some a =>
    cases a <;> simp [leftPoly, e1At, g1Exp, eval_piPoly, Polynomial.eval_comp, Polynomial.eval_finsetSum,
      shiftScalars]

theorem eval_plainGradientPoly (pp : PublicParams P) (c : Coins P)
    (r x : Algebra.Vec (Fq P) P.N) (D : ExprT P) (t : Fq P) :
    (plainGradientPoly pp c D x).eval t =
      ∑ j, rGrad pp ⟨shiftScalars c t, r⟩ D .plain j * x j := by
  unfold plainGradientPoly rGrad
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_listSum, List.map_map]
  apply congrArg (fun z : Fq P => z * x j)
  apply congrArg List.sum
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_legPoly, Polynomial.eval_listSum,
    List.map_map, sectorScale, one_mul]
  apply congrArg (fun z : Fq P => legScale (shiftScalars c t) l * z)
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_C, eval_leftPoly pp c r]

end Generic

private theorem degree_mul_bound (p q : Polynomial (Fq P0)) (a b : ℕ)
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) : (p * q).natDegree ≤ a + b :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

private theorem degree_add_bound (p q : Polynomial (Fq P0)) (a : ℕ)
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ a) : (p + q).natDegree ≤ a :=
  (natDegree_add_le _ _).trans (max_le hp hq)

private theorem degree_scalar (c : Coins P0) (s : ScalarCoin) :
    (scalarPoly c s).natDegree ≤ 1 := by
  exact (natDegree_add_le _ _).trans (by simp)

private theorem degree_scalar_pow (c : Coins P0) (s : ScalarCoin) (n : ℕ) :
    (scalarPoly c s ^ n).natDegree ≤ n := by
  calc
    _ ≤ n * (scalarPoly c s).natDegree := natDegree_pow_le
    _ ≤ n * 1 := Nat.mul_le_mul_left _ (degree_scalar c s)
    _ = n := Nat.mul_one _

private theorem degree_pi (c : Coins P0) (k : ℕ) :
    (piPoly c k).natDegree ≤ 2 * k + 2 := by
  have hε : (1 + scalarPoly c .eps * C (thetaAt k)).natDegree ≤ 1 := by
    apply degree_add_bound
    · simp
    · have h := degree_mul_bound (scalarPoly c .eps) (C (thetaAt k)) 1 0
        (degree_scalar c .eps) (by simp)
      simpa using h
  have h := degree_mul_bound (scalarPoly c .pi * scalarPoly c .u ^ (2 * k))
    (1 + scalarPoly c .eps * C (thetaAt k)) (1 + 2 * k) 1
    (degree_mul_bound _ _ 1 (2 * k) (degree_scalar c .pi) (degree_scalar_pow c .u _)) hε
  change (piPoly c k).natDegree ≤ _ at h
  exact h.trans (by omega)

private theorem degree_leg (c : Coins P0) (l : Leg P0) :
    (legPoly c l).natDegree ≤ P0.n + 1 := by
  have hl : legExp l ≤ P0.n := by
    rcases l with ⟨k, i⟩
    have h := i.isLt
    cases k <;> simp only [legExp, LegKind.base] <;>
      simp only [P0, Params.main, Constants.K1, Constants.K2, Constants.n] at * <;> omega
  have hd : (match l.1 with
    | .E => scalarPoly c .bE | .O => scalarPoly c .bO | .V => scalarPoly c .bV).natDegree ≤ 1 := by
      rcases l with ⟨k, i⟩
      cases k <;> exact degree_scalar c _
  have h := degree_mul_bound _ _ 1 (legExp l) hd (degree_scalar_pow c .u _)
  exact h.trans (by omega)

private theorem degree_left (pp : PublicParams P0) (hD : ValidQAP pp.qap pp.S)
    (c : Coins P0) (a : Option (G1Idx P0)) :
    (leftPoly pp c a).natDegree ≤ P0.D + 2 * P0.K1 + 10 := by
  have hp (k : Fin P0.K1) : (piPoly c k.val).natDegree ≤ 2 * P0.K1 + 2 := by
    have h := degree_pi c k.val
    have hk := k.isLt
    omega
  have hA (i : Fin (P0.N + 1)) :
      ((pp.qap.A i).comp (scalarPoly c .tau)).natDegree ≤ P0.D := by
    have h := natDegree_comp_le (p := pp.qap.A i) (q := scalarPoly c .tau)
    have hd := hD.A_degree i
    have hs := degree_scalar c .tau
    calc
      _ ≤ (pp.qap.A i).natDegree * (scalarPoly c .tau).natDegree := h
      _ ≤ P0.D * 1 := Nat.mul_le_mul (Nat.le_of_lt hd) hs
      _ = P0.D := Nat.mul_one _
  have hL1 (k : Fin P0.K1) (i : Fin (P0.N + 1)) :
      (piPoly c k.val * C (c.1 i)).natDegree ≤ P0.D + 2 * P0.K1 + 10 := by
    have h := degree_mul_bound (piPoly c k.val) (C (c.1 i)) (2 * P0.K1 + 2) 0 (hp k) (by simp)
    omega
  have hL2 (k : Fin P0.K1) (i : Fin (P0.N + 1)) :
      (piPoly c k.val * (scalarPoly c .Om12 * C (c.1 i) +
        scalarPoly c .Om22 * (pp.qap.A i).comp (scalarPoly c .tau))).natDegree ≤
        P0.D + 2 * P0.K1 + 10 := by
    have h₁ : (scalarPoly c .Om12 * C (c.1 i)).natDegree ≤ P0.D + 1 := by
      have h := degree_mul_bound (scalarPoly c .Om12) (C (c.1 i)) 1 0 (degree_scalar c .Om12) (by simp)
      omega
    have h₂ : (scalarPoly c .Om22 * (pp.qap.A i).comp (scalarPoly c .tau)).natDegree ≤ P0.D + 1 := by
      have h := degree_mul_bound _ _ 1 P0.D (degree_scalar c .Om22) (hA i)
      omega
    have h := degree_mul_bound _ _ (2 * P0.K1 + 2) (P0.D + 1) (hp k)
      (degree_add_bound _ _ _ h₁ h₂)
    omega
  cases a with
  | none => simp [leftPoly]
  | some a =>
    cases a with
    | L1 k i => exact hL1 k i
    | L2 k i => exact hL2 k i
    | totL1 k =>
      exact natDegree_sum_le_of_forall_le _ _ (fun i _ => hL1 k i)
    | totL2 k =>
      exact natDegree_sum_le_of_forall_le _ _ (fun i _ => hL2 k i)
    | QP s =>
      have h := degree_mul_bound _ _ 1 s.val (degree_scalar c .zeta) (degree_scalar_pow c .tau _)
      have hs := s.isLt
      have hb : P0.E1 ≤ P0.D := by decide
      exact h.trans (by omega)
    | RP s =>
      have h := degree_mul_bound _ _ 1 s.1.val (degree_scalar c .zeta') (degree_scalar_pow c .tau _)
      have hs := s.1.isLt
      have hb : P0.U * P0.E1p ≤ P0.D := by decide
      exact h.trans (by omega)
    | GY i =>
      have h := degree_mul_bound (scalarPoly c .zeta4) (C (c.1 i)) 1 0 (degree_scalar c .zeta4) (by simp)
      exact h.trans (by omega)

theorem degree_plainGradientPoly (pp : PublicParams P0) (hD : ValidQAP pp.qap pp.S)
    (c : Coins P0) (D : ExprT P0) (x : Algebra.Vec (Fq P0) P0.N) :
    (plainGradientPoly pp c D x).natDegree ≤ 2 * P0.D + P0.n + 1000 := by
  unfold plainGradientPoly
  apply natDegree_sum_le_of_forall_le
  intro j _
  have hinner (l : Leg P0) :
      (((keys1 P0).map fun a => leftPoly pp c a *
        C (D.1 (a, some (.ZeroCoordinate .plain l j)) + D.1 (a, some (.totR1 .plain l)))).sum).natDegree ≤
          P0.D + 2 * P0.K1 + 10 := by
    apply View.polynomial_list_degree_le
    intro a _
    have h := degree_mul_bound (leftPoly pp c a)
      (C (D.1 (a, some (.ZeroCoordinate .plain l j)) + D.1 (a, some (.totR1 .plain l))))
      (P0.D + 2 * P0.K1 + 10) 0 (degree_left pp hD c a) (by simp)
    simpa using h
  have hlegs : (((legList P0).map fun l => legPoly c l *
      ((keys1 P0).map fun a => leftPoly pp c a *
        C (D.1 (a, some (.ZeroCoordinate .plain l j)) + D.1 (a, some (.totR1 .plain l)))).sum).sum).natDegree ≤
      (P0.n + 1) + (P0.D + 2 * P0.K1 + 10) := by
    apply View.polynomial_list_degree_le
    intro l _
    exact degree_mul_bound _ _ _ _ (degree_leg c l) (hinner l)
  have h := degree_mul_bound _ (C (x j)) ((P0.n + 1) + (P0.D + 2 * P0.K1 + 10)) 0 hlegs (by simp)
  have hc : 2 * P0.K1 + 11 ≤ P0.D + 1000 := by decide
  exact h.trans (by omega)

theorem shift_polynomial_zero {P : Params} [Fact (Nat.Prime P.q)]
    (Dm : QAPData P) (c : Coins P) (d : ℕ)
    (hsize : Fintype.card (QAPIndex P) = P.D)
    (hcard : d < P.q - (P.D + 16 + P.K1))
    (p : Polynomial (Fq P)) (hd : p.natDegree ≤ d)
    (h : ∀ t, ValidCoins Dm (shiftScalars c t) → p.eval t = 0) : p = 0 := by
  classical
  let badτ : Finset (Fq P) := Finset.univ.image fun k : QAPIndex P => Dm.point k - coin c .tau
  let badu : Finset (Fq P) := Finset.univ.image fun s : ScalarCoin => -coin c s
  let badε : Finset (Fq P) := Finset.univ.image fun k : Fin P.K1 =>
    -(betaF P ^ (2 * k.val))⁻¹ - coin c .eps
  let bad := badτ ∪ badu ∪ badε
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (Finset.univ \ bad)
  · intro t ht
    have hn : t ∉ bad := (Finset.mem_sdiff.mp ht).2
    apply h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      apply hn
      have : t = Dm.point k - coin c .tau := by
        change coin c .tau + t = Dm.point k at hk
        linear_combination hk
      simp only [bad, Finset.mem_union]
      exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, this.symm⟩))
    · intro s _ hs
      apply hn
      have : t = -coin c s := by
        change coin c s + t = 0 at hs
        linear_combination hs
      simp only [bad, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, this.symm⟩))
    · intro hs
      apply hn
      have : t = -coin c .eps := by
        change coin c .eps + t = 0 at hs
        linear_combination hs
      simp only [bad, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨.eps, Finset.mem_univ _, this.symm⟩))
    · intro k hs
      apply hn
      have : t = -(betaF P ^ (2 * k.val))⁻¹ - coin c .eps := by
        change coin c .eps + t = _ at hs
        linear_combination hs
      simp only [bad, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, this.symm⟩)
  · have hτ : badτ.card ≤ P.D := by
      exact Finset.card_image_le.trans_eq (by simp only [Finset.card_univ, hsize])
    have hu : badu.card ≤ 16 := by
      exact Finset.card_image_le.trans_eq (by decide)
    have hε : badε.card ≤ P.K1 := by
      exact Finset.card_image_le.trans_eq (by simp)
    have hb : bad.card ≤ P.D + 16 + P.K1 := by
      exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_right (Finset.card_union_le _ _) _).trans
        (Nat.add_le_add (Nat.add_le_add hτ hu) hε))
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ bad)]
    simp only [Finset.card_univ, ZMod.card]
    exact hd.trans_lt (hcard.trans_le (Nat.sub_le_sub_left hb _))

theorem plain_gradient_zero (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (D : ExprT P0)
    (r : Algebra.Vec (Fq P0) P0.N) (ι : Fq P0)
    (hid : IdentityAtR (ppOf ch S) (formVec A) r D ι)
    (hplain : exprStack D .plain = 0) (ω : Assign P0) :
    rGrad (ppOf ch S) ω D .plain = 0 := by
  let c := ω.coins
  have hpoly (x : Algebra.Vec (Fq P0) P0.N) :
      plainGradientPoly (ppOf ch S) c D x = 0 := by
    apply shift_polynomial_zero (ppOf ch S).qap c (2 * P0.D + P0.n + 1000)
      View.qapIndex_card (by decide)
    · exact degree_plainGradientPoly (ppOf ch S) (QAP.domainMap_valid ch S) c D x
    · intro t ht
      rw [eval_plainGradientPoly _ _ r]
      exact plain_gradient_orthogonal_valid ch S hS A D r x ι hid hplain _ ht
  have hc : shiftScalars c 0 = c := by
    cases c with
    | mk y c => cases c with
      | mk z s => simp [shiftScalars, coin]
  funext j
  have h := congrArg (fun p : Polynomial (Fq P0) => p.eval 0) (hpoly (Pi.single j 1))
  rw [eval_plainGradientPoly _ _ r, hc] at h
  have hr : rGrad (ppOf ch S) ⟨c, r⟩ D .plain = rGrad (ppOf ch S) ω D .plain := rfl
  rw [hr] at h
  simpa only [eval_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] using h

end

end Praxis.Proofs.Reduction
