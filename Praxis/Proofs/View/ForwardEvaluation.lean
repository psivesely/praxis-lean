import Praxis.Proofs.View.ForwardMain
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardHelpers
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

section Sums

variable {P : Params} {M α β : Type*} [AddCommMonoid M] [Fintype α] [Fintype β]

lemma sum_cells1 (f : Cell P → α → M) :
    (∑ k : Fin P.K1, ∑ i : α, ∑ l : Leg P, f (k,l) i) = ∑ cl, ∑ i, f cl i := by
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_comm

lemma sum_cells2 (f : Cell P → α → β → M) :
    (∑ k : Fin P.K1, ∑ i : α, ∑ l : Leg P, ∑ j : β, f (k,l) i j) =
      ∑ cl, ∑ i, ∑ j, f cl i j := by
  exact sum_cells1 (fun cl i => ∑ j, f cl i j)

end Sums

section RawValue

variable {P : Params} [Fact (Nat.Prime P.q)]

noncomputable def rawClassValue (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) : Fq P :=
  (∑ k, ∑ i, ∑ l, ∑ j, aC E σ (k,l) i j *
    (e1At pp ⟨c,r⟩ (some (.L1 k i)) * e2At pp v ⟨c,r⟩ (some (.ZeroCoordinate σ l j)))) +
  (∑ k, ∑ i, ∑ l, ∑ j, dC E σ (k,l) i j *
    (e1At pp ⟨c,r⟩ (some (.L2 k i)) * e2At pp v ⟨c,r⟩ (some (.R2 σ l j)))) +
  (∑ k, ∑ i, ∑ l, sC E σ (k,l) i *
    (e1At pp ⟨c,r⟩ (some (.L1 k i)) * e2At pp v ⟨c,r⟩ (some (.SC σ l)))) +
  (∑ k, ∑ i, lC E σ k i * e1At pp ⟨c,r⟩ (some (.L1 k i))) +
  (∑ a, ∑ cl, ∑ j, E.1 (some (.QP a), some (.QB σ cl j)) *
    (e1At pp ⟨c,r⟩ (some (.QP a)) * e2At pp v ⟨c,r⟩ (some (.QB σ cl j)))) +
  (∑ a, ∑ cl, ∑ j, E.1 (some (.RP a), some (.RB σ cl j)) *
    (e1At pp ⟨c,r⟩ (some (.RP a)) * e2At pp v ⟨c,r⟩ (some (.RB σ cl j)))) +
  (∑ i, ∑ g, ∑ e, gbC E σ i g e *
    (e1At pp ⟨c,r⟩ (some (.GY i)) * e2At pp v ⟨c,r⟩ (some (.GB σ g e)))) +
  (∑ i, ∑ s, ∑ e, gmC E σ i s e *
    (e1At pp ⟨c,r⟩ (some (.GY i)) * e2At pp v ⟨c,r⟩ (some (.GM σ s e))))

noncomputable def classRightSum (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (a : Option (G1Idx P)) : Fq P :=
  ((keys2 P).map fun b => classCoeff E σ a b * (e1At pp ⟨c,r⟩ a * e2At pp v ⟨c,r⟩ b)).sum

set_option maxHeartbeats 1000000 in
lemma classRightSum_none (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P)  :
    classRightSum pp v r E σ c (none) = 0 := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classRightSum_L1 (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (k : Fin P.K1) (i : Fin (P.N+1)) :
    classRightSum pp v r E σ c (some (.L1 k i)) = lC E σ k i * e1At pp ⟨c,r⟩ (some (.L1 k i)) +
      (∑ l, ∑ j, aC E σ (k,l) i j * (e1At pp ⟨c,r⟩ (some (.L1 k i)) * e2At pp v ⟨c,r⟩ (some (.ZeroCoordinate σ l j)))) +
      ∑ l, sC E σ (k,l) i * (e1At pp ⟨c,r⟩ (some (.L1 k i)) * e2At pp v ⟨c,r⟩ (some (.SC σ l))) := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classRightSum_L2 (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (k : Fin P.K1) (i : Fin (P.N+1)) :
    classRightSum pp v r E σ c (some (.L2 k i)) = ∑ l, ∑ j, dC E σ (k,l) i j *
      (e1At pp ⟨c,r⟩ (some (.L2 k i)) * e2At pp v ⟨c,r⟩ (some (.R2 σ l j))) := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classRightSum_totL1 (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (k : Fin P.K1) :
    classRightSum pp v r E σ c (some (.totL1 k)) = 0 := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classRightSum_totL2 (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (k : Fin P.K1) :
    classRightSum pp v r E σ c (some (.totL2 k)) = 0 := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classRightSum_QP (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (a : Fin P.E1) :
    classRightSum pp v r E σ c (some (.QP a)) = ∑ cl, ∑ j, E.1 (some (.QP a), some (.QB σ cl j)) *
      (e1At pp ⟨c,r⟩ (some (.QP a)) * e2At pp v ⟨c,r⟩ (some (.QB σ cl j))) := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classRightSum_RP (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (a : RemExp P) :
    classRightSum pp v r E σ c (some (.RP a)) = ∑ cl, ∑ j, E.1 (some (.RP a), some (.RB σ cl j)) *
      (e1At pp ⟨c,r⟩ (some (.RP a)) * e2At pp v ⟨c,r⟩ (some (.RB σ cl j))) := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classRightSum_GY (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (i : Fin (P.N+1)) :
    classRightSum pp v r E σ c (some (.GY i)) = (∑ g, ∑ e, gbC E σ i g e *
      (e1At pp ⟨c,r⟩ (some (.GY i)) * e2At pp v ⟨c,r⟩ (some (.GB σ g e)))) +
      ∑ s, ∑ e, gmC E σ i s e *
      (e1At pp ⟨c,r⟩ (some (.GY i)) * e2At pp v ⟨c,r⟩ (some (.GM σ s e))) := by
  cases σ <;> simp [classRightSum, keys2_sum, classCoeff, sum_sector,
    aC, dC, sC, lC, gbC, gmC, e2At] <;> ring

set_option maxHeartbeats 1000000 in
lemma classExpr_value_raw (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) :
    valT pp v ⟨c,r⟩ (classExpr E σ) = rawClassValue pp v r E σ c +
      (if σ = .alpha then E.2 * gtExp pp c else 0) := by
  change ((keys1 P).map (classRightSum pp v r E σ c)).sum +
    (if σ = .alpha then E.2 else 0) * gtExp pp c = _
  simp only [keys1_sum, classRightSum_none, classRightSum_L1, classRightSum_L2,
    classRightSum_totL1, classRightSum_totL2, classRightSum_QP, classRightSum_RP,
    classRightSum_GY, rawClassValue, Finset.sum_add_distrib, Finset.sum_const_zero,
    zero_add, add_zero, ite_mul, zero_mul]
  ring

noncomputable def mainValue (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) : Fq P :=
  (∑ cl, ∑ i, ∑ j, aC E σ cl i j * piAt c cl.1.val * c.1 i * r1ExpAt pp v ⟨c,r⟩ cl.2 j) +
  (∑ cl, ∑ i, ∑ j, dC E σ cl i j * piAt c cl.1.val *
    (coin c .Om12 * c.1 i + coin c .Om22 * (pp.qap.A i).eval (coin c .tau)) *
      (H2 pp c cl.2 j / coin c .Om22)) +
  (∑ cl, ∑ i, sC E σ cl i * piAt c cl.1.val * c.1 i * legScale c cl.2) +
  (∑ k, ∑ i, lC E σ k i * piAt c k.val * c.1 i) +
  (∑ cl, gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) * (hC E σ cl).eval (coin c .tau)) +
  (∑ cl, gamma c cl * pp.qap.Z0.eval (coin c .tau) * (RC E σ cl).eval (coin c .tau)) +
  coin c .pi * (∑ i, c.1 i * ∑ g, crossVal c g * ∑ e, gbC E σ i g e * coin c .u ^ e.val) +
  coin c .pi * kummerAtU c * (∑ i, c.1 i * ∑ s, cTie c s * ∑ e, gmC E σ i s e * coin c .u ^ e.val)

lemma raw_quot_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hz : coin c .zeta ≠ 0) :
    (∑ a, ∑ cl, ∑ j, E.1 (some (.QP a), some (.QB σ cl j)) *
      (e1At pp ⟨c,r⟩ (some (.QP a)) * e2At pp v ⟨c,r⟩ (some (.QB σ cl j)))) =
    sectorScale c σ * ∑ cl, gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) *
      (hC E σ cl).eval (coin c .tau) := by
  rw [Finset.sum_comm]
  simp only [hC, eval_finsetSum, eval_monomial, pow_add, Finset.mul_sum, e1At, g1Exp, e2At, g2Exp]
  apply Finset.sum_congr rfl
  intro cl _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hz]

lemma raw_rem_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hz : coin c .zeta' ≠ 0) :
    (∑ a, ∑ cl, ∑ j, E.1 (some (.RP a), some (.RB σ cl j)) *
      (e1At pp ⟨c,r⟩ (some (.RP a)) * e2At pp v ⟨c,r⟩ (some (.RB σ cl j)))) =
    sectorScale c σ * ∑ cl, gamma c cl * pp.qap.Z0.eval (coin c .tau) *
      (RC E σ cl).eval (coin c .tau) := by
  rw [Finset.sum_comm]
  simp only [RC, eval_finsetSum, eval_monomial, pow_add, Finset.mul_sum, e1At, g1Exp, e2At, g2Exp]
  apply Finset.sum_congr rfl
  intro cl _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hz]

lemma raw_cross_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hz : coin c .zeta4 ≠ 0) :
    (∑ i, ∑ g, ∑ e, gbC E σ i g e *
      (e1At pp ⟨c,r⟩ (some (.GY i)) * e2At pp v ⟨c,r⟩ (some (.GB σ g e)))) =
    sectorScale c σ * (coin c .pi * (∑ i, c.1 i * ∑ g, crossVal c g *
      ∑ e, gbC E σ i g e * coin c .u ^ e.val)) := by
  simp only [Finset.mul_sum, e1At, g1Exp, e2At, g2Exp]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro e _
  field_simp [hz]

lemma raw_tie_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hz : coin c .zeta4 ≠ 0) :
    (∑ i, ∑ s, ∑ e, gmC E σ i s e *
      (e1At pp ⟨c,r⟩ (some (.GY i)) * e2At pp v ⟨c,r⟩ (some (.GM σ s e)))) =
    sectorScale c σ * (coin c .pi * kummerAtU c * (∑ i, c.1 i * ∑ s, cTie c s *
      ∑ e, gmC E σ i s e * coin c .u ^ e.val)) := by
  simp only [Finset.mul_sum, e1At, g1Exp, e2At, g2Exp]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro e _
  field_simp [hz]

set_option maxHeartbeats 1000000 in
lemma rawClassValue_eq_mainValue (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (c : Coins P) (hc : ValidCoins pp.qap c) :
    rawClassValue pp v r E σ c = sectorScale c σ * mainValue pp v r E σ c := by
  have hL : (∑ k, ∑ i, lC E σ k i * e1At pp ⟨c,r⟩ (some (.L1 k i))) =
      sectorScale c σ * (∑ k, ∑ i, lC E σ k i * piAt c k.val * c.1 i) := by
    cases σ <;> simp [lC, e1At, g1Exp, sectorScale, mul_assoc]
  unfold rawClassValue mainValue
  rw [sum_cells2 (fun cl i j => aC E σ cl i j *
      (e1At pp ⟨c,r⟩ (some (.L1 cl.1 i)) * e2At pp v ⟨c,r⟩ (some (.ZeroCoordinate σ cl.2 j)))),
    sum_cells2 (fun cl i j => dC E σ cl i j *
      (e1At pp ⟨c,r⟩ (some (.L2 cl.1 i)) * e2At pp v ⟨c,r⟩ (some (.R2 σ cl.2 j)))),
    sum_cells1 (fun cl i => sC E σ cl i *
      (e1At pp ⟨c,r⟩ (some (.L1 cl.1 i)) * e2At pp v ⟨c,r⟩ (some (.SC σ cl.2)))), hL,
    raw_quot_value _ _ _ _ _ _ (hc.2.1 .zeta rfl),
    raw_rem_value _ _ _ _ _ _ (hc.2.1 .zeta' rfl),
    raw_cross_value _ _ _ _ _ _ (hc.2.1 .zeta4 rfl),
    raw_tie_value _ _ _ _ _ _ (hc.2.1 .zeta4 rfl)]
  have h1 : (∑ cl, ∑ i, ∑ j, aC E σ cl i j *
      (e1At pp ⟨c,r⟩ (some (.L1 cl.1 i)) * e2At pp v ⟨c,r⟩ (some (.ZeroCoordinate σ cl.2 j)))) =
      sectorScale c σ * (∑ cl, ∑ i, ∑ j, aC E σ cl i j * piAt c cl.1.val * c.1 i *
        r1ExpAt pp v ⟨c,r⟩ cl.2 j) := by
    simp only [Finset.mul_sum, e1At, g1Exp, e2At]
    apply Finset.sum_congr rfl
    intro cl _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : (∑ cl, ∑ i, ∑ j, dC E σ cl i j *
      (e1At pp ⟨c,r⟩ (some (.L2 cl.1 i)) * e2At pp v ⟨c,r⟩ (some (.R2 σ cl.2 j)))) =
      sectorScale c σ * (∑ cl, ∑ i, ∑ j, dC E σ cl i j * piAt c cl.1.val *
        (coin c .Om12 * c.1 i + coin c .Om22 * (pp.qap.A i).eval (coin c .tau)) *
        (H2 pp c cl.2 j / coin c .Om22)) := by
    simp only [Finset.mul_sum, e1At, g1Exp, e2At, g2Exp, r2Exp]
    apply Finset.sum_congr rfl
    intro cl _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : (∑ cl, ∑ i, sC E σ cl i *
      (e1At pp ⟨c,r⟩ (some (.L1 cl.1 i)) * e2At pp v ⟨c,r⟩ (some (.SC σ cl.2)))) =
      sectorScale c σ * (∑ cl, ∑ i, sC E σ cl i * piAt c cl.1.val * c.1 i * legScale c cl.2) := by
    simp only [Finset.mul_sum, e1At, g1Exp, e2At, g2Exp]
    apply Finset.sum_congr rfl
    intro cl _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1, h2, hs]
  ring

end RawValue

lemma mainValue_identity (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0) (h : IdentityAtR pp v r D ι)
    (σ : Sector) (c : Coins P0) (hc : ValidCoins pp.qap c) :
    mainValue pp v r (expandTot D) σ c = (if σ = .plain then ι else -D.2) * kappa pp c := by
  have hh := mainProject_identity pp v r D ι h σ c hc
  rw [mainProject_eq_classExpr, classExpr_value_raw, rawClassValue_eq_mainValue _ _ _ _ _ _ hc] at hh
  cases σ
  · simpa only [sectorScale, reduceCtorEq, ite_true, ite_false, zero_mul, one_mul, add_zero] using hh
  · have hα := hc.2.1 .alpha rfl
    change coin c .alpha ≠ 0 at hα
    simp only [sectorScale, gtExp, reduceCtorEq, ite_true, ite_false] at hh ⊢
    have hE2 : (expandTot D).2 = D.2 := rfl
    rw [hE2] at hh
    apply (mul_left_inj' hα).mp
    linear_combination hh

end Praxis.Proofs.View
