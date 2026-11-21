import Praxis.Proofs.View.Locus.Separation
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Proofs.View.ForwardMain
import Praxis.Proofs.View.Locus.Rows
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View.Locus

open Praxis.Algebra (Vec Mat)

variable {P : Params} [Fact (Nat.Prime P.q)]

def rightDelta (c : Coins P) (d : Vec (Fq P) P.N) : Option (G2Idx P) → Fq P
  | some (.ZeroCoordinate σ l j) => sectorScale c σ * (legScale c l * d j)
  | some (.totR1 σ l) => sectorScale c σ * ∑ j, legScale c l * d j
  | _ => 0

lemma e2Delta (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (c : Coins P) (r r' : Vec (Fq P) P.N) (b : Option (G2Idx P)) :
    e2At pp v ⟨c,r'⟩ b - e2At pp v ⟨c,r⟩ b = rightDelta c (r'-r) b := by
  cases b with
  | none => simp [e2At, rightDelta]
  | some b =>
    cases b <;> simp only [e2At, rightDelta, r1ExpAt, Pi.sub_apply]
    · ring
    · ring
    · rw [← mul_sub, ← Finset.sum_sub_distrib]
      apply congrArg (fun x : Fq P => sectorScale c _ * x)
      apply Finset.sum_congr rfl
      intro j _
      ring
    all_goals ring

lemma list_sum_sub {α R : Type*} [AddCommGroup R] (xs : List α) (f g : α → R) :
    (xs.map f).sum - (xs.map g).sum = (xs.map fun x => f x - g x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ← ih]; abel

lemma list_sum_finset {α β R : Type*} [AddCommMonoid R]
    (xs : List α) (s : Finset β) (f : α → β → R) :
    (xs.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (xs.map fun a => f a b).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

lemma value_displacement (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (c : Coins P) (r r' : Vec (Fq P) P.N) (D : ExprT P) :
    valT pp v ⟨c,r'⟩ (expandTot D) - valT pp v ⟨c,r⟩ (expandTot D) =
      ∑ j, (((keys1 P).map fun a => e1At pp ⟨c,r⟩ a * rowCoeff (expandTot D) c a j).sum) *
        (r' j - r j) := by
  have hv : valT pp v ⟨c,r'⟩ (expandTot D) - valT pp v ⟨c,r⟩ (expandTot D) =
      ((keys1 P).map fun a => ((keys2 P).map fun b =>
        (expandTot D).1 (a,b) * (e1At pp ⟨c,r⟩ a * rightDelta c (r'-r) b)).sum).sum := by
    unfold valT
    rw [add_sub_add_right_eq_sub, list_sum_sub]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    rw [list_sum_sub]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b _
    have he : e1At pp ⟨c,r'⟩ a = e1At pp ⟨c,r⟩ a := by cases a <;> rfl
    rw [he, ← e2Delta pp v c r r' b]
    ring
  rw [hv]
  have hr (a : Option (G1Idx P)) :
      ((keys2 P).map fun b => (expandTot D).1 (a,b) *
        (e1At pp ⟨c,r⟩ a * rightDelta c (r'-r) b)).sum =
      ∑ j, (e1At pp ⟨c,r⟩ a * rowCoeff (expandTot D) c a j) * (r' j - r j) := by
    simp only [keys2_sum, rightDelta, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      show ∀ σ l, (expandTot D).1 (a, some (.totR1 σ l)) = 0 from fun _ _ => rfl,
      zero_mul, Pi.sub_apply]
    simp only [rowCoeff, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hr, list_sum_finset]
  apply Finset.sum_congr rfl
  intro j _
  exact List.sum_map_mul_right (keys1 P) _ _

lemma rowCoeff_totL1 (D : ExprT P) (c : Coins P) (k : Fin P.K1) (j : Fin (P.N+1)) :
    rowCoeff (expandTot D) c (some (.totL1 k)) j = 0 := by
  simp [rowCoeff, expandTot, expand2, expand2C, expand1, expand1C]

lemma rowCoeff_totL2 (D : ExprT P) (c : Coins P) (k : Fin P.K1) (j : Fin (P.N+1)) :
    rowCoeff (expandTot D) c (some (.totL2 k)) j = 0 := by
  simp [rowCoeff, expandTot, expand2, expand2C, expand1, expand1C]

lemma left_sum_reduction (pp : PublicParams P) (c : Coins P) (r : Vec (Fq P) P.N)
    (D : ExprT P) (j : Fin (P.N+1))
    (hm : mixingCoeff (expandTot D) c = 0)
    (hf : (fun i j => rowCoeff (expandTot D) c (some (.GY i)) j) = 0)
    (hg : constantCoeff (expandTot D) c = 0) :
    ((keys1 P).map fun a => e1At pp ⟨c,r⟩ a * rowCoeff (expandTot D) c a j).sum =
      ∑ k, ∑ i, (piAt c k.val * c.1 i) * rowCoeff (expandTot D) c (some (.L1 k i)) j := by
  have hmix : (∑ k, ∑ i, (piAt c k.val * (coin c .Om12 * c.1 i +
      coin c .Om22 * (pp.qap.A i).eval (coin c .tau))) *
        rowCoeff (expandTot D) c (some (.L2 k i)) j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    calc
      _ = (coin c .Om12 * c.1 i + coin c .Om22 * (pp.qap.A i).eval (coin c .tau)) *
          mixingCoeff (expandTot D) c i j := by
        simp only [mixingCoeff, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by rw [hm]; simp
  have hlin : (∑ i, (coin c .zeta4 * c.1 i) * rowCoeff (expandTot D) c (some (.GY i)) j) = 0 := by
    have hz (i) : rowCoeff (expandTot D) c (some (.GY i)) j = 0 := congrFun (congrFun hf i) j
    simp only [hz, mul_zero, Finset.sum_const_zero]
  have hgen := congrFun hg j
  change constantCoeff (expandTot D) c j = 0 at hgen
  simp only [constantCoeff] at hgen
  simp only [keys1_sum, e1At, g1Exp, rowCoeff_totL1, rowCoeff_totL2,
    mul_zero, Finset.sum_const_zero, add_zero, one_mul, hmix, hlin]
  linear_combination hgen

lemma stack_displacement (D : ExprT P) (c : Coins P) (r r' : Vec (Fq P) P.N)
    (hr : ∀ σ cl, (exprStack D σ cl).mulVec r = exprSC D σ cl)
    (hr' : ∀ σ cl, (exprStack D σ cl).mulVec r' = exprSC D σ cl) :
    (∑ j, (∑ k, ∑ i, (piAt c k.val * c.1 i) *
      rowCoeff (expandTot D) c (some (.L1 k i)) j) * (r' j - r j)) = 0 := by
  have hs (σ : Sector) (l : Leg P) (k : Fin P.K1) (i : Fin (P.N+1)) :
      ∑ j, (expandTot D).1 (some (.L1 k i), some (.ZeroCoordinate σ l j)) * (r' j - r j) = 0 := by
    have hh := congrFun ((hr' σ (k,l)).trans (hr σ (k,l)).symm) i
    simp only [Matrix.mulVec, dotProduct] at hh
    have ha (j) : (expandTot D).1 (some (.L1 k i), some (.ZeroCoordinate σ l j)) =
        exprStack D σ (k,l) i j := congrFun (congrFun (congrFun (aC_expandTot D σ) (k,l)) i) j
    simp only [ha, mul_sub, Finset.sum_sub_distrib, hh, sub_self]
  simp only [rowCoeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro σ _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l _
  calc
    _ = (piAt c k.val * c.1 i * sectorScale c σ * legScale c l) *
        (∑ j, (expandTot D).1 (some (.L1 k i), some (.ZeroCoordinate σ l j)) * (r' j - r j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hs, mul_zero]

end Praxis.Proofs.View.Locus
