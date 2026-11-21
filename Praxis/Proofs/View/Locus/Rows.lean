import Praxis.Proofs.View.Forward
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardAlgebra
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Proofs.View.ForwardSeparation
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View.Locus

open Praxis.Algebra (Vec Mat)

variable {P : Params} [Fact (Nat.Prime P.q)]

inductive RowKind | mixing | constant | linear
  deriving DecidableEq

def keepRow : RowKind → Option (G1Idx P) → Bool
  | .mixing, some (.L2 _ _) => true
  | .constant, none | .constant, some (.QP _) | .constant, some (.RP _) => true
  | .linear, some (.GY _) => true
  | _, _ => false

def rowExpr (k : RowKind) (E : ExprT P) : ExprT P :=
  (fun ab => if keepRow k ab.1 then
    match ab.2 with
    | none | some (.ZeroCoordinate _ _ _) | some (.SC _ _) => E.1 ab
    | _ => 0
   else 0, 0)

lemma rowExpr_project (k : RowKind) (D : ExprT P) :
    rowExpr k (expandTot D) =
      match k with
      | .mixing => project .omega 3 (project .pi 3 (expandTot D))
      | .constant => project .zeta4 2 (project .omega 2 (project .pi 2 (expandTot D)))
      | .linear => project .zeta4 3 (project .omega 2 (project .pi 2 (expandTot D))) := by
  apply Prod.ext
  · funext ab
    rcases ab with ⟨a,b⟩
    cases k <;> cases a with
    | none => cases b with
      | none => rfl
      | some b => cases b <;> first | rfl | simp [rowExpr, keepRow, project, restrictW,
          ViewScale.weight1, ViewScale.weight2, ViewScale.weightT,
          expandTot, expand2, expand2C, expand1, expand1C]
    | some a => cases a <;> cases b with
      | none => rfl
      | some b => cases b <;> first | rfl | simp [rowExpr, keepRow, project, restrictW,
          ViewScale.weight1, ViewScale.weight2, ViewScale.weightT,
          expandTot, expand2, expand2C, expand1, expand1C]
  · cases k <;> rfl

lemma rowExpr_identity (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0)
    (h : IdentityAtR pp v r D ι) (k : RowKind) :
    IdentityAtR pp v r (rowExpr k (expandTot D)) 0 := by
  have hE : IdentityAtR pp v r (expandTot D) ι := by
    intro c hc
    rw [valT_expandTot]
    exact h c hc
  rw [rowExpr_project]
  cases k
  · have hp := project_identity .pi (by decide) pp v r _ ι hE 3
    exact project_identity .omega (by decide) pp v r _ ι hp 3
  · have hp := project_identity .pi (by decide) pp v r _ ι hE 2
    have ho := project_identity .omega (by decide) pp v r _ 0 hp 2
    exact project_identity .zeta4 (by decide) pp v r _ 0 ho 2
  · have hp := project_identity .pi (by decide) pp v r _ ι hE 2
    have ho := project_identity .omega (by decide) pp v r _ 0 hp 2
    exact project_identity .zeta4 (by decide) pp v r _ 0 ho 3

noncomputable def rowValue (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (a : Option (G1Idx P)) : Fq P :=
  E.1 (a, none) + ∑ σ, ∑ l,
    ((∑ j, E.1 (a, some (.ZeroCoordinate σ l j)) * (sectorScale c σ * r1ExpAt pp v ⟨c,r⟩ l j)) +
      E.1 (a, some (.SC σ l)) * (sectorScale c σ * legScale c l))

def rowCoeff (E : ExprT P) (c : Coins P) (a : Option (G1Idx P)) (j : Fin (P.N+1)) : Fq P :=
  ∑ σ, ∑ l, E.1 (a, some (.ZeroCoordinate σ l j)) * (sectorScale c σ * legScale c l)

lemma rowExpr_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (k : RowKind) :
    valT pp v ⟨c,r⟩ (rowExpr k E) =
      ((keys1 P).map fun a => if keepRow k a then e1At pp ⟨c,r⟩ a * rowValue pp v r E c a else 0).sum := by
  simp only [valT, rowExpr, zero_mul, add_zero]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  by_cases ha : keepRow k a = true
  · simp only [ha, ite_true, keys2_sum, e2At, g2Exp, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add]
    simp only [rowValue, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro σ _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · ring
  · simp [ha]

lemma mixing_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) :
    valT pp v ⟨c,r⟩ (rowExpr .mixing E) =
      ∑ k, ∑ i, (piAt c k.val * (coin c .Om12 * c.1 i +
        coin c .Om22 * (pp.qap.A i).eval (coin c .tau))) *
          rowValue pp v r E c (some (.L2 k i)) := by
  simp [rowExpr_value, keys1_sum, keepRow, e1At, g1Exp]

lemma linear_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) :
    valT pp v ⟨c,r⟩ (rowExpr .linear E) =
      ∑ i, (coin c .zeta4 * c.1 i) * rowValue pp v r E c (some (.GY i)) := by
  simp [rowExpr_value, keys1_sum, keepRow, e1At, g1Exp]

lemma constant_value (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) :
    valT pp v ⟨c,r⟩ (rowExpr .constant E) = rowValue pp v r E c none +
      (∑ s, (coin c .zeta * coin c .tau ^ s.val) * rowValue pp v r E c (some (.QP s))) +
      (∑ s, (coin c .zeta' * coin c .tau ^ s.1.val) * rowValue pp v r E c (some (.RP s))) := by
  simp [rowExpr_value, keys1_sum, keepRow, e1At, g1Exp]

@[simp] lemma sectorScale_setOm12 (c : Coins P) (x : Fq P) (σ : Sector) :
    sectorScale (setCoin c .Om12 x) σ = sectorScale c σ := by cases σ <;> simp [sectorScale]

lemma r1ExpAt_Om12_neg (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (c : Coins P) (hΩ : coin c .Om22 ≠ 0)
    (l : Leg P) (j : Fin (P.N+1)) :
    r1ExpAt pp v ⟨setCoin c .Om12 (-coin c .Om22),r⟩ l j -
      r1ExpAt pp v ⟨setCoin c .Om12 0,r⟩ l j = H2 pp c l j := by
  simp [r1ExpAt, hΩ]

lemma rowValue_difference (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (a : Option (G1Idx P))
    (x : Fq P) (hR : ∀ l j, r1ExpAt pp v ⟨setCoin c .Om12 x,r⟩ l j -
      r1ExpAt pp v ⟨setCoin c .Om12 0,r⟩ l j = x / coin c .Om22 * (-H2 pp c l j)) :
    rowValue pp v r E (setCoin c .Om12 x) a -
      rowValue pp v r E (setCoin c .Om12 0) a =
      -(x / coin c .Om22) * ∑ j, rowCoeff E c a j * ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  simp only [rowValue, sectorScale_setOm12, legScale_setOm12, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, add_sub_add_right_eq_sub]
  simp_rw [← mul_sub, hR]
  simp only [rowCoeff, H2, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rowValue_plus (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (hΩ : coin c .Om22 ≠ 0)
    (a : Option (G1Idx P)) :
    rowValue pp v r E (setCoin c .Om12 (coin c .Om22)) a =
      rowValue pp v r E (setCoin c .Om12 0) a -
        ∑ j, rowCoeff E c a j * ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  have hh := rowValue_difference pp v r E c a (coin c .Om22) (by
    intro l j
    simpa [hΩ] using r1ExpAt_Om12_diff pp v r c hΩ l j)
  simp only [div_self hΩ, neg_one_mul] at hh
  linear_combination hh

lemma rowValue_minus (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (E : ExprT P) (c : Coins P) (hΩ : coin c .Om22 ≠ 0)
    (a : Option (G1Idx P)) :
    rowValue pp v r E (setCoin c .Om12 (-coin c .Om22)) a =
      rowValue pp v r E (setCoin c .Om12 0) a +
        ∑ j, rowCoeff E c a j * ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  have hh := rowValue_difference pp v r E c a (-coin c .Om22) (by
    intro l j
    simpa [hΩ] using r1ExpAt_Om12_neg pp v r c hΩ l j)
  simp [hΩ] at hh
  linear_combination hh

end Praxis.Proofs.View.Locus
