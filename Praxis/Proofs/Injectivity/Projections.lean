import Praxis.Proofs.Basic
import Praxis.Extractor
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra

variable {P : Params}

def proj1 (A : Expr1 P) : Fin P.K1 → Vec (Fq P) P.N := fun k i =>
  A (some (.L1 k i)) + A (some (.totL1 k))

def proj2 (sk : Sketches P) (B : Expr2 P) : Cell P → Fin 3 → Sector → Fq P := fun c l s =>
  ∑ j, (B (some (.ZeroCoordinate s c.2 j)) + B (some (.totR1 s c.2))) * sk c l s j

@[simp] theorem proj1_zero : proj1 (0 : Expr1 P) = 0 := by ext k i; simp [proj1]

@[simp] theorem proj1_add (A B : Expr1 P) : proj1 (A + B) = proj1 A + proj1 B := by
  ext k i; simp [proj1]; ring

@[simp] theorem proj1_smul (a : Fq P) (A : Expr1 P) : proj1 (a • A) = a • proj1 A := by
  ext k i; simp [proj1, mul_add]

@[simp] theorem proj2_zero (sk : Sketches P) : proj2 sk (0 : Expr2 P) = 0 := by
  ext c l s; simp [proj2]

@[simp] theorem proj2_add (sk : Sketches P) (A B : Expr2 P) :
    proj2 sk (A + B) = proj2 sk A + proj2 sk B := by
  ext c l s
  simp only [proj2, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _; ring

@[simp] theorem proj2_smul (sk : Sketches P) (a : Fq P) (A : Expr2 P) :
    proj2 sk (a • A) = a • proj2 sk A := by
  ext c l s
  simp only [proj2, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _; ring

@[simp] theorem exprStack_zero (s : Sector) : exprStack (0 : ExprT P) s = 0 := by
  ext c i j; simp [exprStack]

@[simp] theorem exprStack_add (D E : ExprT P) (s : Sector) :
    exprStack (D + E) s = (fun c => exprStack D s c + exprStack E s c) := by
  ext c i j; simp [exprStack]; ring

@[simp] theorem exprStack_smul (a : Fq P) (D : ExprT P) (s : Sector) :
    exprStack (a • D) s = a • exprStack D s := by
  ext c i j; simp [exprStack, mul_add]

@[simp] theorem sketches_zero (sk : Sketches P) : sketchesOf (0 : ExprT P) sk = 0 := by
  ext l s i
  simp [sketchesOf, Matrix.mulVec, dotProduct]

@[simp] theorem sketches_add (D E : ExprT P) (sk : Sketches P) :
    sketchesOf (D + E) sk = sketchesOf D sk + sketchesOf E sk := by
  ext l s i
  simp [sketchesOf, Matrix.add_mulVec, Finset.sum_add_distrib]

@[simp] theorem sketches_smul (a : Fq P) (D : ExprT P) (sk : Sketches P) :
    sketchesOf (a • D) sk = a • sketchesOf D sk := by
  ext l s i
  simp [sketchesOf, Matrix.smul_mulVec, Finset.mul_sum]

@[simp] theorem sketches_neg (D : ExprT P) (sk : Sketches P) :
    sketchesOf (-D) sk = -sketchesOf D sk := by
  simpa only [neg_one_smul] using sketches_smul (-1) D sk

@[simp] theorem sketches_sub (D E : ExprT P) (sk : Sketches P) :
    sketchesOf (D - E) sk = sketchesOf D sk - sketchesOf E sk := by
  simp [sub_eq_add_neg]

theorem sketches_pair (A : Expr1 P) (B : Expr2 P) (sk : Sketches P) :
    sketchesOf (pairExpr A B) sk =
      (fun l s => ∑ k : Fin P.K1, (∑ leg : Leg P, proj2 sk B (k, leg) l s) • proj1 A k) := by
  ext l s i
  simp only [sketchesOf, Finset.sum_apply, Matrix.mulVec, dotProduct, exprStack, pairExpr,
    proj1, proj2, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro leg _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem proj1_init (i : Option (G1Idx P)) : proj1 (Pi.single i 1) = initG1 i := by
  cases i with
  | none => ext k j; simp [proj1, initG1, Pi.single_apply]
  | some i =>
    cases i <;> ext k j <;> simp [proj1, initG1, Pi.single_apply, ite_apply, eq_comm, and_comm]
    all_goals split_ifs <;> simp_all [Pi.single_apply, ← and_assoc]

@[simp] theorem proj2_init (sk : Sketches P) (i : Option (G2Idx P)) :
    proj2 sk (Pi.single i 1) = initG2 sk i := by
  cases i with
  | none => ext c l s; simp [proj2, initG2, Pi.single_apply]
  | some i =>
    cases i <;> ext c l s <;> simp [proj2, initG2, Pi.single_apply, ite_apply, eq_comm, and_comm]
    all_goals split_ifs <;> simp_all [Pi.single_apply, ← and_assoc]
    all_goals
      symm
      apply Finset.sum_eq_zero
      intro j _
      split_ifs <;> aesop

@[simp] theorem sketches_gtInit (sk : Sketches P) (i : Option Unit) :
    sketchesOf (gtInit i) sk = 0 := by
  cases i with
  | none => ext l s j; simp [sketchesOf, exprStack, gtInit, Pi.single_apply, Matrix.mulVec, dotProduct]
  | some i => cases i; ext l s j; simp [sketchesOf, exprStack, gtInit, Matrix.mulVec, dotProduct]

theorem map_getD_zero {X Y : Type*} [Zero X] [Zero Y] (f : X → Y) (hf : f 0 = 0)
    (o : Option X) : (o.map f).getD 0 = f (o.getD 0) := by
  cases o <;> simp [hf]

theorem map_keepEarliest {X Y : Type*} (f : X → Y) (t : Label P → Option X)
    (l : Label P) (a : X) :
    (fun j => ((keepEarliest t l a) j).map f) =
      keepEarliest (fun j => (t j).map f) l (f a) := by
  unfold keepEarliest
  cases ht : t l with
  | some b => simp [ht]
  | none =>
    simp only [ht, Option.map_none]
    funext j
    by_cases hj : j = l <;> simp [hj, Function.update_of_ne]

end Praxis.Proofs.Injectivity
