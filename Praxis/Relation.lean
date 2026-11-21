import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Praxis.Params

namespace Praxis

open Praxis.Algebra (Vec Mat dot Gate Sat MomentGate)

abbrev Relation (P : Params) : Type := Algebra.Relation (Fq P) P.N P.gatesMax

def InShape (P : Params) (S : Relation P) : Prop :=
  ∀ t, (S t).products ≤ P.productsMax

abbrev IsWitness {P : Params} [Fact (Nat.Prime P.q)] (S : Relation P) (x : Vec (Fq P) P.N) : Prop := Sat S x

instance {P : Params} [Fact (Nat.Prime P.q)] (S : Relation P) (x : Vec (Fq P) P.N) :
    Decidable (Sat S x) := by
  unfold Sat; infer_instance

def formNonzeros {F : Type*} [Zero F] [DecidableEq F] {N : ℕ} (v : Vec F N) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

def size {P : Params} [DecidableEq (Fq P)] (S : Relation P) : ℕ :=
  (∑ t, ((∑ f, (formNonzeros ((S t).left f) + formNonzeros ((S t).right f))) +
      formNonzeros (S t).linear)) +
    (∑ t, (2 * (S t).products + 1)) + (∑ t, (S t).products) + P.gatesMax

abbrev SparseForm (P : Params) : Type := List (Fin (P.N + 1) × Fq P)

structure SparseGate (P : Params) where
  products : ℕ
  left : Fin products → SparseForm P
  right : Fin products → SparseForm P
  linear : SparseForm P

abbrev SparseRelation (P : Params) : Type := Fin P.gatesMax → SparseGate P

def sparseForm {P : Params} (a : Vec (Fq P) P.N) : SparseForm P :=
  (List.finRange (P.N + 1)).filterMap fun i => if a i = 0 then none else some (i, a i)

def sparseOf {P : Params} (S : Relation P) : SparseRelation P := fun t =>
  { products := (S t).products
    left := fun f => sparseForm ((S t).left f)
    right := fun f => sparseForm ((S t).right f)
    linear := sparseForm (S t).linear }

def Passes {P : Params} [Fact (Nat.Prime P.q)] (S : Relation P) (W : Mat (Fq P) P.N) : Prop :=
  W.IsSymm ∧ (∀ j : Fin P.N, W j.succ j.succ = W 0 j.succ) ∧ ∀ t, MomentGate (S t) W = 0

end Praxis
