import Praxis.Grid
import Mathlib.Data.Matrix.Mul
import Praxis.Kummer
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat dot Gate Sat MomentGate)

variable (P : Params)

abbrev Stack : Type := Cell P → Mat (Fq P) P.N

variable {P}

def stackU (W : Stack P) (k : ℕ) : Mat (Fq P) P.N :=
  ∑ c ∈ Finset.univ.filter (fun c : Cell P => IsUCell c ∧ cellExp c = k), W c

def stackV (W : Stack P) (j : ℕ) : Mat (Fq P) P.N :=
  ∑ c ∈ Finset.univ.filter (fun c : Cell P => ¬ IsUCell c ∧ cellExp c = 2 * j), W c

def polyU (W : Stack P) : KPoly (Mat (Fq P) P.N) P.n := fun k => stackU W k.val

def polyV (W : Stack P) : KPoly (Mat (Fq P) P.N) P.n :=
  fun k => if k.val % 2 = 0 then stackV W (k.val / 2) else 0

def rawMulMV {N n : ℕ} {F : Type*} [CommSemiring F] (A : KPoly (Mat F N) n) (b : KPoly (Vec F N) n) :
    ℕ → Vec F N :=
  fun t => ∑ i : Fin n, ∑ j : Fin n, if i.val + j.val = t then (A i).mulVec (b j) else 0

def tiePoly (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) : TieIdx → ℕ → Vec (Fq P) P.N
  | .t1 => rawMulMV (polyU W) (sigma P P.m v) - rawMulMV (polyV W) (sigma P (P.m - 1) v)
  | .t2 => rawMulMV (polyU W) (sigma P (P.m + 1) v) -
      rawMulMV (sigma P (P.m + 1) (polyU W)) (sigma P (P.m - 1) v)
  | .t3 => rawMulMV (polyV W) (sigma P (P.m + 1) v) -
      rawMulMV (sigma P (P.m + 1) (polyU W)) (sigma P P.m v)

def Ties (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) : Prop :=
  ∀ s, reduceP P.n (c0F P) (tiePoly v W s) = 0

def tieQuot (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (s : TieIdx) : ℕ → Vec (Fq P) P.N :=
  quotP P.n (tiePoly v W s)

def honestStack (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) : Stack P :=
  fun c => weight v x c • Matrix.vecMulVec x x

def PassingStack [Fact (Nat.Prime P.q)] (S : Relation P) (v : Fin P.n → Vec (Fq P) P.N)
    (W : Stack P) : Prop :=
  (∀ c, Passes S (W c)) ∧ Ties v W

def keyCoeff (W : Stack P) : Fq P :=
  ∑ c ∈ Finset.univ.filter (fun c : Cell P => IsKeyCell c), W c 0 0

end Praxis
