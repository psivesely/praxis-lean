import Praxis.Kummer
import Praxis.Algebra.Definitions.MSIS
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat dot Gate Sat MomentGate MSISRing RingMatrix MSISAlgorithm msisSuccess)

variable (P : Params)

abbrev Rq : Type := Fin P.d → Fq P

variable {P}

def rqCoeff (a : Rq P) (i : ℕ) : Fq P := if h : i < P.d then a ⟨i, h⟩ else 0

def rqMul (a b : Rq P) : Rq P := fun i =>
  ∑ j : Fin P.d, ∑ k : Fin P.d,
    if j.val + k.val = i.val then a j * b k
    else if j.val + k.val = i.val + P.d then -(a j * b k) else 0

variable (P)

abbrev FormIndex : Type := Fin P.rows × Option (Fin P.cols)

abbrev FormMatrix : Type := FormIndex P → Rq P

abbrev Seed : Type := BitVec P.seedBits

abbrev FormOracle : Type := Seed P → FormIndex P → Rq P

variable {P}

def formsAt (HF : FormOracle P) (seed : Seed P) : FormMatrix P := HF seed

def slotPoly (x : Vec (Fq P) P.N) (j : Fin P.cols) : Rq P := fun s =>
  if h : 1 + P.d * j.val + s.val < P.N + 1 then x ⟨1 + P.d * j.val + s.val, h⟩ else 0

def phi (A : FormMatrix P) (e : Fin P.n) (x : Vec (Fq P) P.N) : Fq P :=
  if e.val / P.d = 0 then (if e.val % P.d = 0 then x 0 else 0)
  else if h : e.val / P.d - 1 < P.rows then
    x 0 * rqCoeff (A (⟨e.val / P.d - 1, h⟩, none)) (e.val % P.d) +
      ∑ j : Fin P.cols,
        rqCoeff (rqMul (A (⟨e.val / P.d - 1, h⟩, some j)) (slotPoly x j)) (e.val % P.d)
  else 0

def formVec (A : FormMatrix P) (e : Fin P.n) : Vec (Fq P) P.N :=
  fun c => phi A e (Pi.single c 1)

variable (P)

noncomputable def msisRing [Fact (1 < P.q)] (hd : P.d ≠ 0) : MSISRing P.q P.d where
  Phi := Polynomial.X ^ P.d + Polynomial.C 1
  monic := Polynomial.monic_X_pow_add_C 1 hd
  natDegree_eq := Polynomial.natDegree_X_pow_add_C

abbrev MSISChallenge [Fact (1 < P.q)] (hd : P.d ≠ 0) : Type :=
  RingMatrix (msisRing P hd) P.rows P.cols

noncomputable def formsOfChallenge [Fact (1 < P.q)] (hd : P.d ≠ 0) (A : MSISChallenge P hd)
    (aStar : Fin P.rows → Rq P) : FormMatrix P
  | (ρ, none) => aStar ρ
  | (ρ, some j) => fun i => (msisRing P hd).coords (A ρ j)
      (Fin.cast (msisRing P hd).natDegree_eq.symm i)

end Praxis
