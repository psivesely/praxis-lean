import Praxis.Relation
import Mathlib.RingTheory.AdjoinRoot
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat dot Gate Sat MomentGate)

abbrev KPoly (V : Type*) (n : ℕ) : Type _ := Fin n → V

def kcoeff {V : Type*} [Zero V] {n : ℕ} (a : KPoly V n) (k : ℕ) : V :=
  if h : k < n then a ⟨k, h⟩ else 0

def rawMul {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] {n : ℕ}
    (a : KPoly R n) (b : KPoly V n) : ℕ → V :=
  fun t => ∑ i : Fin n, ∑ j : Fin n, if i.val + j.val = t then a i • b j else 0

def reduceP {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] (n : ℕ) (c0 : R)
    (p : ℕ → V) : KPoly V n :=
  fun e => p e.val + c0 • p (e.val + n)

def quotP {V : Type*} (n : ℕ) (p : ℕ → V) : ℕ → V := fun e => p (e + n)

def frob {R V : Type*} [Monoid R] [MulAction R V] {n : ℕ} (β : R) (s : ℕ) (a : KPoly V n) :
    KPoly V n :=
  fun e => (β ^ (s * e.val)) • a e

section Params

variable (P : Params)

def c0F : Fq P := (P.c0 : Fq P)

def betaF : Fq P := (P.beta : Fq P)

noncomputable def KummerPoly : Polynomial (Fq P) :=
  Polynomial.X ^ P.n - Polynomial.C (c0F P)

abbrev KummerField : Type := AdjoinRoot (KummerPoly P)

def KummerIrreducible : Prop := Irreducible (KummerPoly P)

def BetaLaws : Prop :=
  betaF P = c0F P ^ ((P.q - 1) / P.n) ∧ orderOf (betaF P) = P.n ∧ betaF P ^ P.m = -1

def kmul {V : Type*} [AddCommMonoid V] [Module (Fq P) V] (a : KPoly (Fq P) P.n)
    (b : KPoly V P.n) : KPoly V P.n :=
  reduceP P.n (c0F P) (rawMul a b)

def sigma {V : Type*} [MulAction (Fq P) V] (s : ℕ) (a : KPoly V P.n) : KPoly V P.n :=
  frob (betaF P) s a

variable {P}

def zOf (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) : KPoly (Fq P) P.n :=
  fun e => dot (v e) x

def lam (v : Fin P.n → Vec (Fq P) P.N) (s : Fq P) : Vec (Fq P) P.N :=
  ∑ e, s ^ e.val • v e

def Uw (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) (k : ℕ) : Fq P :=
  kcoeff (kmul P (zOf v x) (sigma P (P.m - 1) (zOf v x))) k

def Vw (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) (j : ℕ) : Fq P :=
  kcoeff (kmul P (zOf v x) (sigma P P.m (zOf v x))) (2 * j)

end Params

end Praxis
