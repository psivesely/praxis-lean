import Praxis.QAP
import Mathlib.LinearAlgebra.Lagrange
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Stack

namespace Praxis

open Praxis.Algebra (Vec e0)

open Polynomial

variable (P : Params)

structure RowPoints where

  colPt : Fin (P.N + 1) → Fq P

  rho : Fq P

  delta : Fin P.gatesMax → Fq P

  mu : Fq P

  place : Fin P.gatesMax → (Fin P.U ≃ Option (Fin P.productsMax))

variable {P}

namespace RowPoints

variable (pts : RowPoints P)

def gatePoint (t : Fin P.gatesMax) (j : Fin P.U) : Fq P := pts.delta t * pts.mu ^ j.val

def point : QAPIndex P → Fq P
  | .inl i => pts.colPt i
  | .inr (.inl _) => pts.rho
  | .inr (.inr tj) => pts.gatePoint tj.1 tj.2

structure Admissible : Prop where
  mu_order : orderOf pts.mu = P.U
  cosets_distinct : Function.Injective fun t => pts.delta t ^ P.U
  distinct : Function.Injective pts.point

noncomputable def Z0 : Polynomial (Fq P) := z0Poly pts.colPt pts.rho

noncomputable def Z : Polynomial (Fq P) := zPoly (Finset.univ.image pts.point) pts.rho

variable [Fact (Nat.Prime P.q)]

noncomputable def interp (r : QAPIndex P → Fq P) : Polynomial (Fq P) :=
  Lagrange.interpolate Finset.univ pts.point r

noncomputable def aVal (S : Relation P) (i : Fin (P.N + 1)) : QAPIndex P → Fq P
  | .inl j => if j = 0 then 0 else if i = j then 1 else if i = 0 then -1 else 0
  | .inr (.inl _) => e0 i
  | .inr (.inr tj) =>
    (gateVals (pts.place tj.1) S tj.1 (pts.Z0.eval (pts.gatePoint tj.1 tj.2)) tj.2 i).1

noncomputable def bVal (S : Relation P) (i : Fin (P.N + 1)) : QAPIndex P → Fq P
  | .inl j => if i = j then 1 else 0
  | .inr (.inl _) => e0 i
  | .inr (.inr tj) =>
    (gateVals (pts.place tj.1) S tj.1 (pts.Z0.eval (pts.gatePoint tj.1 tj.2)) tj.2 i).2

noncomputable def toQAP (S : Relation P) : QAPData P where
  colPt := pts.colPt
  rho := pts.rho
  delta := pts.delta
  mu := pts.mu
  place := pts.place
  A := fun i => pts.interp (pts.aVal S i)
  B := fun i => pts.interp (pts.bVal S i)
  Z0 := pts.Z0
  Z := pts.Z
  Lrho := pts.interp fun k => if k = rhoIndex then 1 else 0

end RowPoints

variable (P) in

def AdmissibleChoice : Type := {pts : RowPoints P // pts.Admissible}

noncomputable def domainMap [Fact (Nat.Prime P.q)] (ch : AdmissibleChoice P) : DomainMap P :=
  fun S => ch.1.toQAP S

end Praxis
