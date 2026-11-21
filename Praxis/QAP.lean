import Praxis.Stack
import Praxis.Algebra.Definitions.Stack
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.GroupTheory.OrderOfElement
import Praxis.Grid
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat e0)

open Polynomial

variable (P : Params)

structure QAPData where

  colPt : Fin (P.N + 1) → Fq P

  rho : Fq P

  delta : Fin P.gatesMax → Fq P

  mu : Fq P

  place : Fin P.gatesMax → (Fin P.U ≃ Option (Fin P.productsMax))
  A : Fin (P.N + 1) → Polynomial (Fq P)
  B : Fin (P.N + 1) → Polynomial (Fq P)
  Z0 : Polynomial (Fq P)
  Z : Polynomial (Fq P)
  Lrho : Polynomial (Fq P)

abbrev DomainMap : Type := Relation P → QAPData P

abbrev QAPIndex : Type := Fin (P.N + 1) ⊕ (Unit ⊕ (Fin P.gatesMax × Fin P.U))

variable {P}

namespace QAPData

variable (Dm : QAPData P)

def gatePoint (t : Fin P.gatesMax) (j : Fin P.U) : Fq P := Dm.delta t * Dm.mu ^ j.val

def point : QAPIndex P → Fq P
  | .inl i => Dm.colPt i
  | .inr (.inl _) => Dm.rho
  | .inr (.inr tj) => Dm.gatePoint tj.1 tj.2

def pointSet : Finset (Fq P) := Finset.univ.image Dm.point

noncomputable def zCell (c : Cell P) : Polynomial (Fq P) :=
  if IsKeyCell c then Dm.Z * (X - C Dm.rho) else Dm.Z

noncomputable def qapPoly (W : Mat (Fq P) P.N) : Polynomial (Fq P) :=
  ∑ i, ∑ j, C (W i j) * Dm.A i * Dm.B j

noncomputable def Ax (x : Vec (Fq P) P.N) : Polynomial (Fq P) := ∑ i, C (x i) * Dm.A i

noncomputable def Bx (x : Vec (Fq P) P.N) : Polynomial (Fq P) := ∑ i, C (x i) * Dm.B i

end QAPData

def rhoIndex : QAPIndex P := .inr (.inl ())

noncomputable def z0Poly (colPt : Fin (P.N + 1) → Fq P) (rho : Fq P) : Polynomial (Fq P) :=
  (X - C rho) * ∏ j, (X - C (colPt j))

noncomputable def zPoly (points : Finset (Fq P)) (rho : Fq P) : Polynomial (Fq P) :=
  ∏ p ∈ points.erase rho, (X - C p)

def gateVals (place : Fin P.U ≃ Option (Fin P.productsMax)) (S : Relation P) (t : Fin P.gatesMax)
    (z0d : Fq P) (j : Fin P.U) (i : Fin (P.N + 1)) : Fq P × Fq P :=
  match place j with
  | none => (z0d * e0 i, -(S t).linear i)
  | some f =>
    if hf : f.val < (S t).products then
      (z0d * (S t).left ⟨f.val, hf⟩ i, (S t).right ⟨f.val, hf⟩ i)
    else (0, 0)

structure ValidQAP [Fact (Nat.Prime P.q)] (Dm : QAPData P) (S : Relation P) : Prop where
  distinct : Function.Injective Dm.point
  mu_order : orderOf Dm.mu = P.U
  cosets_distinct : Function.Injective fun t => Dm.delta t ^ P.U
  Z0_eq : Dm.Z0 = z0Poly Dm.colPt Dm.rho
  Z_eq : Dm.Z = zPoly Dm.pointSet Dm.rho
  Lrho_degree : Dm.Lrho.natDegree < P.D
  Lrho_eval : ∀ k, Dm.Lrho.eval (Dm.point k) = if k = rhoIndex then 1 else 0
  A_degree : ∀ i, (Dm.A i).natDegree < P.D
  B_degree : ∀ i, (Dm.B i).natDegree < P.D
  A_col : ∀ i j, (Dm.A i).eval (Dm.colPt j) =
    if j = 0 then 0 else if i = j then 1 else if i = 0 then -1 else 0
  B_col : ∀ i j, (Dm.B i).eval (Dm.colPt j) = if i = j then 1 else 0
  A_rho : ∀ i, (Dm.A i).eval Dm.rho = e0 i
  B_rho : ∀ i, (Dm.B i).eval Dm.rho = e0 i
  A_gate : ∀ t j i, (Dm.A i).eval (Dm.gatePoint t j) =
    (gateVals (Dm.place t) S t (Dm.Z0.eval (Dm.gatePoint t j)) j i).1
  B_gate : ∀ t j i, (Dm.B i).eval (Dm.gatePoint t j) =
    (gateVals (Dm.place t) S t (Dm.Z0.eval (Dm.gatePoint t j)) j i).2

def AllowedRem (R : Polynomial (Fq P)) : Prop :=
  R.natDegree < P.U * P.gatesMax ∧ ∀ k, P.U ∣ k → R.coeff k = 0

def QAPCriterion (Dm : QAPData P) (W : Mat (Fq P) P.N) : Prop :=
  ∃ h R : Polynomial (Fq P), Dm.qapPoly W - C (W 0 0) * Dm.Lrho =
    h * (Dm.Z * (X - C Dm.rho)) + Dm.Z0 * R ∧ AllowedRem R

def CellQuotient (Dm : QAPData P) (W : Stack P) (c : Cell P) (h R : Polynomial (Fq P)) :
    Prop :=
  Dm.qapPoly (W c) - (if IsKeyCell c then C (W c 0 0) * Dm.Lrho else 0) =
      h * Dm.zCell c + Dm.Z0 * R ∧ AllowedRem R ∧ h.natDegree < P.E1 * P.Mq

open Classical in

noncomputable def cellQuot (Dm : QAPData P) (W : Stack P) (c : Cell P) :
    Polynomial (Fq P) × Polynomial (Fq P) :=
  if h : ∃ hR : Polynomial (Fq P) × Polynomial (Fq P), CellQuotient Dm W c hR.1 hR.2
  then h.choose else (0, 0)

def HonestQuotient (Dm : QAPData P) (x : Vec (Fq P) P.N)
    (hk ho R : Polynomial (Fq P)) : Prop :=
  Dm.Ax x * Dm.Bx x - Dm.Lrho = hk * (Dm.Z * (X - C Dm.rho)) + Dm.Z0 * R ∧
    Dm.Ax x * Dm.Bx x = ho * Dm.Z + Dm.Z0 * R ∧ AllowedRem R

open Classical in

noncomputable def honestQuot (Dm : QAPData P) (x : Vec (Fq P) P.N) :
    Polynomial (Fq P) × Polynomial (Fq P) × Polynomial (Fq P) :=
  if h : ∃ t : Polynomial (Fq P) × Polynomial (Fq P) × Polynomial (Fq P),
      HonestQuotient Dm x t.1 t.2.1 t.2.2
  then h.choose else (0, 0, 0)

end Praxis
