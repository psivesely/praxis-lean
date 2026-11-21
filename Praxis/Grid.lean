import Praxis.Forms
import Mathlib.Data.Fintype.Basic
import Praxis.Kummer
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat dot Gate Sat MomentGate)

inductive LegKind
  | E
  | O
  | V
  deriving DecidableEq, Repr

instance : Fintype LegKind where
  elems := {.E, .O, .V}
  complete := fun x => by cases x <;> simp

def LegKind.base : LegKind → ℕ
  | .E => 0
  | .O => 1
  | .V => 0

inductive TieIdx
  | t1
  | t2
  | t3
  deriving DecidableEq, Repr

instance : Fintype TieIdx where
  elems := {.t1, .t2, .t3}
  complete := fun x => by cases x <;> simp

variable (P : Params)

abbrev Leg : Type := LegKind × Fin P.K2

abbrev Cell : Type := Fin P.K1 × Leg P

variable {P}

def legExp (l : Leg P) : ℕ := l.1.base + 2 * P.K1 * l.2.val

def cellExp (c : Cell P) : ℕ := 2 * c.1.val + legExp c.2

def IsUCell (c : Cell P) : Prop := c.2.1 ≠ .V

instance (c : Cell P) : Decidable (IsUCell c) := by unfold IsUCell; infer_instance

def IsKeyCell (c : Cell P) : Prop := c.1.val = 0 ∧ c.2.1 = .E ∧ c.2.2.val = 0

instance (c : Cell P) : Decidable (IsKeyCell c) := by unfold IsKeyCell; infer_instance

def keyCell [NeZero P.K1] [NeZero P.K2] : Cell P := (0, (.E, 0))

def cellWeight {F : Type*} (wU wV : ℕ → F) (c : Cell P) : F :=
  if c.2.1 = .V then wV (cellExp c / 2) else wU (cellExp c)

def weight (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) (c : Cell P) : Fq P :=
  cellWeight (Uw v x) (Vw v x) c

def wKey (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) : Fq P := Uw v x 0

end Praxis
