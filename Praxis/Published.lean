import Praxis.Keys
import Mathlib.Data.List.FinRange
import Praxis.Grid
import Praxis.Params

namespace Praxis

inductive Sector
  | plain
  | alpha
  deriving DecidableEq, Repr

instance : Fintype Sector where
  elems := {.plain, .alpha}
  complete := fun x => by cases x <;> simp

inductive CrossIdx
  | c1eps
  | c2eps
  | c3eps
  | c2div
  | c3div
  deriving DecidableEq, Repr

instance : Fintype CrossIdx where
  elems := {.c1eps, .c2eps, .c3eps, .c2div, .c3div}
  complete := fun x => by cases x <;> simp

variable (P : Params)

abbrev RemExp : Type := {s : Fin (P.U * P.E1p) // ¬ P.U ∣ s.val}

inductive G1Idx
  | L1 (k1 : Fin P.K1) (i : Fin (P.N + 1))
  | L2 (k1 : Fin P.K1) (i : Fin (P.N + 1))
  | totL1 (k1 : Fin P.K1)
  | totL2 (k1 : Fin P.K1)
  | QP (s : Fin P.E1)
  | RP (s : RemExp P)
  | GY (i : Fin (P.N + 1))
  deriving DecidableEq

inductive G2Idx
  | ZeroCoordinate (σ : Sector) (leg : Leg P) (j : Fin (P.N + 1))
  | R2 (σ : Sector) (leg : Leg P) (j : Fin (P.N + 1))
  | totR1 (σ : Sector) (leg : Leg P)
  | totR2 (σ : Sector) (leg : Leg P)
  | QB (σ : Sector) (c : Cell P) (j : Fin P.Mq)
  | RB (σ : Sector) (c : Cell P) (j : Fin P.Wr)
  | SC (σ : Sector) (leg : Leg P)
  | GB (σ : Sector) (g : CrossIdx) (e : Fin (2 * P.n - 1))
  | GM (σ : Sector) (s : TieIdx) (e : Fin (P.n - 1))
  deriving DecidableEq

def legList : List (Leg P) :=
  [LegKind.E, LegKind.O, LegKind.V].flatMap fun X => (List.finRange P.K2).map fun k2 => (X, k2)

def cellList : List (Cell P) :=
  (List.finRange P.K1).flatMap fun k1 => (legList P).map fun l => (k1, l)

def g1Order : List (G1Idx P) :=
  ((List.finRange P.K1).flatMap fun k1 => (List.finRange (P.N + 1)).map (G1Idx.L1 k1)) ++
  ((List.finRange P.K1).flatMap fun k1 => (List.finRange (P.N + 1)).map (G1Idx.L2 k1)) ++
  (List.finRange P.K1).map G1Idx.totL1 ++ (List.finRange P.K1).map G1Idx.totL2 ++
  (List.finRange P.E1).map G1Idx.QP ++
  ((List.finRange (P.U * P.E1p)).filterMap fun s =>
    if h : P.U ∣ s.val then none else some (G1Idx.RP ⟨s, h⟩)) ++
  (List.finRange (P.N + 1)).map G1Idx.GY

def g2OrderSector (σ : Sector) : List (G2Idx P) :=
  ((legList P).flatMap fun l => (List.finRange (P.N + 1)).map (G2Idx.ZeroCoordinate σ l)) ++
  ((legList P).flatMap fun l => (List.finRange (P.N + 1)).map (G2Idx.R2 σ l)) ++
  (legList P).map (G2Idx.totR1 σ) ++ (legList P).map (G2Idx.totR2 σ) ++
  ((cellList P).flatMap fun c => (List.finRange P.Mq).map (G2Idx.QB σ c)) ++
  ((cellList P).flatMap fun c => (List.finRange P.Wr).map (G2Idx.RB σ c)) ++
  (legList P).map (G2Idx.SC σ) ++
  ([CrossIdx.c1eps, .c2eps, .c3eps, .c2div, .c3div].flatMap fun g =>
    (List.finRange (2 * P.n - 1)).map (G2Idx.GB σ g)) ++
  ([TieIdx.t1, .t2, .t3].flatMap fun s => (List.finRange (P.n - 1)).map (G2Idx.GM σ s))

def g2Order : List (G2Idx P) := g2OrderSector P .plain ++ g2OrderSector P .alpha

def legCount : ℕ := Fintype.card LegKind * P.K2

def cellCount : ℕ := P.K1 * legCount P

def countG1 : ℕ :=
  2 * P.K1 * (P.N + 1) + 2 * P.K1 + P.E1 + (P.U - 1) * P.E1p + (P.N + 1)

def countG2 : ℕ :=
  2 * 2 * legCount P * (P.N + 1) + 2 * 2 * legCount P + 2 * cellCount P * P.Mq +
    2 * cellCount P * P.Wr + 2 * legCount P + 2 * Fintype.card CrossIdx * (2 * P.n - 1) +
    2 * Fintype.card TieIdx * (P.n - 1)

end Praxis
