import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Kummer
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat dot)

open Polynomial

variable (P : Params)

structure CombCoeffs where

  W : Stack P

  sc : Cell P → Vec (Fq P) P.N

  h : Cell P → Polynomial (Fq P)
  R : Cell P → Polynomial (Fq P)

  Q : TieIdx → ℕ → Vec (Fq P) P.N
  X : CrossIdx → ℕ → Vec (Fq P) P.N

  key : Fq P

variable {P}

def shiftLam (v : Fin P.n → Vec (Fq P) P.N) (M : Mat (Fq P) P.N) (a : Fq P) (k e : ℕ) :
    Vec (Fq P) P.N :=
  if h : k ≤ e ∧ e - k < P.n then a ^ (e - k) • M.mulVec (v ⟨e - k, h.2⟩) else 0

def cellTheta (c : Cell P) : Fq P := betaF P ^ (2 * c.1.val)

def cellBetaLeg (c : Cell P) : Fq P := (-betaF P) ^ legExp c.2

def uCells : Finset (Cell P) := Finset.univ.filter IsUCell

def vCells : Finset (Cell P) := Finset.univ.filter fun c => ¬ IsUCell c

def crossPoly (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) : CrossIdx → ℕ → Vec (Fq P) P.N
  | .c1eps => fun e =>
      (∑ c ∈ uCells, cellTheta c • shiftLam v (W c) (-1) (cellExp c) e) -
        ∑ c ∈ vCells, cellTheta c • shiftLam v (W c) (betaF P ^ (P.m - 1)) (cellExp c) e
  | .c2eps => fun e => ∑ c ∈ uCells, cellTheta c • shiftLam v (W c) (-betaF P) (cellExp c) e
  | .c3eps => fun e => ∑ c ∈ vCells, cellTheta c • shiftLam v (W c) (-betaF P) (cellExp c) e
  | .c2div => fun e =>
      -∑ c ∈ uCells, cellBetaLeg c • shiftLam v (W c) (betaF P ^ (P.m - 1)) (cellExp c) e
  | .c3div => fun e => -∑ c ∈ uCells, cellBetaLeg c • shiftLam v (W c) (-1) (cellExp c) e

def evalComb (B : BilinearGroups P.q) (ct : Ciphertext B) (σ : Sector) (k : CombCoeffs P) :
    B.GT :=
  (∑ cl : Cell P, ∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1),
      k.W cl i j • (B.pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.ZeroCoordinate σ cl.2 j)) +
        B.pair (ct.g1 (.L2 cl.1 i)) (ct.g2 (.R2 σ cl.2 j)))) -
  (∑ cl : Cell P, ∑ i : Fin (P.N + 1), k.sc cl i • B.pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.SC σ cl.2))) -
  (∑ cl : Cell P, ∑ a : Fin P.E1, ∑ j : Fin P.Mq,
      (k.h cl).coeff (a.val + P.E1 * j.val) • B.pair (ct.g1 (.QP a)) (ct.g2 (.QB σ cl j))) -
  (∑ cl : Cell P, ∑ a : Fin (P.U * P.E1p), ∑ j : Fin P.Wr,
      if h : P.U ∣ a.val then 0 else
        (k.R cl).coeff (a.val + P.U * P.E1p * j.val) •
          B.pair (ct.g1 (.RP ⟨a, h⟩)) (ct.g2 (.RB σ cl j))) -
  (∑ s : TieIdx, ∑ e : Fin (P.n - 1), ∑ i : Fin (P.N + 1),
      k.Q s e.val i • B.pair (ct.g1 (.GY i)) (ct.g2 (.GM σ s e))) -
  (∑ g : CrossIdx, ∑ e : Fin (2 * P.n - 1), ∑ i : Fin (P.N + 1),
      k.X g e.val i • B.pair (ct.g1 (.GY i)) (ct.g2 (.GB σ g e))) -
  (match σ with
    | .plain => 0
    | .alpha => k.key • ct.gT)

noncomputable def stackComb (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (W : Stack P) : CombCoeffs P where
  W := W
  sc := fun cl => (W cl).mulVec r
  h := fun cl => (cellQuot pp.qap W cl).1
  R := fun cl => (cellQuot pp.qap W cl).2
  Q := tieQuot v W
  X := crossPoly v W
  key := keyCoeff W

noncomputable def lambdaCoeffs (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (x : Vec (Fq P) P.N) : CombCoeffs P where
  W := honestStack v x
  sc := 0
  h := fun cl => if IsKeyCell cl then C (wKey v x) * (honestQuot pp.qap x).1
    else C (weight v x cl) * (honestQuot pp.qap x).2.1
  R := fun cl => C (weight v x cl) * (honestQuot pp.qap x).2.2
  Q := tieQuot v (honestStack v x)
  X := crossPoly v (honestStack v x)
  key := 0

def psi (B : BilinearGroups P.q) (ct : Ciphertext B) (v : Fin P.n → Vec (Fq P) P.N)
    (x : Vec (Fq P) P.N) (σ : Sector) : B.GT :=
  ∑ cl : Cell P, weight v x cl •
    ∑ i : Fin (P.N + 1), x i • B.pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.SC σ cl.2))

def findT {G : Type*} [AddCommGroup G] [Module (Fq P) G] [DecidableEq G] (H' Ψ : G) :
    Option ℤ :=
  ((List.range (2 * P.tBound + 1)).map fun k => (k : ℤ) - P.tBound).find?
    fun t => decide (H' = ((t : ℤ) : Fq P) • Ψ)

noncomputable def decRef [Fact (Nat.Prime P.q)] (B : BilinearGroups P.q) (HF : FormOracle P)
    (kdf : KDF P) (name : B.GT → ClassName P) (pp : PublicParams P)
    (ct : Ciphertext B) (x : Vec (Fq P) P.N) : Option (Msg P) :=

  let v := formsOf HF ct.header.seed
  let wk := wKey v x
  if wk = 0 then none else

  let k := lambdaCoeffs pp v x
  let Λ0 := evalComb B ct .plain k
  let Λ1 := evalComb B ct .alpha k
  let Ψ0 := psi B ct v x .plain
  let Ψ1 := psi B ct v x .alpha
  let cx := cX (toInt x)

  let H' := Λ1 - wk • ct.gT - ((cx : ℤ) : Fq P) • Ψ1
  let t? : Option ℤ := if Ψ1 ≠ 0 then findT (P := P) H' Ψ1 else if H' = 0 then some 0 else none
  match t? with
  | none => none
  | some t =>

    let K := wk⁻¹ • (Λ0 - ((cx + t : ℤ) : Fq P) • Ψ0)
    some (maskMsg kdf (name K) ct.header.cm)

end Praxis
