import Praxis.Proofs.View.SZ.Grid
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View.SZ

open Praxis.Algebra (Vec)

open MvPolynomial

noncomputable section

abbrev Poly := MvPolynomial (CoinVar P0) (Fq P0)

def xs (s : ScalarCoin) : Poly := X (.inr s)

def xy (i : Fin (P0.N + 1)) : Poly := X (.inl i)

def tauP (p : Polynomial (Fq P0)) : Poly := p.eval₂ C (xs .tau)

def lamP (v : Fin P0.n → Vec (Fq P0) P0.N) (x : Poly)
    (j : Fin (P0.N + 1)) : Poly := ∑ e, C (v e j) * x ^ e.val

def piP (k : ℕ) : Poly :=
  xs .pi * xs .u ^ (2 * k) * (1 + xs .eps * C (betaF P0 ^ (2 * k)))

def bP : LegKind → Poly
  | .E => xs .bE
  | .O => xs .bO
  | .V => xs .bV

def legP (l : Leg P0) : Poly := bP l.1 * xs .u ^ legExp l

def gammaP (cl : Cell P0) : Poly := piP cl.1.val * legP cl.2

def sectorP : Sector → Poly
  | .plain => 1
  | .alpha => xs .alpha

def denomP : Poly := xs .Om22 * xs .zeta * xs .zeta' * xs .zeta4 * xs .eps

def maskP (v : Fin P0.n → Vec (Fq P0) P0.N) (l : Leg P0)
    (j : Fin (P0.N + 1)) : Poly :=
  let u := xs .u
  let bu := C (-betaF P0) * u
  match l.1 with
  | .V => xs .eps * u ^ legExp l *
      (xs .c3 * lamP v bu j - xs .c1 * lamP v (C (betaF P0 ^ (P0.m - 1)) * u) j)
  | _ => xs .eps * u ^ legExp l *
      (xs .c1 * lamP v (-u) j + xs .c2 * lamP v bu j) -
      bu ^ legExp l *
      (xs .c2 * lamP v (C (betaF P0 ^ (P0.m - 1)) * u) j + xs .c3 * lamP v (-u) j)

def e1P (pp : PublicParams P0) : Option (G1Idx P0) → Poly
  | none => 1
  | some (.L1 k i) => piP k.val * xy i
  | some (.L2 k i) => piP k.val * (xs .Om12 * xy i + xs .Om22 * tauP (pp.qap.A i))
  | some (.totL1 k) => ∑ i, piP k.val * xy i
  | some (.totL2 k) => ∑ i, piP k.val * (xs .Om12 * xy i + xs .Om22 * tauP (pp.qap.A i))
  | some (.QP s) => xs .zeta * xs .tau ^ s.val
  | some (.RP s) => xs .zeta' * xs .tau ^ s.1.val
  | some (.GY i) => xs .zeta4 * xy i

def r1P (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (l : Leg P0) (j : Fin (P0.N + 1)) : Poly :=
  xs .zeta * xs .zeta' * xs .zeta4 *
    (xs .Om22 * xs .eps * legP l * (C (r j) + tauP (pp.qap.A j)) +
      xs .Om22 * maskP v l j - xs .Om12 * xs .eps * legP l * (tauP (pp.qap.B j) - xy j))

def r2P (pp : PublicParams P0) (l : Leg P0) (j : Fin (P0.N + 1)) : Poly :=
  xs .zeta * xs .zeta' * xs .zeta4 * xs .eps * legP l * (tauP (pp.qap.B j) - xy j)

def crossP : CrossIdx → Poly
  | .c1eps => xs .c1 * xs .eps ^ 2
  | .c2eps => xs .c2 * xs .eps ^ 2
  | .c3eps => xs .c3 * xs .eps ^ 2
  | .c2div => xs .c2
  | .c3div => xs .c3

def tieP : TieIdx → Poly
  | .t1 => xs .c1
  | .t2 => xs .c2
  | .t3 => xs .c3

def e2P (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) : Option (G2Idx P0) → Poly
  | none => denomP
  | some (.ZeroCoordinate σ l j) => sectorP σ * r1P pp v r l j
  | some (.R2 σ l j) => sectorP σ * r2P pp l j
  | some (.totR1 σ l) => sectorP σ * ∑ j, r1P pp v r l j
  | some (.totR2 σ l) => sectorP σ * ∑ j, r2P pp l j
  | some (.QB σ cl j) => sectorP σ * xs .Om22 * xs .zeta' * xs .zeta4 * xs .eps *
      gammaP cl * tauP (pp.qap.zCell cl) * xs .tau ^ (P0.E1 * j.val)
  | some (.RB σ cl j) => sectorP σ * xs .Om22 * xs .zeta * xs .zeta4 * xs .eps *
      gammaP cl * tauP pp.qap.Z0 * xs .tau ^ (P0.U * P0.E1p * j.val)
  | some (.SC σ l) => sectorP σ * denomP * legP l
  | some (.GB σ g e) => sectorP σ * xs .Om22 * xs .zeta * xs .zeta' *
      xs .pi * crossP g * xs .u ^ e.val
  | some (.GM σ s e) => sectorP σ * xs .Om22 * xs .zeta * xs .zeta' * xs .eps *
      xs .pi * tieP s * (xs .u ^ P0.n - C (c0F P0)) * xs .u ^ e.val

def kappaP (pp : PublicParams P0) : Poly := piP 0 * xs .bE * tauP pp.qap.Lrho

def differenceP (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0) : Poly :=
  ((keys1 P0).map fun a => ((keys2 P0).map fun b =>
    C (D.1 (a, b)) * (e1P pp a * e2P pp v r b)).sum).sum +
    C D.2 * denomP * xs .alpha * kappaP pp - C ι * denomP * kappaP pp

end

end Praxis.Proofs.View.SZ
