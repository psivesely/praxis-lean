import Praxis.Published
import VCVio.OracleComp.Constructions.SampleableType
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Kummer
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat dot)

open Polynomial

variable (P : Params)

structure PublicParams where
  S : Relation P
  qap : QAPData P

variable {P}

def setup (dom : DomainMap P) (S : Relation P) : PublicParams P := ⟨S, dom S⟩

inductive ScalarCoin
  | tau | Om12 | Om22 | zeta | zeta' | zeta4 | pi | bE | bO | bV | c1 | c2 | c3 | u | alpha | eps
  deriving DecidableEq, Repr

instance : Fintype ScalarCoin where
  elems := {.tau, .Om12, .Om22, .zeta, .zeta', .zeta4, .pi, .bE, .bO, .bV, .c1, .c2, .c3, .u,
    .alpha, .eps}
  complete := fun x => by cases x <;> simp

def ScalarCoin.inUnits : ScalarCoin → Bool
  | .tau | .Om12 | .eps => false
  | _ => true

variable (P)

abbrev Coins : Type := Vec (Fq P) P.N × SearchSample P × (ScalarCoin → Fq P)

variable {P}

def ValidCoins (Dm : QAPData P) (c : Coins P) : Prop :=
  (∀ k, c.2.2 .tau ≠ Dm.point k) ∧ (∀ s, s.inUnits = true → c.2.2 s ≠ 0) ∧
    c.2.2 .eps ≠ 0 ∧ ∀ k1 : Fin P.K1, c.2.2 .eps ≠ -(betaF P ^ (2 * k1.val))⁻¹

instance (Dm : QAPData P) (c : Coins P) : Decidable (ValidCoins Dm c) := by
  unfold ValidCoins; infer_instance

section Derived

variable [Fact (Nat.Prime P.q)] (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N) (c : Coins P)

def coin (s : ScalarCoin) : Fq P := c.2.2 s

def thetaAt (k1 : ℕ) : Fq P := betaF P ^ (2 * k1)

def piAt (k1 : ℕ) : Fq P :=
  coin c .pi * coin c .u ^ (2 * k1) * (1 + coin c .eps * thetaAt k1)

def bOf : LegKind → Fq P
  | .E => coin c .bE
  | .O => coin c .bO
  | .V => coin c .bV

def legScaleAt (X : LegKind) (k2 : ℕ) : Fq P :=
  bOf c X * coin c .u ^ (X.base + 2 * P.K1 * k2)

def legScale (l : Leg P) : Fq P := legScaleAt c l.1 l.2.val

def gamma (cl : Cell P) : Fq P := piAt c cl.1.val * legScale c cl.2

def gammaKey : Fq P := piAt c 0 * legScaleAt c .E 0

def legMask (l : Leg P) : Vec (Fq P) P.N :=
  let u := coin c .u
  let b' := -betaF P
  let L := lam v
  let x := legExp l
  match l.1 with
  | .V => u ^ x • (coin c .c3 • L (b' * u) - coin c .c1 • L (betaF P ^ (P.m - 1) * u))
  | _ => u ^ x • (coin c .c1 • L (-u) + coin c .c2 • L (b' * u)) -
      ((coin c .eps)⁻¹ * (b' * u) ^ x) •
        (coin c .c2 • L (betaF P ^ (P.m - 1) * u) + coin c .c3 • L (-u))

def H1 (l : Leg P) (j : Fin (P.N + 1)) : Fq P :=
  legScale c l * (rField c.2.1 j + (pp.qap.A j).eval (coin c .tau)) + legMask v c l j

def H2 (l : Leg P) (j : Fin (P.N + 1)) : Fq P :=
  legScale c l * ((pp.qap.B j).eval (coin c .tau) - c.1 j)

def kappa : Fq P := gammaKey c * pp.qap.Lrho.eval (coin c .tau)

def sectorScale : Sector → Fq P
  | .plain => 1
  | .alpha => coin c .alpha

def crossVal : CrossIdx → Fq P
  | .c1eps => coin c .c1 * coin c .eps
  | .c2eps => coin c .c2 * coin c .eps
  | .c3eps => coin c .c3 * coin c .eps
  | .c2div => coin c .c2 / coin c .eps
  | .c3div => coin c .c3 / coin c .eps

def cTie : TieIdx → Fq P
  | .t1 => coin c .c1
  | .t2 => coin c .c2
  | .t3 => coin c .c3

def kummerAtU : Fq P := coin c .u ^ P.n - c0F P

def g1Exp : G1Idx P → Fq P
  | .L1 k1 i => piAt c k1.val * c.1 i
  | .L2 k1 i => piAt c k1.val * (coin c .Om12 * c.1 i +
      coin c .Om22 * (pp.qap.A i).eval (coin c .tau))
  | .totL1 k1 => ∑ i, piAt c k1.val * c.1 i
  | .totL2 k1 => ∑ i, piAt c k1.val * (coin c .Om12 * c.1 i +
      coin c .Om22 * (pp.qap.A i).eval (coin c .tau))
  | .QP s => coin c .zeta * coin c .tau ^ s.val
  | .RP s => coin c .zeta' * coin c .tau ^ s.1.val
  | .GY i => coin c .zeta4 * c.1 i

def r1Exp (l : Leg P) (j : Fin (P.N + 1)) : Fq P :=
  H1 pp v c l j - coin c .Om12 / coin c .Om22 * H2 pp c l j

def r2Exp (l : Leg P) (j : Fin (P.N + 1)) : Fq P := H2 pp c l j / coin c .Om22

noncomputable def g2Exp : G2Idx P → Fq P
  | .ZeroCoordinate σ l j => sectorScale c σ * r1Exp pp v c l j
  | .R2 σ l j => sectorScale c σ * r2Exp pp c l j
  | .totR1 σ l => sectorScale c σ * ∑ j, r1Exp pp v c l j
  | .totR2 σ l => sectorScale c σ * ∑ j, r2Exp pp c l j
  | .QB σ cl j => sectorScale c σ * (gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) *
      coin c .tau ^ (P.E1 * j.val) / coin c .zeta)
  | .RB σ cl j => sectorScale c σ * (gamma c cl * pp.qap.Z0.eval (coin c .tau) *
      coin c .tau ^ (P.U * P.E1p * j.val) / coin c .zeta')
  | .SC σ l => sectorScale c σ * legScale c l
  | .GB σ g e => sectorScale c σ * (coin c .pi * crossVal c g * coin c .u ^ e.val / coin c .zeta4)
  | .GM σ s e => sectorScale c σ *
      (coin c .pi * cTie c s * kummerAtU c * coin c .u ^ e.val / coin c .zeta4)

def gtExp : Fq P := coin c .alpha * kappa pp c

end Derived

structure Ciphertext (B : BilinearGroups P.q) where
  g1 : G1Idx P → B.G1
  g2 : G2Idx P → B.G2

  gT : B.GT
  header : Header P

def formsOf (HF : FormOracle P) (seed : Seed P) : Fin P.n → Vec (Fq P) P.N :=
  formVec (formsAt HF seed)

noncomputable def encrypt [Fact (Nat.Prime P.q)] (B : BilinearGroups P.q) (HF : FormOracle P) (kdf : KDF P)
    (name : B.GT → ClassName P) (pp : PublicParams P) (m : Msg P) (seed : Seed P)
    (c : Coins P) : Ciphertext B :=
  let v := formsOf HF seed
  { g1 := fun i => B.enc1 (g1Exp pp c i)
    g2 := fun i => B.enc2 (g2Exp pp v c i)
    gT := B.encT (gtExp pp c)
    header := ⟨seed, maskMsg kdf (name (B.encT (kappa pp c))) m⟩ }

noncomputable def Enc [Fact (Nat.Prime P.q)] (B : BilinearGroups P.q) (HF : FormOracle P) (kdf : KDF P)
    (name : B.GT → ClassName P) (pp : PublicParams P) (m : Msg P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] : ProbComp (Ciphertext B) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  do
    let seed ← $ᵗ (Seed P)
    let c ← $ᵗ {c : Coins P // ValidCoins pp.qap c}
    pure (encrypt B HF kdf name pp m seed c.1)

end Praxis
