import Praxis.Proofs.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open MvPolynomial

noncomputable section

variable {P : Params} [Fact (Nat.Prime P.q)]

abbrev MonVar (P : Params) := Fin (P.N + 1) ⊕ (Fin (P.N + 1) ⊕ ScalarCoin)

abbrev MonPoly (P : Params) := MvPolynomial (MonVar P) (Fq P)

def assignmentCoords (ω : Assign P) : MonVar P → Fq P
  | .inl i => ω.coins.1 i
  | .inr (.inl i) => ω.r i
  | .inr (.inr s) => coin ω.coins s

def scalarX (s : ScalarCoin) : MonPoly P := X (.inr (.inr s))

def yX (i : Fin (P.N + 1)) : MonPoly P := X (.inl i)

def univarAtTau (p : Polynomial (Fq P)) : MonPoly P :=
  p.eval₂ MvPolynomial.C (scalarX .tau)

theorem eval_univarAtTau (ω : Assign P) (p : Polynomial (Fq P)) :
    MvPolynomial.eval (assignmentCoords ω) (univarAtTau p) =
      p.eval (coin ω.coins .tau) := by
  simp only [univarAtTau, Polynomial.hom_eval₂, scalarX, MvPolynomial.eval_X]
  have h : (MvPolynomial.eval (assignmentCoords ω)).comp MvPolynomial.C = RingHom.id (Fq P) := by
    ext x
    simp
  rw [h]
  rfl

def piPoly (k : ℕ) : MonPoly P :=
  scalarX .pi * scalarX .u ^ (2 * k) *
    (1 + scalarX .eps * C (thetaAt (P := P) k))

noncomputable def leftPoly (pp : PublicParams P) : Option (G1Idx P) → MonPoly P
  | none => 1
  | some (.L1 k i) => piPoly k.val * yX i
  | some (.L2 k i) => piPoly k.val *
      (scalarX .Om12 * yX i + scalarX .Om22 * univarAtTau (pp.qap.A i))
  | some (.totL1 k) => ∑ i, piPoly k.val * yX i
  | some (.totL2 k) => ∑ i, piPoly k.val *
      (scalarX .Om12 * yX i + scalarX .Om22 * univarAtTau (pp.qap.A i))
  | some (.QP s) => scalarX .zeta * scalarX .tau ^ s.val
  | some (.RP s) => scalarX .zeta' * scalarX .tau ^ s.1.val
  | some (.GY i) => scalarX .zeta4 * yX i

theorem eval_leftPoly (pp : PublicParams P) (ω : Assign P) (a : Option (G1Idx P)) :
    MvPolynomial.eval (assignmentCoords ω) (leftPoly pp a) = e1At pp ω a := by
  cases a with
  | none => simp [leftPoly, e1At]
  | some a =>
    cases a <;> simp [leftPoly, e1At, g1Exp, piPoly, piAt, scalarX, yX,
      assignmentCoords, eval_univarAtTau]

def deltaPoly : MonPoly P :=
  scalarX .Om22 * scalarX .zeta * scalarX .zeta' * scalarX .zeta4 * scalarX .eps

def keyPoly (pp : PublicParams P) : MonPoly P :=
  deltaPoly * (piPoly 0 * scalarX .bE * univarAtTau pp.qap.Lrho)

theorem eval_keyPoly (pp : PublicParams P) (ω : Assign P) :
    MvPolynomial.eval (assignmentCoords ω) (keyPoly pp) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * kappa pp ω.coins := by
  simp [keyPoly, deltaPoly, piPoly, scalarX, assignmentCoords, eval_univarAtTau,
    kappa, gammaKey, piAt, thetaAt, legScaleAt, bOf, LegKind.base]

def legCoin : LegKind → ScalarCoin
  | .E => .bE
  | .O => .bO
  | .V => .bV

def legPoly (l : Leg P) : MonPoly P :=
  scalarX (legCoin l.1) * scalarX .u ^ (l.1.base + 2 * P.K1 * l.2.val)

def sectorPoly : Sector → MonPoly P
  | .plain => 1
  | .alpha => scalarX .alpha

def gammaPoly (c : Cell P) : MonPoly P := piPoly c.1.val * legPoly c.2

def h2Poly (pp : PublicParams P) (l : Leg P) (j : Fin (P.N + 1)) : MonPoly P :=
  legPoly l * (univarAtTau (pp.qap.B j) - yX j)

def rightR2Poly (pp : PublicParams P) (σ : Sector) (l : Leg P)
    (j : Fin (P.N + 1)) : MonPoly P :=
  sectorPoly σ * scalarX .zeta * scalarX .zeta' * scalarX .zeta4 * scalarX .eps *
    h2Poly pp l j

theorem eval_legPoly (ω : Assign P) (l : Leg P) :
    MvPolynomial.eval (assignmentCoords ω) (legPoly l) = legScale ω.coins l := by
  cases l with
  | mk kind k =>
    cases kind <;> simp [legPoly, legCoin, scalarX, assignmentCoords, legScale,
      legScaleAt, bOf]

theorem eval_sectorPoly (ω : Assign P) (σ : Sector) :
    MvPolynomial.eval (assignmentCoords ω) (sectorPoly σ) = sectorScale ω.coins σ := by
  cases σ <;> simp [sectorPoly, sectorScale, scalarX, assignmentCoords]

theorem eval_gammaPoly (ω : Assign P) (c : Cell P) :
    MvPolynomial.eval (assignmentCoords ω) (gammaPoly c) = gamma ω.coins c := by
  simp [gammaPoly, piPoly, scalarX, assignmentCoords, eval_legPoly, gamma, piAt]

theorem eval_h2Poly (pp : PublicParams P) (ω : Assign P) (l : Leg P)
    (j : Fin (P.N + 1)) :
    MvPolynomial.eval (assignmentCoords ω) (h2Poly pp l j) = H2 pp ω.coins l j := by
  simp [h2Poly, eval_legPoly, eval_univarAtTau, yX, assignmentCoords, H2]

theorem eval_rightR2Poly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (l : Leg P)
    (j : Fin (P.N + 1)) :
    MvPolynomial.eval (assignmentCoords ω) (rightR2Poly pp σ l j) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.R2 σ l j)) := by
  have h22 : coin ω.coins .Om22 ≠ 0 := h.2.1 .Om22 rfl
  simp only [rightR2Poly, map_mul, eval_sectorPoly, scalarX, MvPolynomial.eval_X,
    assignmentCoords, eval_h2Poly, e2At, g2Exp, r2Exp]
  field_simp

def rightTotR2Poly (pp : PublicParams P) (σ : Sector) (l : Leg P) : MonPoly P :=
  ∑ j, rightR2Poly pp σ l j

theorem eval_rightTotR2Poly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (l : Leg P) :
    MvPolynomial.eval (assignmentCoords ω) (rightTotR2Poly pp σ l) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.totR2 σ l)) := by
  simp only [rightTotR2Poly, map_sum, eval_rightR2Poly pp v ω h, e2At, g2Exp,
    Finset.mul_sum]

def rightSCPoly (σ : Sector) (l : Leg P) : MonPoly P :=
  deltaPoly * sectorPoly σ * legPoly l

theorem eval_rightSCPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (σ : Sector) (l : Leg P) :
    MvPolynomial.eval (assignmentCoords ω) (rightSCPoly σ l) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.SC σ l)) := by
  simp [rightSCPoly, deltaPoly, scalarX, assignmentCoords, eval_sectorPoly, eval_legPoly,
    e2At, g2Exp, mul_assoc]

def rightQBPoly (pp : PublicParams P) (σ : Sector) (c : Cell P) (t : Fin P.Mq) : MonPoly P :=
  sectorPoly σ * scalarX .Om22 * scalarX .zeta' * scalarX .zeta4 * scalarX .eps *
    gammaPoly c * univarAtTau (pp.qap.zCell c) * scalarX .tau ^ (P.E1 * t.val)

theorem eval_rightQBPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (c : Cell P) (t : Fin P.Mq) :
    MvPolynomial.eval (assignmentCoords ω) (rightQBPoly pp σ c t) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.QB σ c t)) := by
  have hz : coin ω.coins .zeta ≠ 0 := h.2.1 .zeta rfl
  simp only [rightQBPoly, map_mul, map_pow, eval_sectorPoly, scalarX, MvPolynomial.eval_X,
    assignmentCoords, eval_gammaPoly, eval_univarAtTau, e2At, g2Exp]
  field_simp

def rightRBPoly (pp : PublicParams P) (σ : Sector) (c : Cell P) (t : Fin P.Wr) : MonPoly P :=
  sectorPoly σ * scalarX .Om22 * scalarX .zeta * scalarX .zeta4 * scalarX .eps *
    gammaPoly c * univarAtTau pp.qap.Z0 * scalarX .tau ^ (P.U * P.E1p * t.val)

theorem eval_rightRBPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (c : Cell P) (t : Fin P.Wr) :
    MvPolynomial.eval (assignmentCoords ω) (rightRBPoly pp σ c t) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.RB σ c t)) := by
  have hz : coin ω.coins .zeta' ≠ 0 := h.2.1 .zeta' rfl
  simp only [rightRBPoly, map_mul, map_pow, eval_sectorPoly, scalarX, MvPolynomial.eval_X,
    assignmentCoords, eval_gammaPoly, eval_univarAtTau, e2At, g2Exp]
  field_simp

def tieCoin : TieIdx → ScalarCoin
  | .t1 => .c1
  | .t2 => .c2
  | .t3 => .c3

def rightGMPoly (σ : Sector) (s : TieIdx) (e : Fin (P.n - 1)) : MonPoly P :=
  sectorPoly σ * scalarX .Om22 * scalarX .zeta * scalarX .zeta' * scalarX .eps *
    scalarX .pi * scalarX (tieCoin s) * (scalarX .u ^ P.n - C (c0F P)) *
      scalarX .u ^ e.val

theorem eval_rightGMPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (s : TieIdx)
    (e : Fin (P.n - 1)) :
    MvPolynomial.eval (assignmentCoords ω) (rightGMPoly σ s e) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.GM σ s e)) := by
  have hz : coin ω.coins .zeta4 ≠ 0 := h.2.1 .zeta4 rfl
  cases s <;> simp only [rightGMPoly, map_mul, map_sub, map_pow, eval_sectorPoly, scalarX,
    MvPolynomial.eval_X, MvPolynomial.eval_C, assignmentCoords, tieCoin, e2At, g2Exp,
    cTie, kummerAtU] <;> field_simp

def crossPoly : CrossIdx → MonPoly P
  | .c1eps => scalarX .c1 * scalarX .eps ^ 2
  | .c2eps => scalarX .c2 * scalarX .eps ^ 2
  | .c3eps => scalarX .c3 * scalarX .eps ^ 2
  | .c2div => scalarX .c2
  | .c3div => scalarX .c3

def rightGBPoly (σ : Sector) (g : CrossIdx) (e : Fin (2 * P.n - 1)) : MonPoly P :=
  sectorPoly σ * scalarX .Om22 * scalarX .zeta * scalarX .zeta' * scalarX .pi *
    crossPoly g * scalarX .u ^ e.val

theorem eval_rightGBPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (g : CrossIdx)
    (e : Fin (2 * P.n - 1)) :
    MvPolynomial.eval (assignmentCoords ω) (rightGBPoly σ g e) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.GB σ g e)) := by
  have hz : coin ω.coins .zeta4 ≠ 0 := h.2.1 .zeta4 rfl
  have he : coin ω.coins .eps ≠ 0 := h.2.2.1
  cases g <;> simp only [rightGBPoly, crossPoly, map_mul, map_pow, eval_sectorPoly, scalarX,
    MvPolynomial.eval_X, assignmentCoords, e2At, g2Exp, crossVal] <;> field_simp

end

end Praxis.Proofs.Monitor
