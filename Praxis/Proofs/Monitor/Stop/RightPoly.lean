import Praxis.Proofs.Monitor.Stop.LeftPoly
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

def rX (i : Fin (P.N + 1)) : MonPoly P := X (.inr (.inl i))

def lambdaPoly (v : Fin P.n → Algebra.Vec (Fq P) P.N) (s : MonPoly P)
    (j : Fin (P.N + 1)) : MonPoly P :=
  ∑ e, s ^ e.val * C (v e j)

theorem eval_lambdaPoly (ω : Assign P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (s : MonPoly P) (j : Fin (P.N + 1)) :
    MvPolynomial.eval (assignmentCoords ω) (lambdaPoly v s j) =
      lam v (MvPolynomial.eval (assignmentCoords ω) s) j := by
  simp [lambdaPoly, lam, Finset.sum_apply, smul_eq_mul]

def maskPoly (v : Fin P.n → Algebra.Vec (Fq P) P.N) (l : Leg P)
    (j : Fin (P.N + 1)) : MonPoly P :=
  let u := scalarX .u
  let b := -C (betaF P) * u
  let t := C (betaF P ^ (P.m - 1)) * u
  match l.1 with
  | .V => scalarX .eps * u ^ legExp l *
      (scalarX .c3 * lambdaPoly v b j - scalarX .c1 * lambdaPoly v t j)
  | _ => scalarX .eps * u ^ legExp l *
      (scalarX .c1 * lambdaPoly v (-u) j + scalarX .c2 * lambdaPoly v b j) -
      b ^ legExp l *
      (scalarX .c2 * lambdaPoly v t j + scalarX .c3 * lambdaPoly v (-u) j)

theorem eval_maskPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N) (ω : Assign P)
    (h : ValidCoins pp.qap ω.coins) (l : Leg P) (j : Fin (P.N + 1)) :
    MvPolynomial.eval (assignmentCoords ω) (maskPoly v l j) =
      coin ω.coins .eps * legMask v ω.coins l j := by
  have he : coin ω.coins .eps ≠ 0 := h.2.2.1
  rcases l with ⟨kind, k⟩
  cases kind <;>
    simp only [maskPoly, map_mul, map_sub, map_add, map_neg, map_pow,
      MvPolynomial.eval_C, scalarX, MvPolynomial.eval_X, assignmentCoords,
      eval_lambdaPoly, legMask, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] <;> field_simp <;> ring

def rightR1Poly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (σ : Sector) (l : Leg P) (j : Fin (P.N + 1)) : MonPoly P :=
  sectorPoly σ * (deltaPoly * legPoly l * (rX j + univarAtTau (pp.qap.A j)) +
    scalarX .Om22 * scalarX .zeta * scalarX .zeta' * scalarX .zeta4 * maskPoly v l j -
    scalarX .Om12 * scalarX .zeta * scalarX .zeta' * scalarX .zeta4 * scalarX .eps *
      h2Poly pp l j)

theorem eval_rightR1Poly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (l : Leg P)
    (j : Fin (P.N + 1)) :
    MvPolynomial.eval (assignmentCoords ω) (rightR1Poly pp v σ l j) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.ZeroCoordinate σ l j)) := by
  have h22 : coin ω.coins .Om22 ≠ 0 := h.2.1 .Om22 rfl
  simp only [rightR1Poly, deltaPoly, map_mul, map_add, map_sub, eval_sectorPoly,
    eval_legPoly, eval_univarAtTau, eval_maskPoly pp v ω h, eval_h2Poly, scalarX, rX,
    MvPolynomial.eval_X, assignmentCoords, e2At, r1ExpAt]
  field_simp
  <;> ring

def rightTotR1Poly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (σ : Sector) (l : Leg P) : MonPoly P := ∑ j, rightR1Poly pp v σ l j

theorem eval_rightTotR1Poly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (σ : Sector) (l : Leg P) :
    MvPolynomial.eval (assignmentCoords ω) (rightTotR1Poly pp v σ l) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω (some (.totR1 σ l)) := by
  simp only [rightTotR1Poly, map_sum, eval_rightR1Poly pp v ω h, e2At,
    Finset.mul_sum]

def rightPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N) :
    Option (G2Idx P) → MonPoly P
  | none => deltaPoly
  | some (.ZeroCoordinate σ l j) => rightR1Poly pp v σ l j
  | some (.R2 σ l j) => rightR2Poly pp σ l j
  | some (.totR1 σ l) => rightTotR1Poly pp v σ l
  | some (.totR2 σ l) => rightTotR2Poly pp σ l
  | some (.QB σ c t) => rightQBPoly pp σ c t
  | some (.RB σ c t) => rightRBPoly pp σ c t
  | some (.SC σ l) => rightSCPoly σ l
  | some (.GB σ g e) => rightGBPoly σ g e
  | some (.GM σ s e) => rightGMPoly σ s e

theorem eval_rightPoly (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (h : ValidCoins pp.qap ω.coins) (b : Option (G2Idx P)) :
    MvPolynomial.eval (assignmentCoords ω) (rightPoly pp v b) =
      (coin ω.coins .Om22 * coin ω.coins .zeta * coin ω.coins .zeta' *
        coin ω.coins .zeta4 * coin ω.coins .eps) * e2At pp v ω b := by
  cases b with
  | none => simp [rightPoly, deltaPoly, scalarX, assignmentCoords, e2At]
  | some b =>
    cases b <;> simp only [rightPoly, eval_rightR1Poly pp v ω h,
      eval_rightR2Poly pp v ω h, eval_rightTotR1Poly pp v ω h,
      eval_rightTotR2Poly pp v ω h, eval_rightQBPoly pp v ω h,
      eval_rightRBPoly pp v ω h, eval_rightSCPoly pp v ω,
      eval_rightGBPoly pp v ω h, eval_rightGMPoly pp v ω h]

end

end Praxis.Proofs.Monitor
