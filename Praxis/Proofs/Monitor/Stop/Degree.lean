import Praxis.Proofs.Monitor.Stop.RightPoly
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open MvPolynomial

noncomputable section

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem degree_univarAtTau (p : Polynomial (Fq P)) :
    (univarAtTau p).totalDegree ≤ p.natDegree := by
  classical
  unfold univarAtTau
  rw [Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  have hp := MvPolynomial.totalDegree_mul (C (p.coeff i)) ((scalarX .tau : MonPoly P) ^ i)
  simp only [MvPolynomial.totalDegree_C, zero_add, scalarX,
    MvPolynomial.totalDegree_X_pow] at hp
  exact hp.trans (Polynomial.le_natDegree_of_mem_supp i hi)

theorem degree_scalarX (s : ScalarCoin) : (scalarX s : MonPoly P).totalDegree = 1 := by
  simp [scalarX]

theorem degree_yX (i : Fin (P.N + 1)) : (yX i : MonPoly P).totalDegree = 1 := by
  simp [yX]

theorem degree_rX (i : Fin (P.N + 1)) : (rX i : MonPoly P).totalDegree = 1 := by
  simp [rX]

theorem degree_sectorPoly (σ : Sector) : (sectorPoly σ : MonPoly P).totalDegree ≤ 1 := by
  cases σ <;> simp [sectorPoly, degree_scalarX]

theorem degree_piPoly (k : ℕ) : (piPoly k : MonPoly P).totalDegree ≤ 2 * k + 2 := by
  have h₁ := MvPolynomial.totalDegree_mul (scalarX .pi : MonPoly P) (scalarX .u ^ (2 * k))
  have h₂ := MvPolynomial.totalDegree_mul (scalarX .eps : MonPoly P) (C (thetaAt (P := P) k))
  have h₃ := MvPolynomial.totalDegree_add (1 : MonPoly P)
    (scalarX .eps * C (thetaAt (P := P) k))
  have h₄ := MvPolynomial.totalDegree_mul
    (scalarX .pi * scalarX .u ^ (2 * k) : MonPoly P)
    (1 + scalarX .eps * C (thetaAt (P := P) k))
  unfold piPoly
  simp only [scalarX, MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X,
    MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_one, Nat.zero_max] at h₁ h₂ h₃ h₄ ⊢
  omega

theorem degree_deltaPoly : (deltaPoly : MonPoly P).totalDegree ≤ 5 := by
  unfold deltaPoly
  have h₁ := MvPolynomial.totalDegree_mul (scalarX .Om22 : MonPoly P) (scalarX .zeta)
  have h₂ := MvPolynomial.totalDegree_mul (scalarX .Om22 * scalarX .zeta : MonPoly P)
    (scalarX .zeta')
  have h₃ := MvPolynomial.totalDegree_mul
    (scalarX .Om22 * scalarX .zeta * scalarX .zeta' : MonPoly P) (scalarX .zeta4)
  have h₄ := MvPolynomial.totalDegree_mul
    (scalarX .Om22 * scalarX .zeta * scalarX .zeta' * scalarX .zeta4 : MonPoly P)
    (scalarX .eps)
  simp only [degree_scalarX] at h₁ h₂ h₃ h₄
  omega

theorem degree_legPoly (l : Leg P) : (legPoly l : MonPoly P).totalDegree ≤ legExp l + 1 := by
  have h := MvPolynomial.totalDegree_mul (scalarX (legCoin l.1) : MonPoly P)
    (scalarX .u ^ (l.1.base + 2 * P.K1 * l.2.val))
  unfold legPoly legExp
  simp only [scalarX, MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X] at h ⊢
  omega

theorem degree_gammaPoly (c : Cell P) :
    (gammaPoly c : MonPoly P).totalDegree ≤ 2 * c.1.val + 2 + (legExp c.2 + 1) := by
  have h := MvPolynomial.totalDegree_mul (piPoly c.1.val : MonPoly P) (legPoly c.2)
  exact h.trans (Nat.add_le_add (degree_piPoly c.1.val) (degree_legPoly c.2))

theorem degree_h2Poly (pp : PublicParams P) (l : Leg P) (j : Fin (P.N + 1)) (d : ℕ)
    (hB : (pp.qap.B j).natDegree ≤ d) :
    (h2Poly pp l j).totalDegree ≤ legExp l + 1 + max d 1 := by
  have h₁ := MvPolynomial.totalDegree_sub (univarAtTau (pp.qap.B j)) (yX j)
  have h₂ := MvPolynomial.totalDegree_mul (legPoly l) (univarAtTau (pp.qap.B j) - yX j)
  have hu := (degree_univarAtTau (pp.qap.B j)).trans hB
  rw [degree_yX] at h₁
  exact h₂.trans (Nat.add_le_add (degree_legPoly l) (h₁.trans (max_le_max hu le_rfl)))

theorem degree_keyPoly (pp : PublicParams P) (h : pp.qap.Lrho.natDegree < P.D) :
    (keyPoly pp).totalDegree ≤ P.D + 7 := by
  have h₁ := MvPolynomial.totalDegree_mul (piPoly 0 : MonPoly P) (scalarX .bE)
  have h₂ := MvPolynomial.totalDegree_mul (piPoly 0 * scalarX .bE : MonPoly P)
    (univarAtTau pp.qap.Lrho)
  have h₃ := MvPolynomial.totalDegree_mul (deltaPoly : MonPoly P)
    (piPoly 0 * scalarX .bE * univarAtTau pp.qap.Lrho)
  have hpi := degree_piPoly (P := P) 0
  have hd := degree_deltaPoly (P := P)
  have hu := degree_univarAtTau (P := P) pp.qap.Lrho
  simp only [degree_scalarX] at h₁
  unfold keyPoly
  omega

end

end Praxis.Proofs.Monitor
