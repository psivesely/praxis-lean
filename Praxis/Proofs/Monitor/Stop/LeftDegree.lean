import Praxis.Proofs.Monitor.Stop.Degree
import Praxis.Enc
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open MvPolynomial

noncomputable section

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem deg_mul_le {a b : MonPoly P} {m n : ℕ} (ha : a.totalDegree ≤ m)
    (hb : b.totalDegree ≤ n) : (a * b).totalDegree ≤ m + n :=
  (MvPolynomial.totalDegree_mul a b).trans (Nat.add_le_add ha hb)

theorem deg_add_le {a b : MonPoly P} {d : ℕ} (ha : a.totalDegree ≤ d)
    (hb : b.totalDegree ≤ d) : (a + b).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)

theorem deg_sub_le {a b : MonPoly P} {d : ℕ} (ha : a.totalDegree ≤ d)
    (hb : b.totalDegree ≤ d) : (a - b).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub a b).trans (max_le ha hb)

theorem deg_C_le (c : Fq P) : (C c : MonPoly P).totalDegree ≤ 0 := by
  simp

theorem deg_scalarX_pow_le (s : ScalarCoin) (k : ℕ) :
    ((scalarX s : MonPoly P) ^ k).totalDegree ≤ k := by
  simp [scalarX, MvPolynomial.totalDegree_X_pow]

theorem deg_sum_le {ι : Type} (t : Finset ι) (f : ι → MonPoly P) {d : ℕ}
    (h : ∀ i ∈ t, (f i).totalDegree ≤ d) : (∑ i ∈ t, f i).totalDegree ≤ d :=
  MvPolynomial.totalDegree_finsetSum_le h

theorem degree_leftPoly_le (pp : PublicParams P) (hA : ∀ i, (pp.qap.A i).natDegree < P.D)
    (hD : 2 ≤ P.D) (hE : P.E1 ≤ P.D + 2 * P.K1) (hU : P.U * P.E1p ≤ P.D + 2 * P.K1)
    (a : Option (G1Idx P)) : (leftPoly pp a).totalDegree ≤ P.D + 2 * P.K1 := by
  have hL2 : ∀ (k : Fin P.K1) (i : Fin (P.N + 1)),
      (piPoly k.val * (scalarX .Om12 * yX i + scalarX .Om22 * univarAtTau (pp.qap.A i)) :
        MonPoly P).totalDegree ≤ P.D + 2 * P.K1 := by
    intro k i
    have h1 := degree_piPoly (P := P) k.val
    have h2 : (scalarX .Om12 * yX i : MonPoly P).totalDegree ≤ 2 :=
      (deg_mul_le (degree_scalarX .Om12).le (degree_yX i).le)
    have h3 : (scalarX .Om22 * univarAtTau (pp.qap.A i) : MonPoly P).totalDegree ≤ 1 + (P.D - 1) :=
      deg_mul_le (degree_scalarX .Om22).le
        ((degree_univarAtTau _).trans (by have := hA i; omega))
    have h4 := deg_add_le (a := scalarX .Om12 * yX i)
      (b := scalarX .Om22 * univarAtTau (pp.qap.A i)) (d := P.D) (by omega) (by omega)
    have h5 := deg_mul_le h1 h4
    have := k.2
    omega
  have hL1 : ∀ (k : Fin P.K1) (i : Fin (P.N + 1)),
      (piPoly k.val * yX i : MonPoly P).totalDegree ≤ P.D + 2 * P.K1 := by
    intro k i
    have h5 := deg_mul_le (degree_piPoly (P := P) k.val) (degree_yX (P := P) i).le
    have := k.2
    omega
  cases a with
  | none => simp [leftPoly]
  | some a =>
    cases a with
    | L1 k i => exact hL1 k i
    | L2 k i => exact hL2 k i
    | totL1 k => exact deg_sum_le _ _ (fun i _ => hL1 k i)
    | totL2 k => exact deg_sum_le _ _ (fun i _ => hL2 k i)
    | QP s =>
      have h := deg_mul_le (degree_scalarX (P := P) .zeta).le (deg_scalarX_pow_le (P := P) .tau s.val)
      have := s.2
      simp only [leftPoly]
      omega
    | RP s =>
      have h := deg_mul_le (degree_scalarX (P := P) .zeta').le
        (deg_scalarX_pow_le (P := P) .tau s.1.val)
      have := s.1.2
      simp only [leftPoly]
      omega
    | GY i =>
      have h := deg_mul_le (degree_scalarX (P := P) .zeta4).le (degree_yX (P := P) i).le
      simp only [leftPoly]
      omega

end

end Praxis.Proofs.Monitor
