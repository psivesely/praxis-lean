import Praxis.Algebra.Inverse.Definitions
import Praxis.Lift.Trim

set_option autoImplicit false

namespace Praxis.Lift

open Praxis.Algebra.Inverse.Definitions

structure VITParameters extends VITData where
  p_prime : p.Prime
  L0_lower : 7 ≤ L0
  g_lower : 2^L0 ≤ g
  g_upper : g < 2^254

  trim : TrimSide R eps
  eps_pos : 0 < eps
  eps_lt_mu : eps < toVITData.mu
  denominator_pos : 0 < (g : ℝ)^3 * toVITData.mu - toVITData.xi / (g : ℝ)
  S_pos : 0 < S
  D_pos : 0 < D
  E_pos : 0 < E
  F_pos : 0 < F
  C1_pos : 0 < C1
  C2_pos : 0 < C2
  C3_pos : 0 < C3
  A_pos : 0 < A
  Q1_pos : 0 < Q1
  Q2_pos : 0 < Q2
  D_geometry : 12 * R^2 * S ≤ D^2
  E_geometry : 54^2 * Real.pi^2 * R^4 * S^2 / 2 ≤ E^2
  F_geometry : 15552^2 * (4 * Real.pi / 3)^2 * R^6 * S^3 / (12^3 * 6) ≤ F^2
  C3_height : toVITData.xi * (1 + toVITData.H3 / (g : ℝ)) ≤ C3
  A_restore : toVITData.mu / (toVITData.mu - eps) ≤ A
  Q2_power : ((g : ℝ)^(-(3 : ℤ)) + eps) / toVITData.mu ≤ Q2^(L0-1)
  Q1_power : ((g : ℝ)^(-(2 : ℤ)) + 2*eps) / toVITData.mu ≤ Q1^(L0-1)
  C2_power : (g : ℝ)^(-(2 : ℤ)) / toVITData.mu ≤ C2^(L0-1)
  C1_power : (g : ℝ)⁻¹ / toVITData.mu ≤ C1^(L0-1)
  C2_recursion : A * D * C3 * Q2 ≤ C2
  C1_recursion : A * max (D*C2) (E*C3) * Q1 ≤ C1
  wrap1 : D * C1 / (p : ℝ) < toVITData.mu
  wrap2 : E * C2 / (p : ℝ) < toVITData.mu
  wrap3 : F * C3 / (p : ℝ) < toVITData.mu
  rank4_light : (g : ℝ)^(-(4 : ℤ)) < toVITData.mu
  minor1 : toVITData.H1^2 * toVITData.T2 < (p : ℝ)^2
  minor2 : 4 * toVITData.H2 * toVITData.T2 < (p : ℝ)
  minor3 : (54 * toVITData.H3)^2 * toVITData.T2^3 < (p : ℝ)^2

theorem VITParameters.R_pos (P : VITParameters) : 0 < P.R := by
  linarith [P.trim.1]

structure CertifiedLiftParameters extends VITParameters where

  eta : ℕ

  two_eta_lt_p : 2 * eta < p

  branch1 : Int.ceil toVITData.H1 ≤ (eta : ℤ)

  branch2 : Int.ceil (2 * toVITData.H2 * (p : ℝ)) ≤ (eta : ℤ) ^ 2

  branch3 : 6 * Int.floor toVITData.H3 * (p : ℤ) ^ 2 ≤ (eta : ℤ) ^ 3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def VectorInverseStatement (P : CertifiedLiftParameters)
    (G : ι → ℕ) (z : ι → ZMod P.p) : Prop :=
  GridBudget P.toVITData G → z ≠ 0 → P.theta0 < mass G (scalar G z) →
    ShortMultiple P.p z (P.eta : ℝ)

def VectorInverseZ0Statement (P : CertifiedLiftParameters) {n : ℕ}
    (G : Fin n → ℕ) (z : Fin (n+1) → ZMod P.p) : Prop :=
  GridBudget P.toVITData G → z ≠ 0 → z 0 = 0 →
    P.theta0 < mass G (scalar G (fun i => z i.succ)) →
    ∃ (c : ZMod P.p) (w : Fin (n+1) → ℤ), c ≠ 0 ∧ w ≠ 0 ∧ w 0 = 0 ∧
      (∀ i, (w i : ZMod P.p) = c * z i) ∧ maxAbs w ≤ P.eta

def LiftHyp (P : CertifiedLiftParameters) : Prop :=
  ∀ (n : ℕ) (G : Fin n → ℕ) (z : Fin (n+1) → ZMod P.p),
    VectorInverseZ0Statement P G z

def LiftHolds : Prop := ∀ P : CertifiedLiftParameters, LiftHyp P

end Praxis.Lift
