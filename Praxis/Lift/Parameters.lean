import Praxis.Lift.Final
import Praxis.Lift.Pi
import Praxis.Constants
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

noncomputable section

namespace Praxis.Lift.Parameters

open Praxis.Algebra.Inverse.Definitions

def mainData : VITData where
  p := Praxis.Constants.q
  g := Praxis.Constants.g
  L0 := Praxis.Constants.lift_Y
  theta0 := (Praxis.Constants.theta : ℝ)
  eps := (Praxis.Constants.lift_eps_trim : ℝ)
  R := (Praxis.Constants.lift_R_trim : ℝ)
  S := (Praxis.Constants.N : ℝ)
  D := (Praxis.Constants.lift_exact_values_Lambda1 : ℝ)
  E := (Praxis.Constants.lift_exact_values_Lambda2 : ℝ)
  F := (Praxis.Constants.lift_exact_values_Lambda3 : ℝ)
  C1 := (Praxis.Constants.lift_exact_values_Gamma1 : ℝ)
  C2 := (Praxis.Constants.lift_exact_values_Gamma2 : ℝ)
  C3 := (Praxis.Constants.lift_exact_values_Gamma3 : ℝ)
  A := (Praxis.Constants.lift_exact_values_A : ℝ)
  Q1 := (Praxis.Constants.lift_exact_values_Q1 : ℝ)
  Q2 := (Praxis.Constants.lift_exact_values_Q2 : ℝ)

theorem main_mu : mainData.mu = (Praxis.Constants.lift_mu : ℝ) := by
  simp only [VITData.mu, mainData]
  norm_num [Praxis.Constants.theta, Praxis.Constants.lift_eps_trim, Praxis.Constants.lift_mu]

theorem main_H1 : mainData.H1 = (Praxis.Constants.lift_exact_values_H1 : ℝ) := by
  simp only [VITData.H1, VITData.mu, mainData]
  norm_num [Praxis.Constants.theta, Praxis.Constants.lift_eps_trim, Praxis.Constants.g,
    Praxis.Constants.lift_exact_values_Gamma1, Praxis.Constants.lift_exact_values_H1]

theorem main_H2 : mainData.H2 = (Praxis.Constants.lift_exact_values_H2 : ℝ) := by
  simp only [VITData.H2, VITData.mu, mainData]
  norm_num [Praxis.Constants.theta, Praxis.Constants.lift_eps_trim, Praxis.Constants.g,
    Praxis.Constants.lift_exact_values_Gamma2, Praxis.Constants.lift_exact_values_H2]

theorem main_xi : mainData.xi = (Praxis.Constants.lift_exact_values_xi : ℝ) := by
  simp only [VITData.xi, mainData]
  norm_num [Praxis.Constants.g, Praxis.Constants.lift_exact_values_xi]

theorem main_H3 : mainData.H3 = (Praxis.Constants.lift_exact_values_H3 : ℝ) := by
  simp only [VITData.H3, VITData.xi, VITData.mu, mainData]
  norm_num [Praxis.Constants.theta, Praxis.Constants.lift_eps_trim, Praxis.Constants.g,
    Praxis.Constants.lift_exact_values_H3]

theorem main_T2 : mainData.T2 = (Praxis.Constants.lift_exact_values_T_squared : ℝ) := by
  simp only [VITData.T2, mainData]
  norm_num [Praxis.Constants.lift_R_trim, Praxis.Constants.g, Praxis.Constants.N,
    Praxis.Constants.lift_exact_values_T_squared]

theorem main_L0_lower : 7 ≤ mainData.L0 := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_Y]

theorem main_g_lower : 2 ^ mainData.L0 ≤ mainData.g := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_Y, Praxis.Constants.g]

theorem main_g_upper : mainData.g < 2 ^ 254 := by
  simp only [mainData]; norm_num [Praxis.Constants.g]

theorem main_trim : TrimSide mainData.R mainData.eps := trimSide_main

theorem main_eps_pos : 0 < mainData.eps := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_eps_trim]

theorem main_eps_lt_mu : mainData.eps < mainData.mu := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.lift_eps_trim, Praxis.Constants.lift_mu]

theorem main_denominator_pos :
    0 < (mainData.g : ℝ)^3 * mainData.mu - mainData.xi / (mainData.g : ℝ) := by
  rw [main_mu, main_xi]; simp only [mainData]
  norm_num [Praxis.Constants.g, Praxis.Constants.lift_mu, Praxis.Constants.lift_exact_values_xi]

theorem main_S_pos : 0 < mainData.S := by
  simp only [mainData]; norm_num [Praxis.Constants.N]

theorem main_D_pos : 0 < mainData.D := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Lambda1]

theorem main_E_pos : 0 < mainData.E := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Lambda2]

theorem main_F_pos : 0 < mainData.F := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Lambda3]

theorem main_C1_pos : 0 < mainData.C1 := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Gamma1]

theorem main_C2_pos : 0 < mainData.C2 := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Gamma2]

theorem main_C3_pos : 0 < mainData.C3 := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Gamma3]

theorem main_A_pos : 0 < mainData.A := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_A]

theorem main_Q1_pos : 0 < mainData.Q1 := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Q1]

theorem main_Q2_pos : 0 < mainData.Q2 := by
  simp only [mainData]; norm_num [Praxis.Constants.lift_exact_values_Q2]

theorem main_D_geometry :
    12 * mainData.R^2 * mainData.S ≤ mainData.D^2 := by
  simp only [mainData]
  norm_num [Praxis.Constants.lift_R_trim, Praxis.Constants.N, Praxis.Constants.lift_exact_values_Lambda1]

theorem main_E_geometry :
    54^2 * Real.pi^2 * mainData.R^4 * mainData.S^2 / 2 ≤ mainData.E^2 := by
  simp only [mainData]
  have hpi := pi_lt_pi_up
  have hkey : (54 : ℝ)^2 * ((Praxis.Constants.lift_exact_values_pi_up : ℚ) : ℝ)^2 *
      ((Praxis.Constants.lift_R_trim : ℕ) : ℝ)^4 * ((Praxis.Constants.N : ℕ) : ℝ)^2 / 2 ≤
      ((Praxis.Constants.lift_exact_values_Lambda2 : ℚ) : ℝ)^2 := by
    norm_num [Praxis.Constants.lift_exact_values_pi_up, Praxis.Constants.lift_R_trim,
      Praxis.Constants.N, Praxis.Constants.lift_exact_values_Lambda2]
  refine le_trans ?_ hkey
  gcongr

theorem main_F_geometry :
    15552^2 * (4 * Real.pi / 3)^2 * mainData.R^6 * mainData.S^3 / (12^3 * 6) ≤
      mainData.F^2 := by
  simp only [mainData]
  have hpi := pi_lt_pi_up
  have hkey : (15552 : ℝ)^2 * (4 * ((Praxis.Constants.lift_exact_values_pi_up : ℚ) : ℝ) / 3)^2 *
      ((Praxis.Constants.lift_R_trim : ℕ) : ℝ)^6 * ((Praxis.Constants.N : ℕ) : ℝ)^3 / (12^3 * 6) ≤
      ((Praxis.Constants.lift_exact_values_Lambda3 : ℚ) : ℝ)^2 := by
    norm_num [Praxis.Constants.lift_exact_values_pi_up, Praxis.Constants.lift_R_trim,
      Praxis.Constants.N, Praxis.Constants.lift_exact_values_Lambda3]
  refine le_trans ?_ hkey
  gcongr

theorem main_C3_height :
    mainData.xi * (1 + mainData.H3 / (mainData.g : ℝ)) ≤ mainData.C3 := by
  rw [main_xi, main_H3]; simp only [mainData]
  norm_num [Praxis.Constants.g, Praxis.Constants.lift_exact_values_xi,
    Praxis.Constants.lift_exact_values_H3, Praxis.Constants.lift_exact_values_Gamma3]

theorem main_A_restore :
    mainData.mu / (mainData.mu - mainData.eps) ≤ mainData.A := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.lift_mu, Praxis.Constants.lift_eps_trim, Praxis.Constants.lift_exact_values_A]

theorem main_Q2_power :
    ((mainData.g : ℝ)^(-(3 : ℤ)) + mainData.eps) / mainData.mu ≤
      mainData.Q2^(mainData.L0-1) := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.g, Praxis.Constants.lift_eps_trim, Praxis.Constants.lift_mu,
    Praxis.Constants.lift_exact_values_Q2, Praxis.Constants.lift_Y]

theorem main_Q1_power :
    ((mainData.g : ℝ)^(-(2 : ℤ)) + 2*mainData.eps) / mainData.mu ≤
      mainData.Q1^(mainData.L0-1) := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.g, Praxis.Constants.lift_eps_trim, Praxis.Constants.lift_mu,
    Praxis.Constants.lift_exact_values_Q1, Praxis.Constants.lift_Y]

theorem main_C2_power :
    (mainData.g : ℝ)^(-(2 : ℤ)) / mainData.mu ≤ mainData.C2^(mainData.L0-1) := by
  rw [main_mu]; simp only [mainData]
  have hinit : (((Praxis.Constants.g : ℕ) : ℝ))^(-(2 : ℤ)) / ((Praxis.Constants.lift_mu : ℚ) : ℝ) ≤
      ((Praxis.Constants.lift_exact_values_Gamma2_initial : ℚ) : ℝ)^(Praxis.Constants.lift_Y - 1) := by
    norm_num [Praxis.Constants.g, Praxis.Constants.lift_mu,
      Praxis.Constants.lift_exact_values_Gamma2_initial, Praxis.Constants.lift_Y]
  have hle : ((Praxis.Constants.lift_exact_values_Gamma2_initial : ℚ) : ℝ) ≤
      ((Praxis.Constants.lift_exact_values_Gamma2 : ℚ) : ℝ) := by
    norm_num [Praxis.Constants.lift_exact_values_Gamma2_initial, Praxis.Constants.lift_exact_values_Gamma2]
  have h0 : (0 : ℝ) ≤ ((Praxis.Constants.lift_exact_values_Gamma2_initial : ℚ) : ℝ) := by
    norm_num [Praxis.Constants.lift_exact_values_Gamma2_initial]
  exact hinit.trans (pow_le_pow_left₀ h0 hle _)

theorem main_C1_power :
    (mainData.g : ℝ)⁻¹ / mainData.mu ≤ mainData.C1^(mainData.L0-1) := by
  rw [main_mu]; simp only [mainData]
  have hinit : (((Praxis.Constants.g : ℕ) : ℝ))⁻¹ / ((Praxis.Constants.lift_mu : ℚ) : ℝ) ≤
      ((Praxis.Constants.lift_exact_values_Gamma1_initial : ℚ) : ℝ)^(Praxis.Constants.lift_Y - 1) := by
    norm_num [Praxis.Constants.g, Praxis.Constants.lift_mu,
      Praxis.Constants.lift_exact_values_Gamma1_initial, Praxis.Constants.lift_Y]
  have hle : ((Praxis.Constants.lift_exact_values_Gamma1_initial : ℚ) : ℝ) ≤
      ((Praxis.Constants.lift_exact_values_Gamma1 : ℚ) : ℝ) := by
    norm_num [Praxis.Constants.lift_exact_values_Gamma1_initial, Praxis.Constants.lift_exact_values_Gamma1]
  have h0 : (0 : ℝ) ≤ ((Praxis.Constants.lift_exact_values_Gamma1_initial : ℚ) : ℝ) := by
    norm_num [Praxis.Constants.lift_exact_values_Gamma1_initial]
  exact hinit.trans (pow_le_pow_left₀ h0 hle _)

theorem main_C2_recursion :
    mainData.A * mainData.D * mainData.C3 * mainData.Q2 ≤ mainData.C2 := by
  simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_A, Praxis.Constants.lift_exact_values_Lambda1,
    Praxis.Constants.lift_exact_values_Gamma3, Praxis.Constants.lift_exact_values_Q2,
    Praxis.Constants.lift_exact_values_Gamma2]

theorem main_C1_recursion :
    mainData.A * max (mainData.D * mainData.C2) (mainData.E * mainData.C3) *
      mainData.Q1 ≤ mainData.C1 := by
  simp only [mainData]
  rcases max_cases (((Praxis.Constants.lift_exact_values_Lambda1 : ℚ) : ℝ) *
      ((Praxis.Constants.lift_exact_values_Gamma2 : ℚ) : ℝ))
      (((Praxis.Constants.lift_exact_values_Lambda2 : ℚ) : ℝ) *
      ((Praxis.Constants.lift_exact_values_Gamma3 : ℚ) : ℝ)) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;>
    norm_num [Praxis.Constants.lift_exact_values_A, Praxis.Constants.lift_exact_values_Lambda1,
      Praxis.Constants.lift_exact_values_Lambda2, Praxis.Constants.lift_exact_values_Gamma2,
      Praxis.Constants.lift_exact_values_Gamma3, Praxis.Constants.lift_exact_values_Q1,
      Praxis.Constants.lift_exact_values_Gamma1]

theorem main_wrap1 : mainData.D * mainData.C1 / (mainData.p : ℝ) < mainData.mu := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_Lambda1, Praxis.Constants.lift_exact_values_Gamma1,
    Praxis.Constants.q, Praxis.Constants.lift_mu]

theorem main_wrap2 : mainData.E * mainData.C2 / (mainData.p : ℝ) < mainData.mu := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_Lambda2, Praxis.Constants.lift_exact_values_Gamma2,
    Praxis.Constants.q, Praxis.Constants.lift_mu]

theorem main_wrap3 : mainData.F * mainData.C3 / (mainData.p : ℝ) < mainData.mu := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_Lambda3, Praxis.Constants.lift_exact_values_Gamma3,
    Praxis.Constants.q, Praxis.Constants.lift_mu]

theorem main_rank4_light : (mainData.g : ℝ)^(-(4 : ℤ)) < mainData.mu := by
  rw [main_mu]; simp only [mainData]
  norm_num [Praxis.Constants.g, Praxis.Constants.lift_mu]

theorem main_minor1 : mainData.H1^2 * mainData.T2 < (mainData.p : ℝ)^2 := by
  rw [main_H1, main_T2]; simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_H1, Praxis.Constants.lift_exact_values_T_squared,
    Praxis.Constants.q]

theorem main_minor2 : 4 * mainData.H2 * mainData.T2 < (mainData.p : ℝ) := by
  rw [main_H2, main_T2]; simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_H2, Praxis.Constants.lift_exact_values_T_squared,
    Praxis.Constants.q]

theorem main_minor3 :
    (54 * mainData.H3)^2 * mainData.T2^3 < (mainData.p : ℝ)^2 := by
  rw [main_H3, main_T2]; simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_H3, Praxis.Constants.lift_exact_values_T_squared,
    Praxis.Constants.q]

theorem main_branch1 : Int.ceil mainData.H1 = (Praxis.Constants.eta : ℤ) := by
  rw [main_H1, Int.ceil_eq_iff]
  constructor <;>
    norm_num [Praxis.Constants.lift_exact_values_H1, Praxis.Constants.eta]

theorem main_branch2 :
    Int.ceil (2 * mainData.H2 * (mainData.p : ℝ)) ≤ (Praxis.Constants.eta : ℤ) ^ 2 := by
  rw [main_H2, Int.ceil_le]
  simp only [mainData]
  norm_num [Praxis.Constants.lift_exact_values_H2, Praxis.Constants.q, Praxis.Constants.eta]

theorem main_H3_floor :
    Int.floor mainData.H3 = (Praxis.Constants.lift_H3_floor : ℤ) := by
  rw [main_H3, Int.floor_eq_iff]
  constructor <;>
    norm_num [Praxis.Constants.lift_exact_values_H3, Praxis.Constants.lift_H3_floor]

theorem main_branch3 :
    6 * Int.floor mainData.H3 * (mainData.p : ℤ) ^ 2 ≤ (Praxis.Constants.eta : ℤ) ^ 3 := by
  rw [main_H3_floor]
  simp only [mainData]
  norm_num [Praxis.Constants.lift_H3_floor, Praxis.Constants.q, Praxis.Constants.eta]

theorem main_two_eta_lt_p : 2 * Praxis.Constants.eta < mainData.p := by
  simp only [mainData]
  norm_num [Praxis.Constants.q, Praxis.Constants.eta]

variable [Fact (Nat.Prime Praxis.Constants.q)]

def mainParams : VITParameters where
  toVITData := mainData
  p_prime := (Fact.out : Nat.Prime Praxis.Constants.q)
  L0_lower := main_L0_lower
  g_lower := main_g_lower
  g_upper := main_g_upper
  trim := main_trim
  eps_pos := main_eps_pos
  eps_lt_mu := main_eps_lt_mu
  denominator_pos := main_denominator_pos
  S_pos := main_S_pos
  D_pos := main_D_pos
  E_pos := main_E_pos
  F_pos := main_F_pos
  C1_pos := main_C1_pos
  C2_pos := main_C2_pos
  C3_pos := main_C3_pos
  A_pos := main_A_pos
  Q1_pos := main_Q1_pos
  Q2_pos := main_Q2_pos
  D_geometry := main_D_geometry
  E_geometry := main_E_geometry
  F_geometry := main_F_geometry
  C3_height := main_C3_height
  A_restore := main_A_restore
  Q2_power := main_Q2_power
  Q1_power := main_Q1_power
  C2_power := main_C2_power
  C1_power := main_C1_power
  C2_recursion := main_C2_recursion
  C1_recursion := main_C1_recursion
  wrap1 := main_wrap1
  wrap2 := main_wrap2
  wrap3 := main_wrap3
  rank4_light := main_rank4_light
  minor1 := main_minor1
  minor2 := main_minor2
  minor3 := main_minor3

def mainRecord : CertifiedLiftParameters where
  toVITParameters := mainParams
  eta := Praxis.Constants.eta
  two_eta_lt_p := main_two_eta_lt_p
  branch1 := main_branch1.le
  branch2 := main_branch2
  branch3 := main_branch3

theorem lift_main : LiftHyp mainRecord := liftHolds mainRecord

end Praxis.Lift.Parameters

end
