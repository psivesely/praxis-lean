import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.InverseBranches.NormalBranches
import Mathlib.Analysis.Real.Pi.Bounds
import Praxis.Combinatorics.Mass
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Algebra.DifferenceLattice.Saturation

set_option autoImplicit false

namespace Praxis.Algebra.Inverse.Definitions

open Finset Module

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Grid (G : ι → ℕ) := Combinatorics.Mass.Grid G

noncomputable def atom {α : Type*} (G : ι → ℕ)
    (f : Grid G → α) (t : α) : ℝ := Algebra.FiniteProbability.pointProb f t

noncomputable def mass {α : Type*} (G : ι → ℕ)
    (f : Grid G → α) : ℝ := Algebra.FiniteProbability.atomMass f

def scalar {A : Type*} [CommRing A] (G : ι → ℕ)
    (z : ι → A) (r : Grid G) : A := ∑ i, z i * ((r i : ℕ) : A)

def imageZ {d : ℕ} (G : ι → ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid G) : Fin d → ℤ :=
  fun j => ∑ i, B i j * ((r i : ℕ) : ℤ)

def maxAbs (w : ι → ℤ) : ℕ := Combinatorics.UnequalChain.maxNorm w

def height {d : ℕ} (B : Matrix ι (Fin d) ℤ) : ℕ :=
  Algebra.VectorInverse.largestMinor B

def Saturated (L : Submodule ℤ (ι → ℤ)) : Prop := Algebra.Lattice.IsSaturated L

structure IntLat (ι : Type*) [Fintype ι] (d : ℕ) where
  carrier : Submodule ℤ (ι → ℤ)
  basis : Basis (Fin d) ℤ carrier
  saturated : Algebra.Lattice.IsSaturated carrier

noncomputable def IntLat.matrix {d : ℕ} (L : IntLat ι d) : Matrix ι (Fin d) ℤ :=
  fun i j => (L.basis j : ι → ℤ) i

noncomputable def IntLat.mZ {d : ℕ} (G : ι → ℕ) (L : IntLat ι d) : ℝ :=
  mass G (imageZ G L.matrix)

noncomputable def IntLat.H {d : ℕ} (L : IntLat ι d) : ℕ := height L.matrix

def redSpan (p : ℕ) {d : ℕ} (L : IntLat ι d) :
    Submodule (ZMod p) (ι → ZMod p) :=
  Submodule.span (ZMod p) {v | ∃ w ∈ L.carrier, v = fun i => (w i : ZMod p)}

def ShortMultiple (p : ℕ) (z : ι → ZMod p) (beta : ℝ) : Prop :=
  ∃ (c : ZMod p) (w : ι → ℤ), c ≠ 0 ∧ w ≠ 0 ∧
    (∀ i, (w i : ZMod p) = c * z i) ∧ (maxAbs w : ℝ) ≤ beta

structure VITData where
  p : ℕ
  g : ℕ
  L0 : ℕ
  theta0 : ℝ
  eps : ℝ
  R : ℝ
  S : ℝ
  D : ℝ
  E : ℝ
  F : ℝ
  C1 : ℝ
  C2 : ℝ
  C3 : ℝ
  A : ℝ
  Q1 : ℝ
  Q2 : ℝ

noncomputable def VITData.xi (P : VITData) : ℝ := (1 + 2 / (P.g : ℝ)) ^ 254

noncomputable def VITData.mu (P : VITData) : ℝ := P.theta0 - 100 * P.eps

noncomputable def VITData.H1 (P : VITData) : ℝ := P.C1 / ((P.g : ℝ) * P.mu)

noncomputable def VITData.H2 (P : VITData) : ℝ := P.C2 / ((P.g : ℝ)^2 * P.mu)

noncomputable def VITData.H3 (P : VITData) : ℝ :=
  P.xi / ((P.g : ℝ)^3 * P.mu - P.xi / (P.g : ℝ))

noncomputable def VITData.T2 (P : VITData) : ℝ := P.R^2 * (P.g : ℝ)^2 * P.S / 3

noncomputable def VITData.C (P : VITData) (d : ℕ) : ℝ :=
  if d = 1 then P.C1 else if d = 2 then P.C2 else if d = 3 then P.C3 else 0

structure VITParameters extends VITData where
  p_prime : p.Prime
  L0_lower : 7 ≤ L0
  g_lower : 2^L0 ≤ g
  g_upper : g < 2^254
  eps_eq : eps = (2 : ℝ)^(-(270 : ℤ))
  R_eq : R = 20
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

structure CertifiedVITParameters extends VITParameters where
  thetaRow : ℝ
  beta : ℝ
  theta0_lt_row : theta0 < thetaRow
  beta_pos : 0 < beta
  beta_cube : beta^3 =
    6 * (toVITData.xi / ((g : ℝ)^3 * thetaRow - toVITData.xi / (g : ℝ))) * (p : ℝ)^2
  beta_lt_p : beta < (p : ℝ)
  H1_cube : toVITData.H1^3 < beta^3
  H2_cube : (2 * toVITData.H2 * (p : ℝ))^3 < beta^6
  height_floor_eq : Int.floor toVITData.H3 =
    Int.floor (toVITData.xi / ((g : ℝ)^3 * thetaRow - toVITData.xi / (g : ℝ)))
  height_floor_lt : (Int.floor toVITData.H3 : ℝ) <
    toVITData.xi / ((g : ℝ)^3 * thetaRow - toVITData.xi / (g : ℝ))

noncomputable def CertifiedVITParameters.B (P : CertifiedVITParameters) : ℕ :=
  Int.toNat (Int.floor P.beta)

def GridBudget (P : VITData) (G : ι → ℕ) : Prop :=
  (∀ i, P.g ≤ G i) ∧ (∑ i, (G i : ℝ)^2) ≤ (P.g : ℝ)^2 * P.S ∧
    (∀ i, (G i : ℝ)^2 < P.T2)

def Regular (P : VITData) (G : ι → ℕ) {d : ℕ} (L : IntLat ι d) : Prop :=
  L.mZ G * (L.H : ℝ) ≤ P.C d / (P.g : ℝ)^d

def VectorInverseStatement (P : CertifiedVITParameters)
    (G : ι → ℕ) (z : ι → ZMod P.p) : Prop :=
  GridBudget P.toVITData G → z ≠ 0 → P.theta0 < mass G (scalar G z) →
    ShortMultiple P.p z (P.B : ℝ)

end Praxis.Algebra.Inverse.Definitions
