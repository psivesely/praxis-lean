import Praxis.Algebra.Reg.Rank1Model
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Record
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

namespace Praxis.Lift

namespace Algebra.Reg.Rank1Model

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Prefix.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Rank1Model hiding Rank1Promotion Rank1Return21 Rank1Return31 Rank1NestedCall

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Rank1Promotion (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 1)
    (t : Fin 1 → ℤ) (F : Finset (Grid G)) : Prop :=
  GridBudget P.toVITData G →
  atom G (imageZ G L.matrix) t = L.mZ G →
  F.Nonempty → F ⊆ ordinaryFibre G L t →
  L.mZ G - P.eps ≤ density G F → P.toVITData.mu ≤ density G F →
  (Module.finrank ℤ (ordinaryNormals G F) = 2 ∨
    Module.finrank ℤ (ordinaryNormals G F) = 3 ∨
    ∃ (i : ι) (a : ℤ), (∀ r ∈ F, ((r i : ℕ) : ℤ) = a) ∧
      Pi.single i 1 ∉ L.carrier) →
  (∃ L2 : IntLat ι 2, L.carrier ≤ L2.carrier ∧
    L.mZ G - P.eps ≤ L2.mZ G) ∨
  (∃ L3 : IntLat ι 3, L.carrier ≤ L3.carrier ∧
    L.mZ G - P.eps ≤ L3.mZ G ∧
    (L3.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G L3)

def Rank1Return21 (P : VITParameters) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G2 : ι → ℕ) (L2 : IntLat ι 2)
    (G1 : κ → ℕ) (L1 : IntLat κ 1) (trimmedDensity : ℝ) : Prop :=
  P.toVITData.mu ≤ L1.mZ G1 →
  L1.mZ G1 - P.eps ≤ trimmedDensity →
  Regular P.toVITData G2 L2 →
  trimmedDensity * (L1.H : ℝ) ≤
    P.D * (P.g : ℝ) * (L2.H : ℝ) * L2.mZ G2 →
  L1.mZ G1 * (L1.H : ℝ) ≤ P.A * P.D * P.C2 / (P.g : ℝ)

def Rank1Return31 (P : VITParameters) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G3 : ι → ℕ) (L3 : IntLat ι 3)
    (G1 : κ → ℕ) (L1 : IntLat κ 1) (trimmedDensity : ℝ) : Prop :=
  P.toVITData.mu ≤ L1.mZ G1 →
  L1.mZ G1 - P.eps ≤ trimmedDensity →
  Regular P.toVITData G3 L3 →
  trimmedDensity * (L1.H : ℝ) ≤
    P.E * (P.g : ℝ)^2 * (L3.H : ℝ) * L3.mZ G3 →
  L1.mZ G1 * (L1.H : ℝ) ≤ P.A * P.E * P.C3 / (P.g : ℝ)

def Rank1NestedCall (P : VITParameters) (G : ι → ℕ)
    (L1 : IntLat ι 1) (L2 : IntLat ι 2) : Prop :=
  GridBudget P.toVITData G → P.theta0 - 20 * P.eps ≤ L1.mZ G →
  L1.carrier ≤ L2.carrier → L1.mZ G - P.eps ≤ L2.mZ G →
  Regularize2 P G L2 →
  P.theta0 - 30 * P.eps ≤ L2.mZ G ∧
    ((∃ M2 : IntLat ι 2, L1.carrier ≤ M2.carrier ∧
      L1.mZ G - 2 * P.eps ≤ M2.mZ G ∧ Regular P.toVITData G M2) ∨
     (∃ M3 : IntLat ι 3, L1.carrier ≤ M3.carrier ∧
      L1.mZ G - 2 * P.eps ≤ M3.mZ G ∧
      (M3.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G M3))

end Algebra.Reg.Rank1Model

end Praxis.Lift
