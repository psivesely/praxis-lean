import Praxis.Algebra.Mod.Definitions
import Praxis.Lift.Record
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation

set_option autoImplicit false

noncomputable section

namespace Praxis.Lift

namespace Algebra.Mod.Definitions

open Finset Module

open Praxis.Algebra.Inverse.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

def FullImageExclusion (d : ℕ) (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι d) (c : Option (Fin d) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) : Prop :=
  1 ≤ d → d ≤ 3 → GridBudget P.toVITData (extend G Gx) →
    Regular P.toVITData G L → c ≠ 0 → F.Nonempty →
    (∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t) →
    Trimmed P.toVITData G Gx L.matrix F →
    Analysis.rationalRank (imageDifferences (stepImage G Gx L.matrix) F) = d+1 →
    Nat.card ((Option (Fin d) → ℤ) ⧸ congruenceKernel P.p c) = P.p ∧
    (∃ y : Option (Fin d) → ℤ, ∀ r ∈ F,
      stepImage G Gx L.matrix r - y ∈ congruenceKernel P.p c) ∧
    density F ≤ wrapFactor P.toVITData d * P.toVITData.C d / (P.p : ℝ) ∧
    wrapFactor P.toVITData d * P.toVITData.C d / (P.p : ℝ) < P.toVITData.mu

def SaturationApplication (d : ℕ) (P : VITParameters) (n : Fin d → ℕ)
    (T : ℝ) (D : Matrix (Option (Fin d)) κ ℤ) : Prop :=
  1 ≤ d → d ≤ 3 → (∀ j, 1 ≤ n j) →
    (∏ j, (n j : ℝ)) ≤ basisConstant d * heightBound P.toVITData d →
    1 ≤ T → T^2 ≤ P.toVITData.T2 →
    (∀ j k, |(D (some j) k : ℝ)| ≤ T * n j) →
    (∀ k, |(D none k : ℝ)| ≤ T) →
    ∀ e : ℕ, e ≤ d → ∀ (I : Fin e → Option (Fin d)) (J : Fin e → κ),
      (|(D.submatrix I J).det| : ℝ) ≤ minorBound P.toVITData d T ∧
      |(D.submatrix I J).det| < (P.p : ℤ)

def ModStep (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (z : ι → ZMod P.p) (a : ZMod P.p) : Prop :=
  GridBudget P.toVITData (extend G Gx) → z ≠ 0 →
    P.theta0 < mass (extend G Gx) (scalar (extend G Gx) (extend z a)) →
    ∀ d : ℕ, ∀ L : IntLat ι d, RegularWitness P.toVITData G z d L →
      ∃ q : ℕ, ∃ N : IntLat (Option ι) q,
        RegularWitness P.toVITData (extend G Gx) (extend z a) q N

def ModularRegularization (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) : Prop :=
  GridBudget P.toVITData G → z ≠ 0 → P.theta0 < mass G (scalar G z) →
    ∃ d : ℕ, ∃ L : IntLat ι d, RegularWitness P.toVITData G z d L

end Algebra.Mod.Definitions

end Praxis.Lift

end
