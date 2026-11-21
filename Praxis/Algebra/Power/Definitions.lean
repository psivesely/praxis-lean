import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace Praxis.Algebra.Power

def CeilingPowerAt (L G v : ℕ) : Prop :=
  7 ≤ L → 2 ^ L ≤ G → 2 ≤ v → v < G →
    ((G + v - 1) / v) ^ L * v ^ (L - 1) ≤ G ^ L

def CeilingPower : Prop := ∀ L G v : ℕ, CeilingPowerAt L G v

def StretchEstimateAt (L n : ℕ) (G v M : ℕ → ℕ) (m : ℕ → ℝ) : Prop :=
  7 ≤ L →
  (∀ k < n, 2 ^ L ≤ G k) →
  (∀ k < n, 1 ≤ v k) →
  (∀ k < n, v k < G k) →
  (∀ k ≤ n, 0 ≤ m k) →
  (∀ k < n, m (k + 1) ≤ m k * ((((G k + v k - 1) / v k : ℕ) : ℝ) / (G k : ℝ))) →
  (∀ k < n, M (k + 1) = M k * v k) →
    (m n * (M n : ℝ)) ^ (L - 1) * m n ≤ (m 0 * (M 0 : ℝ)) ^ (L - 1) * m 0

def StretchEstimate : Prop :=
  ∀ (L n : ℕ) (G v M : ℕ → ℕ) (m : ℕ → ℝ), StretchEstimateAt L n G v M m

end Praxis.Algebra.Power
