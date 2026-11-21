import Praxis.Algebra.Trans.ChartModel
import Praxis.Lift.Algebra.Trans.Definitions
import Praxis.Lift.Record
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Trans.Definitions

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

open Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Trans

namespace Praxis.Lift

namespace Algebra.Trans

open Praxis.Algebra.Trans hiding Transition32 Transition21 Transition31

namespace Chart

def Transition32 (P : VITParameters) : Prop :=
  ChartCount 3 2 → NormalPullback →
  (∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedCross3 B s) →
  (∀ n (w : Fin n → ℝ) S, ESymBounds w S) → Algebra.Trans.Transition32 P

def Transition21 (P : VITParameters) : Prop :=
  ChartCount 2 1 → NormalPullback →
  (∀ n (B : Matrix (Fin n) (Fin 2) ℝ) (s : Fin n → ℝ), WeightedAdj2 B s) →
  (∀ n (w : Fin n → ℝ) S, ESymBounds w S) → Algebra.Trans.Transition21 P

def Transition31 (P : VITParameters) : Prop :=
  ChartCount 3 1 → NormalPullback →
  (∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedPairs3 B s) →
  (∀ n (w : Fin n → ℝ) S, ESymBounds w S) → Algebra.Trans.Transition31 P

theorem transition32_compat (P : VITParameters) (h : Transition32 P)
    (hc : ChartCount 3 2) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedCross3 B s)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S) : Algebra.Trans.Transition32 P :=
  h hc hn hw he

theorem transition21_compat (P : VITParameters) (h : Transition21 P)
    (hc : ChartCount 2 1) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 2) ℝ) (s : Fin n → ℝ), WeightedAdj2 B s)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S) : Algebra.Trans.Transition21 P :=
  h hc hn hw he

theorem transition31_compat (P : VITParameters) (h : Transition31 P)
    (hc : ChartCount 3 1) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedPairs3 B s)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S) : Algebra.Trans.Transition31 P :=
  h hc hn hw he

end Chart

end Algebra.Trans

end Praxis.Lift
