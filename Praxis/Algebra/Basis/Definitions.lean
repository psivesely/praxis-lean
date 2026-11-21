import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Conversion.L1Minkowski

noncomputable section

open Module MeasureTheory

open scoped BigOperators Matrix Pointwise

namespace Praxis.Algebra.Basis

open Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

def MaximalPivot {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (B : Matrix ι (Fin d) ℤ) (P : Fin d → ι) : Prop :=
  Function.Injective P ∧ (B.submatrix P id).det ≠ 0 ∧
    ∀ Q : Fin d → ι, (B.submatrix Q id).det.natAbs ≤ (B.submatrix P id).det.natAbs

def PivotProjectionBound : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (B : Matrix ι (Fin d) ℤ) (P : Fin d → ι), MaximalPivot B P →
    ∀ y : Fin d → ℝ,
      ‖(B.map (fun z => (z : ℝ))) *ᵥ y‖ ≤
        HeavyStack.l1 (((B.submatrix P id).map (fun z => (z : ℝ))) *ᵥ y)

def J (d : ℕ) : ℕ := if d = 1 then 1 else if d = 2 then 2 else if d = 3 then 9 else 0

def ControlledBasis (d : ℕ) : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (L : IntLat ι d),
    1 ≤ d → d ≤ 3 → ∃ b : Module.Basis (Fin d) ℤ L.carrier,
      (∏ j, (maxAbs (b j : ι → ℤ) : ℝ)) ≤ (J d : ℝ) * (L.H : ℝ)

end Praxis.Algebra.Basis
