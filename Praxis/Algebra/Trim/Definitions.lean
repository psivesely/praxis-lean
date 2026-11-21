import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.GaussianMoment
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation
import Mathlib.Algebra.Order.Star.Real
import Praxis.Algebra.TrimAnalysis.NumericTrim

set_option autoImplicit false

noncomputable section

open Finset Matrix Praxis.Analysis

open scoped BigOperators

namespace Praxis.Algebra.Trim

def SinhDivLeExp : Prop :=
  ∀ y : ℝ, y ≠ 0 → Real.sinh y / y ≤ Real.exp (y ^ 2 / 6)

def uniformGridMoment (G : ℕ) (t : ℝ) : ℝ :=
  (∑ k : Fin G, Real.exp (t * (((k : ℕ) : ℝ) - ((G : ℝ) - 1) / 2))) / G

def UniformGridMGF : Prop :=
  ∀ (G : ℕ), 0 < G → ∀ t : ℝ,
    uniformGridMoment G t ≤ Real.exp (t ^ 2 * (G : ℝ) ^ 2 / 24)

def GridDirectionalMGF : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (G : ι → ℕ) (hG : ∀ i, 0 < G i) (B : Matrix ι (Fin d) ℝ),
    Analysis.DirectionalMGF (gridLaw G hG) (gridImage G B)
      ((gridLaw G hG).mean (gridImage G B)) (gridCovariance G B)

def TrimForIntLat : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (G : ι → ℕ) (_hG : ∀ i, 0 < G i) (B : Matrix ι (Fin d) ℤ),
    (1 ≤ d ∧ d ≤ 3) → LinearIndependent ℤ B.col →
    ∃ T : GridImage d G (B.map (Int.castRingHom ℝ)),
      T.probOutsideEllipsoid 20 ≤ (2 : ℝ) ^ (-(270 : ℤ)) ∧
      ∀ E : Set (Grid G),
        T.law.prob E - (2 : ℝ) ^ (-(270 : ℤ)) ≤
          T.law.prob (E ∩ T.ellipsoid 20)

end Praxis.Algebra.Trim
