import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GaussianMoment
import Praxis.Algebra.TrimAnalysis.NumericTrim

set_option autoImplicit false

set_option linter.style.haveILetI false

set_option linter.unusedSectionVars false

noncomputable section

open Finset Real Matrix

open scoped BigOperators

namespace Praxis.Analysis

abbrev Grid {ι : Type*} (G : ι → ℕ) := (i : ι) → Fin (G i)

variable {Ω : Type*} [Fintype Ω]

def FiniteLaw.uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel₀ 1 (by exact_mod_cast Fintype.card_ne_zero)

def FiniteLaw.mean {d : ℕ} (P : FiniteLaw Ω) (X : Ω → Fin d → ℝ) : Fin d → ℝ :=
  fun j => P.expect (fun s => X s j)

structure SubGaussianImage (d : ℕ) where
  sample : Type
  finite : Fintype sample
  law : @FiniteLaw sample finite
  image : sample → Fin d → ℝ
  sigma : Matrix (Fin d) (Fin d) ℝ
  positive : sigma.PosDef
  directional : @DirectionalMGF sample finite d law image
    (@FiniteLaw.mean sample finite d law image) sigma

attribute [instance] SubGaussianImage.finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gridLaw (G : ι → ℕ) (hG : ∀ i, 0 < G i) : FiniteLaw (Grid G) := by
  letI : Nonempty (Grid G) := ⟨fun i => ⟨0, hG i⟩⟩
  exact FiniteLaw.uniform (Grid G)

def gridImage {d : ℕ} (G : ι → ℕ) (B : Matrix ι (Fin d) ℝ)
    (r : Grid G) : Fin d → ℝ := fun j => ∑ i, B i j * ((r i : ℕ) : ℝ)

def gridCovariance {d : ℕ} (G : ι → ℕ) (B : Matrix ι (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun j k => ∑ i, (G i : ℝ)^2 / 12 * B i j * B i k

structure GridImage (d : ℕ) (G : ι → ℕ) (B : Matrix ι (Fin d) ℝ) where
  grid_pos : ∀ i, 0 < G i
  sigma_pos : (gridCovariance G B).PosDef

namespace GridImage

variable {d : ℕ} {G : ι → ℕ} {B : Matrix ι (Fin d) ℝ}

def law (T : GridImage d G B) : FiniteLaw (Grid G) := gridLaw G T.grid_pos

def center (T : GridImage d G B) : Fin d → ℝ := T.law.mean (gridImage G B)

def DirectionalMGF (T : GridImage d G B) : Prop :=
  Analysis.DirectionalMGF T.law (gridImage G B) T.center (gridCovariance G B)

def ellipsoid (T : GridImage d G B) (R : ℝ) : Set (Grid G) :=
  {r | mahalanobisSq (gridCovariance G B) T.center (gridImage G B r) ≤ R^2}

def probOutsideEllipsoid (T : GridImage d G B) (R : ℝ) : ℝ :=
  T.law.prob (T.ellipsoid R)ᶜ

end GridImage

end Praxis.Analysis
