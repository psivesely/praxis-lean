import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Combinatorics.Mass

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.DifferenceLattice

open Finset Module Praxis.Combinatorics.Mass Praxis.Algebra.Lattice

open scoped BigOperators Matrix

variable {ι J : Type*} [Fintype ι] [DecidableEq ι]

def ival {G : ι → ℕ} (lower : ι → ℤ) (r : Grid G) (i : ι) : ℤ :=
  lower i + (r i).val

def differenceLattice {G : ι → ℕ} (lower : ι → ℤ) (F : Finset (Grid G)) :
    Submodule ℤ (ι → ℤ) :=
  Submodule.span ℤ {v | ∃ r ∈ F, ∃ r' ∈ F, v = ival lower r - ival lower r'}

variable [Fintype J] [DecidableEq J]

end Praxis.Algebra.DifferenceLattice
