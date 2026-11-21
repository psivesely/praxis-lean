import Praxis.Algebra.Definitions.Relation
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Praxis.Algebra

section Cells

abbrev Cell (d rows : ℕ) := Fin (d + 1) × Fin rows

abbrev Stack (F : Type*) (N d rows : ℕ) := Cell d rows → Mat F N

variable {d rows : ℕ} [NeZero rows]

def IsBlock (k : Cell d rows) : Prop := k.1 ≠ 0 ∨ k.2 = 0

end Cells

section StackOps

variable {F : Type*} {N d rows : ℕ}

def stackRows (W : Stack F N d rows) : (Cell d rows × Fin (N + 1)) → Vec F N :=
  fun ki j => W ki.1 ki.2 j

def stackSpace [Field F] (W : Stack F N d rows) : Submodule F (Vec F N) :=
  Submodule.span F (Set.range (stackRows W))

noncomputable def stackRank [Field F] (W : Stack F N d rows) : ℕ :=
  Module.finrank F (stackSpace W)

variable [NeZero rows]

end StackOps

section Forms

def e0 {F : Type*} [Zero F] [One F] {N : ℕ} : Vec F N :=
  fun i => if i = 0 then 1 else 0

end Forms

end Praxis.Algebra
