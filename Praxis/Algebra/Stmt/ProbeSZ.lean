import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.NormNum.Ineq

namespace Praxis.Algebra.ProbeSZ

noncomputable def uniformProb {Ω : Type} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  (Nat.card {ω // E ω} : ℝ) / (Fintype.card Ω : ℝ)

end Praxis.Algebra.ProbeSZ
