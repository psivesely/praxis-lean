import Praxis.Algebra.Definitions.Stack
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Int.Cast.Lemmas
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Algebra

section MSIS

def castVec {p N : ℕ} (w : Vec ℤ N) : Vec (ZMod p) N := fun i => (w i : ZMod p)

end MSIS

end Praxis.Algebra
