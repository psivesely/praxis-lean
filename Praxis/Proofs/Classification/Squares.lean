import Praxis.Proofs.Classification.Frame

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {k : Type*} [Field k] {I : Type*} [Fintype I] [DecidableEq I]

def matrixEntry (i j : I) : Matrix I I k →ₗ[k] k :=
  (LinearMap.proj j) ∘ₗ (LinearMap.proj i)

@[simp] theorem matrixEntry_apply (i j : I) (M : Matrix I I k) : matrixEntry i j M = M i j := rfl

end

end

end Praxis.Proofs.Classification
