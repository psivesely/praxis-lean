import Praxis.Proofs.Classification.MooreSpan
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section RowForm

variable {F : Type*} [Field F] {d : ℕ}

def rowForm (l : Fin d → F) (Q : Matrix (Fin d) (Fin d) F) : (Fin d → F) →ₗ[F] F :=
  (∑ i, l i • LinearMap.proj i) ∘ₗ Q.mulVecLin

theorem rowForm_apply (l : Fin d → F) (Q : Matrix (Fin d) (Fin d) F) (x : Fin d → F) :
    rowForm l Q x = dotProduct l (Q.mulVec x) := by
  simp only [rowForm, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, Matrix.mulVecLin_apply, dotProduct]

end RowForm

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

end

end Praxis.Proofs.Classification
