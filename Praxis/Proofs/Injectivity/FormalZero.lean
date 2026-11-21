import Praxis.Proofs.View.Forward
import Praxis.Proofs.Injectivity.Projections
import Praxis.Domain
import Praxis.Extractor
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra (Vec)

theorem formalZero_stack (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (F : ExprT P0)
    (h : FormalEqT (ppOf ch S) (formVec A) F 0) : ∀ σ, exprStack F σ = 0 := by
  have hid (r : Vec (Fq P0) P0.N) : IdentityAtR (ppOf ch S) (formVec A) r F 0 := by
    intro c hc
    simpa only [View.valT_zero, zero_mul] using h ⟨c, r⟩ hc
  intro σ
  have hz := (View.view_forward ch S hS A F 0 0 (hid 0)).2
  ext c i j
  have hj := (View.view_forward ch S hS A F (Pi.single j 1) 0 (hid (Pi.single j 1))).2
  have he := congrFun ((hj σ c).trans (hz σ c).symm) i
  change exprStack F σ c i j = 0
  simpa only [Matrix.mulVec_single_one, Matrix.mulVec_zero, Matrix.col_apply,
    Pi.zero_apply] using he

theorem formalZero_sketches (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (F : ExprT P0) (sk : Sketches P0)
    (h : FormalEqT (ppOf ch S) (formVec A) F 0) : sketchesOf F sk = 0 := by
  funext l σ
  change (∑ c, (exprStack F σ c).mulVec (sk c l σ)) = 0
  simp only [formalZero_stack ch S hS A F h σ, Pi.zero_apply, Matrix.zero_mulVec,
    Finset.sum_const_zero]

end Praxis.Proofs.Injectivity
