import Praxis.Proofs.View.Forward
import Praxis.Proofs.View.Locus.Displacement
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Proofs.View.Locus.Rows
import Praxis.Proofs.View.Locus.Separation
import Praxis.Params
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec)

theorem view_locus (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) (r : Vec (Fq P0) P0.N) (ι : Fq P0)
    (h : IdentityAtR (ppOf ch S) (formVec A) r D ι) (r' : Vec (Fq P0) P0.N)
    (h' : ∀ σ c, (exprStack D σ c).mulVec r' = exprSC D σ c) :
    IdentityAtR (ppOf ch S) (formVec A) r' D ι := by
  have hD : ValidQAP (ppOf ch S).qap S := QAP.domainMap_valid ch S
  have hr := (view_forward ch S hS A D r ι h).2
  intro c hc
  have hm := Locus.mixingCoeff_zero (ppOf ch S) S hD (formVec A) r (expandTot D)
    (Locus.rowExpr_identity (ppOf ch S) (formVec A) r D ι h .mixing) c hc
  have hf := Locus.linearCoeff_zero (ppOf ch S) S hD (formVec A) r (expandTot D)
    (Locus.rowExpr_identity (ppOf ch S) (formVec A) r D ι h .linear) c hc
  have hg := Locus.constantCoeff_zero (ppOf ch S) (formVec A) r (expandTot D)
    (Locus.rowExpr_identity (ppOf ch S) (formVec A) r D ι h .constant) c hc
  have hd := Locus.value_displacement (ppOf ch S) (formVec A) c r r' D
  simp_rw [Locus.left_sum_reduction (ppOf ch S) c r D _ hm hf hg] at hd
  rw [Locus.stack_displacement D c r r' hr h', valT_expandTot, valT_expandTot] at hd
  rw [sub_eq_zero.mp hd]
  exact h c hc

end Praxis.Proofs.View
