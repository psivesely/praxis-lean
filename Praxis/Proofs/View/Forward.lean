import Praxis.Proofs.View.Converse
import Praxis.Proofs.View.ForwardAnalysis
import Praxis.Proofs.View.ForwardMasks
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Proofs.View.ForwardMain
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec)

theorem view_forward (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) (r : Vec (Fq P0) P0.N) (ι : Fq P0)
    (h : IdentityAtR (ppOf ch S) (formVec A) r D ι) :
    (∀ σ, PassingStack S (formVec A) (exprStack D σ)) ∧
      ∀ σ c, (exprStack D σ c).mulVec r = exprSC D σ c := by
  have hD : ValidQAP (ppOf ch S).qap S := QAP.domainMap_valid ch S
  have ha (σ : Sector) := forward_analysis (ppOf ch S) S hS hD (formVec A) r D ι h σ
  constructor
  · intro σ
    constructor
    · intro cl
      simpa only [aC_expandTot] using (ha σ).1 cl
    · have ht := mask_ties (ppOf ch S).qap (formVec A) (expandTot D) σ (ha σ).2.2.2
      simpa only [aC_expandTot] using ht
  · intro σ cl
    have hl := (ha σ).2.1 cl
    simpa only [aC_expandTot, sC_expandTot, neg_neg] using hl

theorem forward_key_corner (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) (r : Vec (Fq P0) P0.N) (ι : Fq P0)
    (h : IdentityAtR (ppOf ch S) (formVec A) r D ι) :
    exprStack D .plain keyCell 0 0 = ι := by
  have ha := forward_analysis (ppOf ch S) S hS (QAP.domainMap_valid ch S)
    (formVec A) r D ι h .plain
  have hk := ha.2.2.1 keyCell (by decide)
  simpa only [aC_expandTot, reduceCtorEq, ite_true] using hk

end Praxis.Proofs.View
