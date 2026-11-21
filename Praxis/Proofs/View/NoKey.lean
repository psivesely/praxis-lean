import Praxis.Proofs.View.SZ
import Praxis.Domain
import Praxis.Forms
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.Forward
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

theorem view_no_formal_key (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) : ¬ FormalKey (ppOf ch S) (formVec A) D := by
  set_option maxHeartbeats 20000 in
    intro hkey
    have hid (r : Algebra.Vec (Fq P0) P0.N) :
        IdentityAtR (ppOf ch S) (formVec A) r D 1 := by
      intro c hc
      simpa only [one_mul] using hkey ⟨c, r⟩ hc
    have hzero := (view_forward ch S hS A D 0 1 (hid 0)).2 .plain keyCell
    have hone := (view_forward ch S hS A D (Pi.single 0 1) 1 (hid (Pi.single 0 1))).2 .plain keyCell
    have hcorner0 : exprStack D .plain keyCell 0 0 = 0 := by
      have h := congrFun (hone.trans hzero.symm) 0
      simpa only [Matrix.mulVec_single_one, Matrix.mulVec_zero, Matrix.col_apply, Pi.zero_apply] using h
    have hcorner1 := forward_key_corner ch S hS A D 0 1 (hid 0)
    exact zero_ne_one (hcorner0.symm.trans hcorner1)

end Praxis.Proofs.View
