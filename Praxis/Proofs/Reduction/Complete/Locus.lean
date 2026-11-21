import Praxis.Proofs.View.Locus
import Praxis.Proofs.Reduction.Complete.Delta
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Proofs.View.Forward
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardSeparation
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Reduction

set_option maxRecDepth 4096

private theorem matrix_shift {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (W : Matrix I I F) (r x : I → F) (t : F) (hx : W.mulVec x = 0) :
    W.mulVec (r + t • x) = W.mulVec r := by
  change W.mulVecLin (r + t • x) = W.mulVecLin r
  rw [map_add, map_smul]
  change W.mulVec r + t • W.mulVec x = _
  rw [hx, smul_zero, add_zero]
  rfl

set_option maxRecDepth 4096 in
theorem identity_shift_of_zero_plain (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (D : ExprT P0)
    (r x : Algebra.Vec (Fq P0) P0.N) (ι t : Fq P0)
    (hid : IdentityAtR (ppOf ch S) (formVec A) r D ι)
    (hplain : exprStack D .plain = 0)
    (hx : ∀ c, (exprStack D .alpha c).mulVec x = 0) :
    IdentityAtR (ppOf ch S) (formVec A) (r + t • x) D ι := by
  have hf := (View.view_forward ch S hS A D r ι hid).2
  apply View.view_locus ch S hS A D r ι hid
  intro σ c
  rw [← hf σ c]
  have hz : (exprStack D σ c).mulVec x = 0 := by
    cases σ with
    | plain => simp [hplain]
    | alpha => exact hx c
  exact matrix_shift _ r x t hz

set_option maxRecDepth 4096 in
theorem gradients_orthogonal_of_identity (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (D : ExprT P0)
    (r x : Algebra.Vec (Fq P0) P0.N) (ι : Fq P0)
    (hid : IdentityAtR (ppOf ch S) (formVec A) r D ι)
    (hplain : exprStack D .plain = 0)
    (hx : ∀ cl, (exprStack D .alpha cl).mulVec x = 0)
    (c : Coins P0) (hc : ValidCoins (ppOf ch S).qap c) :
    ∑ j, (rGrad (ppOf ch S) ⟨c, r⟩ D .plain j +
      rGrad (ppOf ch S) ⟨c, r⟩ D .alpha j) * x j = 0 := by
  have hid' : IdentityAtR (ppOf ch S) (formVec A) (r + x) D ι := by
    simpa only [one_smul] using
      identity_shift_of_zero_plain ch S hS A D r x ι 1 hid hplain hx
  have hd := valT_sub_gradient (ppOf ch S) (formVec A) c r (r + x) D
  rw [hid' c hc, hid c hc, sub_self] at hd
  simpa only [Pi.add_apply, add_sub_cancel_left] using hd.symm

theorem plain_projection_stack (D : ExprT P0) (σ : Sector) :
    exprStack (View.project .alpha 2 D) σ =
      if σ = .plain then exprStack D .plain else 0 := by
  cases σ <;> funext cl i j <;>
    simp [exprStack, View.project, View.restrictW, View.ViewScale.weight1,
      View.ViewScale.weight2, View.ViewScale.weightT, View.g2Sector]

theorem plain_projection_gradient (pp : PublicParams P0) (ω : Assign P0) (D : ExprT P0) :
    rGrad pp ω (View.project .alpha 2 D) .plain = rGrad pp ω D .plain := by
  funext j
  simp [rGrad, View.project, View.restrictW, View.ViewScale.weight1,
    View.ViewScale.weight2, View.ViewScale.weightT, View.g2Sector]

theorem alpha_projection_gradient (pp : PublicParams P0) (ω : Assign P0) (D : ExprT P0) :
    rGrad pp ω (View.project .alpha 2 D) .alpha = 0 := by
  funext j
  simp [rGrad, View.project, View.restrictW, View.ViewScale.weight1,
    View.ViewScale.weight2, View.ViewScale.weightT, View.g2Sector]

theorem plain_gradient_orthogonal_valid (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (D : ExprT P0)
    (r x : Algebra.Vec (Fq P0) P0.N) (ι : Fq P0)
    (hid : IdentityAtR (ppOf ch S) (formVec A) r D ι)
    (hplain : exprStack D .plain = 0)
    (c : Coins P0) (hc : ValidCoins (ppOf ch S).qap c) :
    ∑ j, rGrad (ppOf ch S) ⟨c, r⟩ D .plain j * x j = 0 := by
  let E := View.project .alpha 2 D
  have hidE : IdentityAtR (ppOf ch S) (formVec A) r E ι := by
    have h := View.project_identity .alpha (by decide) (ppOf ch S) (formVec A) r D ι hid 2
    simpa [E, View.ViewScale.weightK] using h
  have hEplain : exprStack E .plain = 0 := by
    simpa [E, plain_projection_stack] using hplain
  have hEalpha : exprStack E .alpha = 0 := by
    simp [E, plain_projection_stack]
  have h := gradients_orthogonal_of_identity ch S hS A E r x ι hidE hEplain
    (by intro cl; simp [hEalpha]) c hc
  simpa only [E, plain_projection_gradient, alpha_projection_gradient, Pi.zero_apply, add_zero] using h

end Praxis.Proofs.Reduction
