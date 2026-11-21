import Praxis.Proofs.View.SZ.Eval
import Praxis.Proofs.View.SZ.Bound
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Proofs.View.SZ.Model
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View.SZ

open Praxis.Algebra (Vec)

open Classical

theorem differenceP_ne_zero (ch : AdmissibleChoice P0) (S : Relation P0)
    (A : FormMatrix P0) (D : ExprT P0) (r : Vec (Fq P0) P0.N) (ι : Fq P0)
    (h : ¬ IdentityAtR (ppOf ch S) (formVec A) r D ι) :
    differenceP (ppOf ch S) (formVec A) r D ι ≠ 0 := by
  unfold IdentityAtR at h
  push Not at h
  obtain ⟨c, hc, hn⟩ := h
  intro hp
  have he := eval_differenceP (ppOf ch S) c (formVec A) r D ι hc
  rw [hp, map_zero] at he
  have hd := denom_ne_zero (ppOf ch S).qap c hc
  exact hn (sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hd))

end Praxis.Proofs.View.SZ
