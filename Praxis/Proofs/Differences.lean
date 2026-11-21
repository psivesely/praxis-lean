import Praxis.Proofs.View.NoKey
import Praxis.Proofs.Rank4
import Praxis.Domain
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.View.Forward
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Stack

namespace Praxis.Proofs.Differences

theorem good_mark_passing (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (w : WorldOut P0) (D : ExprT P0) (ι : Fq P0) (h : GoodMark (ppOf ch S) w D ι) :
    (∀ σ, PassingStack S (formsOfRun w) (exprStack D σ)) ∧
      PassingStack S (formsOfRun w) (markStack D) ∧ (∀ c, (markStack D c).IsSymm) ∧
      Module.finrank (Fq P0) (jointSpace (markStack D)) ≤ dimMax := by
  obtain ⟨k, hk, hdata, hid, hnz, hheavy⟩ := h
  have hpass :=
    (Praxis.Proofs.View.view_forward ch S hS w.out.forms D (realR w) ι hid).1
  have hmark : PassingStack S (formsOfRun w) (markStack D) :=
    hpass (markSector D)
  have hsym : ∀ c, (markStack D c).IsSymm := fun c => (hmark.1 c).1
  exact ⟨hpass, hmark, hsym,
    (Praxis.Proofs.Rank4.finrank_jointSpace (markStack D) hsym).2 hheavy⟩

end Praxis.Proofs.Differences
