import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Domain
import Praxis.Forms
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingInitial
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Reduction
import Praxis.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Source

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

lemma cover_source (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (obs : ProbComp (World (ppOf ch S)))
    (hbt : ∀ ω ∈ support obs, ∀ e, BadAt ω e →
      (e.sort = .g₁ → ∃ E : Expr1 P0, e.value = Exposure.value1 (ppOf ch S) E) ∧
      (e.sort = .g₂ → ∃ E : Expr2 P0,
        e.value = Exposure.value2 (ppOf ch S) (formVec ω.1.out.forms) E) ∧
      (e.sort = .gₜ → ∃ (D : ExprT P0) (ι : k),
        e.value = Exposure.valueT (ppOf ch S) (formVec ω.1.out.forms) D -
          ι • Exposure.valueKey (ppOf ch S)))
    (hbn : ∀ ω ∈ support obs, ∀ e, BadAt ω e → e.new ≠ e.old)
    (ω : World (ppOf ch S)) (hω : ω ∈ support obs)
    (e : Collision (ppOf ch S)) (he : BadAt ω e) (hg : GuessFree e) (hs : e.sort ≠ .gₜ) :
    ¬ IdentityAt e.value (realR ω.1) := by
  have hne : e.value ≠ 0 := by
    intro hz
    apply hbn ω hω e he
    have hd : e.diff = 0 := by rw [hg, hz, map_zero]
    exact sub_eq_zero.mp hd
  obtain ⟨h1, h2, _⟩ := hbt ω hω e he
  cases hsort : e.sort with
  | g₁ =>
    obtain ⟨E, hE⟩ := h1 hsort
    have hn : ¬ FormalEq1 (ppOf ch S) E 0 := by
      intro hf
      apply hne
      rw [hE, (Exposure.value1_eq_iff (ppOf ch S) E 0).mpr hf, map_zero]
    intro hid
    apply source1_rigid ch S E 0 hn (realR ω.1)
    intro c hc
    have hz := hid c hc
    rw [hE] at hz
    change val1 (ppOf ch S) ⟨c, realR ω.1⟩ E = 0 at hz
    simpa only [val1_zero] using hz
  | g₂ =>
    obtain ⟨E, hE⟩ := h2 hsort
    have hn : ¬ FormalEq2 (ppOf ch S) (formVec ω.1.out.forms) E 0 := by
      intro hf
      apply hne
      rw [hE, (Exposure.value2_eq_iff (ppOf ch S) _ E 0).mpr hf, map_zero]
    intro hid
    apply source2_rigid ch S hS ω.1.out.forms E 0 hn (realR ω.1)
    intro c hc
    have hz := hid c hc
    rw [hE] at hz
    change val2 (ppOf ch S) (formVec ω.1.out.forms) ⟨c, realR ω.1⟩ E = 0 at hz
    simpa only [val2_zero] using hz
  | gₜ => exact (hs hsort).elim

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Source
