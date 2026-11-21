import Praxis.Proofs.Injectivity.Span
import Praxis.Proofs.Injectivity.Operations
import Praxis.Proofs.Injectivity.FormalZero
import Praxis.Domain
import Praxis.Extractor
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting

namespace Praxis.Proofs.Injectivity

theorem jse_book (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (w : WorldOut P0) (sk : Sketches P0) (D : ExprT P0) (ι : Fq P0)
    (hgood : GoodMark (ppOf ch S) w D ι) (hnone : extractWith S w.out.pv w.st.tr sk = none) :
    testExpr S (sketchesOf D sk) = none := by
  obtain ⟨k, hm, hd, _⟩ := hgood
  refine monitor_book S sk (idealCtx (ppOf ch S) w) ?_
    w.out.pv w.st.tr w.st.kdfLog k D ι hm hd hnone ?_
  · intro kl hkl
    simp only [idealCtx, List.mem_cons, List.not_mem_nil, or_false] at hkl
    rcases hkl with rfl | rfl <;> simp
  · intro F hF
    exact formalZero_sketches ch S hS w.out.forms F sk hF

end Praxis.Proofs.Injectivity
