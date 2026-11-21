import Praxis.Proofs.GroupModel.Init
import Praxis.Proofs.Query.Marked
import Praxis.Proofs.Sampling.Row
import Praxis.Bounds.Rank
import Praxis.Combinatorics.Mass
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Praxis.Proofs.KeyOracle
import Praxis.Proofs.Coupling.Half
import Mathlib.Tactic
import Praxis.Domain
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Relation

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 4096

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Shared

lemma prob_mono {α : Type} (c : ProbComp α) (p q : α → Prop)
    (h : ∀ a ∈ support c, p a → q a) :
    (Pr[p | c]).toReal ≤ (Pr[q | c]).toReal := by
  exact ENNReal.toReal_mono probEvent_ne_top (probEvent_mono h)

lemma bind_bound {α β : Type} (c : ProbComp α) (f : α → ProbComp β)
    (p : β → Prop) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ a ∈ support c, (Pr[p | f a]).toReal ≤ b) :
    (Pr[p | c >>= f]).toReal ≤ b := by
  have h' : Pr[p | c >>= f] ≤ ENNReal.ofReal b :=
    probEvent_bind_le_of_forall_le (fun a ha => by
      rw [← ENNReal.ofReal_toReal probEvent_ne_top]
      exact ENNReal.ofReal_le_ofReal (h a ha))
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h'
  simpa [ENNReal.toReal_ofReal hb] using hr

lemma full_marginal (ch : AdmissibleChoice P0) (S : Relation P0)
    (A : Adversary P0) (m : Msg P0) (p : WorldOut P0 → Prop) :
    Pr[fun f => p f.w | worldFull (ppOf ch S) m A extF] =
      Pr[p | worldRun (ppOf ch S) m A] := by
  exact Praxis.Proofs.Coupling.full_world_marginal (ppOf ch S) m A extF p

end Praxis.Proofs.GroupModel.Split.Shared
