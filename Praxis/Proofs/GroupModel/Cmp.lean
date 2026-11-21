import Praxis.Proofs.GroupModel.Init
import Praxis.Proofs.Query.Marked
import Praxis.Proofs.Sampling.Row
import Praxis.Bounds.Rank
import Praxis.Combinatorics.Mass
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Praxis.Proofs.KeyOracle
import Praxis.Proofs.GroupModel.Split.Lazy
import Praxis.Domain
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Shared
import Praxis.Relation

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

theorem gg_cmp (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S) (Q QH : ℕ)
    (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => ChargedCmp (ppOf ch S) f.w |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (ledgerCmp (simBudget Q) : ℝ) := by

  obtain ⟨events, tests, _hcharged, hcover, hdom⟩ :=
    Praxis.Proofs.GroupModel.Split.Lazy.stopped_exposure ch S hS Q QH A hA m
  rw [Praxis.Proofs.GroupModel.Split.Shared.full_marginal ch S A m (ChargedCmp (ppOf ch S))]
  exact Praxis.Proofs.GroupModel.Split.Lazy.close_stopped ch S Q A m events hcover
    (fun i j => Praxis.Proofs.GroupModel.Split.Lazy.slot_bound ch S hS m A i (events i j) (tests i j) (hdom i j))

end Praxis.Proofs.GroupModel
