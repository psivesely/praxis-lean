import Praxis.Proofs.GroupModel.Split.Lazy.Domination
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingDisintegration
import Praxis.Domain
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.GroupModel.Split.Shared
import Praxis.Relation

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy

open Classical

lemma stopped_exposure (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (Q QH : ℕ) (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    ∃ (events : EventsOn (WorldOut P0 × Disintegration.ObsState (ppOf ch S)) (simBudget Q))
      (tests : (i : Kind) → Fin (quota (simBudget Q) i) → ProbComp (Bounds ch S i)),
      (∀ i j ω, events i j ω → ChargedCmp (ppOf ch S) ω.1) ∧
      (∀ ω ∈ support (Disintegration.observedRun (ppOf ch S) m A), ChargedCmp (ppOf ch S) ω.1 →
        ∃ i j, events i j ω) ∧
      (∀ i j, Pr[events i j | Disintegration.observedRun (ppOf ch S) m A] ≤
        Pr[fun b => b = true | tests i j >>= Bounds.run]) := by
  suffices hparts :
      ∃ (coupling : GenericCoupling ch S (Disintegration.observedRun (ppOf ch S) m A) (simBudget Q))
        (events : EventsOn (WorldOut P0 × Disintegration.ObsState (ppOf ch S)) (simBudget Q)),
        DeterministicFold ch S (Disintegration.observedRun (ppOf ch S) m A) Prod.fst (simBudget Q)
          coupling events by
    obtain ⟨coupling, events, fold⟩ := hparts
    exact stopped_exposure_of_coupling_fold ch S (Disintegration.observedRun (ppOf ch S) m A)
      Prod.fst (simBudget Q) coupling events fold

  exact Disintegration.coupling_fold ch S m A hS Q QH hA

lemma slot_bound (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (m : Msg P0) (A : Adversary P0) (i : Kind)
    (event : WorldOut P0 × Disintegration.ObsState (ppOf ch S) → Prop)
    (tests : ProbComp (Bounds ch S i))
    (hd : Pr[event | Disintegration.observedRun (ppOf ch S) m A] ≤
      Pr[fun b => b = true | tests >>= Bounds.run]) :
    (Pr[event | Disintegration.observedRun (ppOf ch S) m A]).toReal ≤ (rate i : ℝ) := by
  exact (ENNReal.toReal_mono probEvent_ne_top hd).trans
    (Shared.bind_bound tests Bounds.run (fun b => b = true) (rate i : ℝ)
      (rate_nonneg i) (fun t _ => test_bound ch S hS i t))

lemma close_stopped (ch : AdmissibleChoice P0) (S : Relation P0)
    (Q : ℕ) (A : Adversary P0) (m : Msg P0)
    (events : EventsOn (WorldOut P0 × Disintegration.ObsState (ppOf ch S)) (simBudget Q))
    (hc : ∀ ω ∈ support (Disintegration.observedRun (ppOf ch S) m A), ChargedCmp (ppOf ch S) ω.1 →
      ∃ i j, events i j ω)
    (hb : ∀ i j, (Pr[events i j | Disintegration.observedRun (ppOf ch S) m A]).toReal ≤ (rate i : ℝ)) :
    (Pr[ChargedCmp (ppOf ch S) | worldRun (ppOf ch S) m A]).toReal ≤
      (ledgerCmp (simBudget Q) : ℝ) := by
  let idx : Type := (i : Kind) × Fin (quota (simBudget Q) i)
  generalize hobs : Disintegration.observedRun (ppOf ch S) m A = obs at hc hb
  have hcover : Pr[fun ω => ChargedCmp (ppOf ch S) ω.1 | obs] ≤
      Pr[fun ω => ∃ ij ∈ (Finset.univ : Finset idx), events ij.1 ij.2 ω | obs] := by
    apply probEvent_mono
    intro ω hω h
    obtain ⟨i,j,hij⟩ := hc ω hω h
    exact ⟨⟨i,j⟩, Finset.mem_univ _, hij⟩
  have hu := hcover.trans (probEvent_exists_finset_le_sum
    (Finset.univ : Finset idx) obs (fun ij ω => events ij.1 ij.2 ω))
  have hr := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun _ _ => probEvent_ne_top)) hu
  rw [ENNReal.toReal_sum (fun _ _ => probEvent_ne_top)] at hr
  have hlaw := Disintegration.charged_observed ch S m A
  rw [hobs] at hlaw
  calc
    _ = (Pr[fun ω => ChargedCmp (ppOf ch S) ω.1 | obs]).toReal :=
      congrArg ENNReal.toReal hlaw
    _ ≤ ∑ ij : idx, (Pr[events ij.1 ij.2 | obs]).toReal := hr
    _ ≤ ∑ ij : idx, (rate ij.1 : ℝ) := Finset.sum_le_sum (fun ij _ => hb ij.1 ij.2)
    _ = ∑ i : Kind, (allowance (simBudget Q) i : ℝ) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact_mod_cast quota_rate (simBudget Q) i
    _ = (ledgerCmp (simBudget Q) : ℝ) := by
      rw [← sum_allowance, Rat.cast_sum]

end Praxis.Proofs.GroupModel.Split.Lazy
