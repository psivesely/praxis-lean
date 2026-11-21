import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Disintegration

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

attribute [local implicit_reducible] SetM

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.NotMono

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0)

def Ordered (st : ObsState pp) : Prop :=
  st.steps.Pairwise (fun a b => a.order <+: b.order) ∧
    ∀ s ∈ st.steps, s.order <+: st.order

lemma ordered_append (st : ObsState pp) (hst : Ordered pp st)
    (oracle : OracleState P0) (shadow : State pp) (order : List GuessVar)
    (stop : Option ℕ) (entry : Entry) (hpre : st.order <+: order) :
    Ordered pp ⟨oracle, shadow, order, st.steps ++ [⟨entry, shadow, order⟩], stop⟩ := by
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨hst.1, by simp, ?_⟩
    intro s hs t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact (hst.2 s hs).trans hpre
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact (hst.2 s hs).trans hpre
    · simp only [List.mem_singleton] at hs
      subst s
      exact List.prefix_refl _

lemma ordered_step (σ : LabelEncoding P0) (c : Coins P0)
    (q : (AdvModel P0).Domain) (st : ObsState pp) (hst : Ordered pp st) :
    ∀ y ∈ support ((obsHandler pp σ c q).run st), Ordered pp y.2 := by
  intro y hy
  rcases q with ((n | gq) | i) | kq
  all_goals
    simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨z, _, rfl⟩ := hy
    apply ordered_append pp st hst
  · exact List.prefix_refl _
  · exact List.prefix_append _ _
  · exact List.prefix_refl _
  · exact List.prefix_refl _

lemma ordered_run (σ : LabelEncoding P0) (c : Coins P0) {α : Type}
    (oa : OracleComp (AdvModel P0) α) (st : ObsState pp) (hst : Ordered pp st) :
    ∀ y ∈ support ((simulateQ (obsHandler pp σ c) oa).run st), Ordered pp y.2 :=
  simulateQ_run_preserves_inv_of_query (obsHandler pp σ c) (Ordered pp)
    (ordered_step pp σ c) oa st hst

lemma mono_of_pairwise (r : Record pp) (hp : r.pendingOrder = none)
    (h : r.steps.Pairwise (fun a b => a.order <+: b.order)) : Simulation.RMono pp r := by
  intro s hs
  simpa only [Record.order, hp, Option.getD_none, Record.lastOrder,
    List.getLast?_eq_some_getLast (List.ne_nil_of_mem hs),
    Option.map_some, Option.getD_some] using
    h.rel_getLast_of_rel_getLast_getLast hs (List.prefix_refl _)

lemma mono_cut (R : FullRecord pp) (n : ℕ)
    (h : R.steps.Pairwise (fun a b => a.order <+: b.order)) : Simulation.RMono pp (R.cut n) := by
  cases hn : R.steps[n]? with
  | none =>
    apply mono_of_pairwise pp (R.cut n) (by simp only [FullRecord.cut, hn, Option.map_none])
    exact h.take
  | some t =>
    intro s hs
    have hp : (R.cut n).pendingOrder = some t.order := by
      simp only [FullRecord.cut, hn, Option.map_some]
    have hs' : s ∈ R.steps.take n := hs
    have ht : t ∈ R.steps.drop n := by
      rw [List.mem_iff_getElem?]
      exact ⟨0, by simpa only [List.getElem?_drop, Nat.add_zero] using hn⟩
    have hpw := h
    rw [← List.take_append_drop n R.steps, List.pairwise_append] at hpw
    rw [Record.order, hp, Option.getD_some]
    exact hpw.2.2 s hs' t ht

lemma not_mono_proof [Nonempty {c : Coins P0 // ValidCoins pp.qap c}]
    (m : Msg P0) (A : Adversary P0) (n : ℕ) (r : Record pp)
    (c : CoinDomain pp) (x : ℕ → k) (hr : ¬ Simulation.RMono pp r) :
    Pr[fun ω => Clean n ω ∧ (fullRecord ω).cut n = r ∧ ω.1.out.coins = c.val ∧
        guessValues r ω = x | observedRun pp m A] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro ω hω he
  have hordered : Ordered pp ω.2 := by
    clear he hr c x r
    unfold observedRun at hω
    rw [mem_support_bind_iff] at hω
    obtain ⟨σ, _, hω⟩ := hω
    rw [mem_support_bind_iff] at hω
    obtain ⟨e, _, hω⟩ := hω
    rw [mem_support_bind_iff] at hω
    obtain ⟨z, hz, hω⟩ := hω
    simp only [support_pure, Set.mem_singleton_iff] at hω
    rw [hω]
    exact ordered_run pp σ e.1.coins (A.run e.1.pv e.1.header) _
      ⟨by simp, by simp⟩ z hz
  have hlog : ω.2.steps.Pairwise (fun a b => a.order <+: b.order) := hordered.1
  have hmono := mono_cut pp (fullRecord ω) n hlog
  exact hr (he.2.1 ▸ hmono)

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.NotMono
