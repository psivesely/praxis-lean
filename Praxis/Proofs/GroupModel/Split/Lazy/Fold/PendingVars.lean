import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.PendingVars

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

variable (pp : PublicParams P0)

private def FirstVars (st : State pp) : Prop :=
  ∀ e, st.first = some e → ∀ v ∈ e.diff.vars, v ∈ st.guesses

private lemma resolve_firstVars (σ : LabelEncoding P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (h : FirstVars pp st) :
    FirstVars pp (resolve pp σ st s l).2 := by
  obtain ⟨hf, _, hg, _⟩ := resolve_props pp σ st s l
  intro e he v hv
  exact hg v (h e (hf ▸ he) v hv)

private lemma insertResult_firstVars (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp)
    (h : FirstVars pp st)
    (hd : ∀ s l P, st.dict s l = some P → ∀ v ∈ P.vars, v ∈ st.guesses)
    (hP : ∀ v ∈ P.vars, v ∈ st.guesses) :
    FirstVars pp (insertResult pp st s l P) := by
  intro e he v hv
  rw [insertResult_guesses]
  unfold insertResult at he
  cases hQ : st.dict s l with
  | none => exact h e (by simpa only [hQ] using he) v hv
  | some Q =>
    simp only [hQ] at he
    split_ifs at he with hPQ
    · exact h e he v hv
    · cases hf : st.first with
      | some e' =>
        simp only [hf, Option.orElse_some, Option.some.injEq] at he
        subst e'
        exact h e hf v hv
      | none =>
        simp only [hf, Option.orElse_none, Option.some.injEq] at he
        subst e
        rcases Finset.mem_union.mp (MvPolynomial.vars_sub_subset _ hv) with hv | hv
        · exact hP v hv
        · exact hd s l Q hQ v hv

private lemma observeGroup_firstVars (σ : LabelEncoding P0) (st : State pp)
    (gq : GQuery P0) (R : gq.Result) (hs : ShInv pp σ st) (h : FirstVars pp st) :
    FirstVars pp (observeGroup pp σ st gq R) := by
  have hsum : ∀ (a b : k) (P Q : Poly pp) (G : Finset GuessVar),
      (∀ v ∈ P.vars, v ∈ G) → (∀ v ∈ Q.vars, v ∈ G) →
      ∀ v ∈ (scalar pp a * P + scalar pp b * Q).vars, v ∈ G := by
    intro a b P Q G hP hQ v hv
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with hv | hv
    · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
      · simp [scalar] at hv
      · exact hP v hv
    · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
      · simp [scalar] at hv
      · exact hQ v hv
  cases gq with
  | lin s a b u v =>
    obtain ⟨hx, hxv⟩ := resolve_shInv pp σ st s u hs
    obtain ⟨hy, hyv⟩ := resolve_shInv pp σ (resolve pp σ st s u).2 s v hx
    have hf := resolve_firstVars pp σ (resolve pp σ st s u).2 s v
      (resolve_firstVars pp σ st s u h)
    have hg := (resolve_props pp σ (resolve pp σ st s u).2 s v).2.2.1
    simp only [observeGroup]
    cases hP : (resolve pp σ st s u).1 with
    | none => exact hf
    | some P =>
      cases hQ : (resolve pp σ (resolve pp σ st s u).2 s v).1 with
      | none => exact hf
      | some Q =>
        cases R with
        | none => exact hf
        | some l =>
          exact insertResult_firstVars pp _ s l _ hf hy.1
            (hsum a b P Q _ (fun w hw => hg w (hxv P hP w hw)) (hyv Q hQ))
  | pair u v =>
    obtain ⟨hx, hxv⟩ := resolve_shInv pp σ st .g₁ u hs
    obtain ⟨hy, hyv⟩ := resolve_shInv pp σ (resolve pp σ st .g₁ u).2 .g₂ v hx
    have hf := resolve_firstVars pp σ (resolve pp σ st .g₁ u).2 .g₂ v
      (resolve_firstVars pp σ st .g₁ u h)
    have hg := (resolve_props pp σ (resolve pp σ st .g₁ u).2 .g₂ v).2.2.1
    simp only [observeGroup]
    cases hP : (resolve pp σ st .g₁ u).1 with
    | none => exact hf
    | some P =>
      cases hQ : (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).1 with
      | none => exact hf
      | some Q =>
        cases R with
        | none => exact hf
        | some l =>
          apply insertResult_firstVars pp _ .gₜ l _ hf hy.1
          intro w hw
          rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hw) with hw | hw
          · exact hg w (hxv P hP w hw)
          · exact hyv Q hQ w hw
  | name u =>
    simp only [observeGroup]
    cases R with
    | none => exact h
    | some nm =>
      apply insertResult_firstVars pp _ .gₜ _ _ h hs.1
      intro v hv
      rw [MvPolynomial.vars_neg] at hv
      cases hu : st.dict .gₜ u with
      | none => simp [hu] at hv
      | some P => exact hs.1 .gₜ u P hu v (by simpa [hu] using hv)

private lemma fold_initial (σ : LabelEncoding P0)
    (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp)
    (hs : ShInv pp σ st) (hf : FirstVars pp st) (hg : st.guesses = ∅)
    (he : ∀ e ∈ es, e.2.2.vars = ∅) :
    let sh := es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st
    ShInv pp σ sh ∧ FirstVars pp sh ∧ sh.guesses = ∅ := by
  induction es generalizing st with
  | nil => exact ⟨hs, hf, hg⟩
  | cons e es ih =>
    have hP : ∀ v ∈ e.2.2.vars, v ∈ st.guesses := by
      intro v hv
      rw [he e (by simp)] at hv
      exact False.elim (Finset.notMem_empty v hv)
    exact ih _ (insertResult_shInv pp σ st _ _ _ hs hP)
      (insertResult_firstVars pp st _ _ _ hf hs.1 hP)
      (by rw [insertResult_guesses, hg])
      (fun e' he' => he e' (List.mem_cons_of_mem e he'))

private lemma initialise_invariants (σ : LabelEncoding P0) (A : FormMatrix P0)
    (pv : PubView P0) :
    ShInv pp σ (initialise pp A pv) ∧ FirstVars pp (initialise pp A pv) ∧
      (initialise pp A pv).guesses = ∅ := by
  apply fold_initial pp σ
  · refine ⟨?_, ?_, ?_⟩ <;> simp [empty]
  · intro e he
    simp [empty] at he
  · rfl
  · intro e he
    simp only [initialEntries, List.mem_append, List.mem_map] at he
    rcases he with (⟨x, _, rfl⟩ | ⟨x, _, rfl⟩) | ⟨x, _, rfl⟩ <;>
      simp [base1, base2, baseT]

private def Current (σ : LabelEncoding P0) (sh : State pp) (O : List GuessVar) : Prop :=
  ShInv pp σ sh ∧ (∀ v ∈ sh.guesses, v ∈ O) ∧ FirstVars pp sh

private def Logged (s : Step pp) : Prop :=
  VarsIn pp ⟨OracleState.empty, s.shadow, s.order, []⟩ ∧
    ∀ e, s.shadow.first = some e → e.diff.vars ⊆ s.order.toFinset

private lemma current_logged (σ : LabelEncoding P0) (sh : State pp) (O : List GuessVar)
    (h : Current pp σ sh O) (entry : Entry) : Logged pp ⟨entry, sh, O⟩ := by
  constructor
  · intro s l P hP v hv
    exact h.2.1 v (h.1.1 s l P hP v hv)
  · intro e he v hv
    exact List.mem_toFinset.mpr (h.2.1 v (h.2.2 e he v hv))

private lemma current_group (σ : LabelEncoding P0) (sh : State pp) (O : List GuessVar)
    (h : Current pp σ sh O) (gq : GQuery P0) (R : gq.Result) :
    Current pp σ (observeGroup pp σ sh gq R)
      (O ++ newGuesses pp sh (observeGroup pp σ sh gq R) gq) := by
  obtain ⟨hs, _, hn⟩ := observeGroup_shInv pp σ sh gq R h.1
  refine ⟨hs, ?_, observeGroup_firstVars pp σ sh gq R h.1 h.2.2⟩
  intro v hv
  rcases hn v hv with hv | hv
  · exact List.mem_append_left _ (h.2.1 v hv)
  · exact List.mem_append_right _ hv

private def RunInv (σ : LabelEncoding P0) (st : ObsState pp) : Prop :=
  Current pp σ st.shadow st.order ∧ ∀ s ∈ st.steps, Logged pp s

private lemma obs_step_inv (σ : LabelEncoding P0) (c : Coins P0)
    (q : (AdvModel P0).Domain) (st : ObsState pp) (h : RunInv pp σ st) :
    ∀ y ∈ support ((obsHandler pp σ c q).run st), RunInv pp σ y.2 := by
  intro y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨z, _, rfl⟩ := hy
  have hlog (entry : Entry) (sh : State pp) (O : List GuessVar)
      (hc : Current pp σ sh O) :
      ∀ s ∈ st.steps ++ [⟨entry, sh, O⟩], Logged pp s := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact h.2 s hs
    · cases List.mem_singleton.mp hs
      exact current_logged pp σ _ _ hc _
  rcases q with ((n | gq) | i) | kq
  · exact ⟨h.1, hlog _ _ _ h.1⟩
  · have hc := current_group pp σ st.shadow st.order h.1 gq
      (groupAnswer σ st.oracle.issuedT gq)
    exact ⟨hc, hlog _ _ _ hc⟩
  · exact ⟨h.1, hlog _ _ _ h.1⟩
  · exact ⟨h.1, hlog _ _ _ h.1⟩

private lemma observed_logged [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0)
    (obs : ProbComp (World pp)) (hobs : observedRun pp m A = obs)
    (ω : World pp) (hω : ω ∈ support obs) : ∀ s ∈ ω.2.steps, Logged pp s := by
  rw [← hobs] at hω
  simp only [observedRun, support_bind, Set.mem_iUnion, support_pure,
    Set.mem_singleton_iff] at hω
  obtain ⟨σ, _, e, _, z, hz, rfl⟩ := hω
  obtain ⟨hs, hf, hg⟩ := initialise_invariants pp σ e.1.forms e.1.pv
  have hi : RunInv pp σ ⟨e.2, initialise pp e.1.forms e.1.pv, [], [], none⟩ := by
    refine ⟨⟨hs, ?_, hf⟩, ?_⟩
    · intro v hv
      rw [hg] at hv
      exact False.elim (Finset.notMem_empty v hv)
    · simp
  exact (simulateQ_run_preserves_inv_of_query (obsHandler pp σ e.1.coins)
    (RunInv pp σ) (fun q st hst => obs_step_inv pp σ e.1.coins q st hst)
    (A.run e.1.pv e.1.header) _ hi z hz).2

private lemma diff_vars (P Q : Poly pp) (O : List GuessVar)
    (hP : P.vars ⊆ O.toFinset) (hQ : Q.vars ⊆ O.toFinset) :
    (P - Q).vars ⊆ O.toFinset :=
  (MvPolynomial.vars_sub_subset P).trans (Finset.union_subset hP hQ)

private lemma keyCmp_vars (z : WorldOut P0) (s : Step pp)
    (hs : VarsIn pp ⟨OracleState.empty, s.shadow, s.order, []⟩)
    (e : Collision pp) (he : keyCmp pp z s.shadow = some e) :
    e.diff.vars ⊆ s.order.toFinset := by
  have hd : ∀ l P, s.shadow.dict .gₜ l = some P → P.vars ⊆ s.order.toFinset := by
    intro l P hP v hv
    exact List.mem_toFinset.mpr (hs .gₜ l P hP v hv)
  have hk : (key pp).vars ⊆ s.order.toFinset := by simp [key]
  unfold keyCmp at he
  cases hP : s.shadow.dict .gₜ (z.enc .gₜ (kappa pp z.out.coins)) with
  | some P =>
    simp only [hP, Option.some.injEq] at he
    subst e
    exact diff_vars pp _ _ _ (hd _ P hP) hk
  | none =>
    simp only [hP] at he
    cases hQ : s.shadow.dict .gₜ (z.enc .gₜ (-kappa pp z.out.coins)) with
    | none => simp [hQ] at he
    | some Q =>
      simp only [hQ, Option.some.injEq] at he
      subst e
      apply diff_vars pp _ _ _ ?_ hk
      intro v hv
      rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
      · simp [scalar] at hv
      · exact hd _ Q hQ hv

theorem pending_vars_in_order [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0)
    (obs : ProbComp (World pp)) (hobs : observedRun pp m A = obs)
    (ω : World pp) (hω : ω ∈ support obs) (e : Collision pp) (b : ℕ)
    (hb : ω.2.stop = some b) (he : badCmp ω = some e) :
    e.diff.vars ⊆ ((fullRecord ω).cut b).order.toFinset := by
  have hl := observed_logged pp m A obs hobs ω hω
  unfold badCmp at he
  rw [hb] at he
  cases hs : ω.2.steps[b]? with
  | none => simp [hs] at he
  | some s =>
    simp only [hs] at he
    have hlog := hl s (List.mem_of_getElem? hs)
    have hord : ((fullRecord ω).cut b).order = s.order := by
      simp [Record.order, FullRecord.cut, fullRecord, hs]
    rw [hord]
    rcases hq : s.entry.1 with ((n | gq) | i) | kq
    · simp [hq] at he
    · simp only [hq] at he
      exact hlog.2 e he
    · simp [hq] at he
    · simp only [hq] at he
      exact keyCmp_vars pp ω.1 s hlog.1 e he

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.PendingVars
