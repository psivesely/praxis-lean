import Praxis.Proofs.GroupModel.Split.Lazy.Fold.GuessTyped
import Praxis.Constants
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Init.Counts
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option maxHeartbeats 400000

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

def logGroups {pp : PublicParams P0} (steps : List (Step pp)) : ℕ :=
  (steps.map fun step => callCost step.entry.1 .group).sum

@[simp] lemma logGroups_append {pp : PublicParams P0} (xs ys : List (Step pp)) :
    logGroups (xs ++ ys) = logGroups xs + logGroups ys := by
  simp [logGroups]

@[simp] lemma logGroups_singleton {pp : PublicParams P0} (step : Step pp) :
    logGroups [step] = callCost step.entry.1 .group := by simp [logGroups]

def countHandler (σ : LabelEncoding P0) :
    QueryImpl (AdvModel P0) (StateT (ℕ × OracleState P0) ProbComp) := fun q =>
  StateT.mk fun st => (fun w => (w.1, (st.1 + callCost q .group, w.2))) <$>
    (gameImpl σ q).run st.2

def countProjection {pp : PublicParams P0} (st : ObsState pp) : ℕ × OracleState P0 :=
  (logGroups st.steps, st.oracle)

lemma count_obsHandler (pp : PublicParams P0) (σ : LabelEncoding P0) (c : Coins P0)
    (q : (AdvModel P0).Domain) (st : ObsState pp) :
    Prod.map id countProjection <$> (obsHandler pp σ c q).run st =
      (countHandler σ q).run (countProjection st) := by
  simp [obsHandler, countHandler, countProjection, Functor.map_map, Function.comp_def]

lemma count_observed (pp : PublicParams P0) (σ : LabelEncoding P0) (c : Coins P0)
    {α : Type} (oa : OracleComp (AdvModel P0) α) (st : ObsState pp) :
    Prod.map id countProjection <$> (simulateQ (obsHandler pp σ c) oa).run st =
      (simulateQ (countHandler σ) oa).run (countProjection st) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (count_obsHandler pp σ c) oa st

lemma count_withCost (σ : LabelEncoding P0) {α : Type}
    (oa : OracleComp (AdvModel P0) α) (n : ℕ) (st : OracleState P0) :
    (simulateQ (countHandler σ) oa).run (n, st) =
      (fun z => (z.1.1, (n + z.1.2 .group, z.2))) <$>
        ((simulateQ ((gameImpl σ).withCost callCost) oa).run).run st := by
  induction oa using OracleComp.inductionOn generalizing n st with
  | pure a => simp
  | query_bind q cont ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, countHandler, StateT.run_mk,
      bind_map_left]
    simp [QueryImpl.withCost_apply, WriterT.run_bind, WriterT.run_pure,
      StateT.run_bind, StateT.run_pure, map_bind, bind_map_left, ih,
      Functor.map_map, Function.comp_def, Nat.add_assoc]

lemma observed_group_bound (pp : PublicParams P0) [Nonempty (CoinDomain pp)] (m : Msg P0)
    (A : Adversary P0) (Q QH : ℕ) (hA : InClass A Q QH) (ω : World pp)
    (hω : ω ∈ support (observedRun pp m A)) : logGroups ω.2.steps ≤ Q := by
  unfold observedRun at hω
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hω
  obtain ⟨σ, hσ, e, he, z, hz, rfl⟩ := hω
  let st : ObsState pp := ⟨e.2, initialise pp e.1.forms e.1.pv, [], [], none⟩
  have hp := count_observed pp σ e.1.coins (A.run e.1.pv e.1.header) st
  have hz' : (z.1, countProjection z.2) ∈
      support ((simulateQ (countHandler σ) (A.run e.1.pv e.1.header)).run (countProjection st)) := by
    rw [← hp, support_map]
    exact ⟨z, hz, rfl⟩
  rw [count_withCost, support_map] at hz'
  obtain ⟨y, hy, hyz⟩ := hz'
  have hy' : ((e.1, y.1), y.2) ∈ support (countedRun σ A pp m) := by
    unfold countedRun
    rw [StateT.run_bind, mem_support_bind_iff]
    refine ⟨e, he, ?_⟩
    change ((e.1, y.1), y.2) ∈ support
      (((simulateQ ((gameImpl σ).withCost callCost) (A.run e.1.pv e.1.header)).run).run e.2
        >>= fun y => pure ((e.1, y.1), y.2))
    exact (mem_support_bind_iff ..).mpr ⟨y, hy, by simp⟩
  have hbound := hA.group σ pp m _ hy'
  have hc := congrArg (fun w : Bool × (ℕ × OracleState P0) => w.2.1) hyz
  dsimp only [countProjection, st] at hc
  simp only [logGroups, List.map_nil, List.sum_nil, zero_add] at hc
  change logGroups z.2.steps ≤ Q
  change y.1.2 .group = logGroups z.2.steps at hc
  rw [← hc]
  exact hbound

lemma encGame_data {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (σ : LabelEncoding P) (m : Msg P) (e : EncOut P × OracleState P)
    (he : e ∈ support ((encGame σ pp m).run OracleState.empty)) :
    ValidCoins pp.qap e.1.coins ∧
      e.1.pv = pubView σ pp (formVec e.1.forms) e.1.coins := by
  unfold encGame at he
  rw [StateT.run_bind, mem_support_bind_iff] at he
  obtain ⟨seed, hs, he⟩ := he
  unfold encAt at he
  rw [StateT.run_bind, mem_support_bind_iff] at he
  obtain ⟨entries, hentries, he⟩ := he
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify,
    StateT.run_pure, pure_bind, bind_assoc, mem_support_bind_iff,
    mem_support_pure_iff] at he
  obtain ⟨c, hc, pad, hpad, rfl⟩ := he
  exact ⟨c.property, rfl⟩

lemma valid_observedRun (pp : PublicParams P0) [Nonempty (CoinDomain pp)] (m : Msg P0)
    (A : Adversary P0) (ω : World pp) (hω : ω ∈ support (observedRun pp m A)) :
    ValidCoins pp.qap ω.1.out.coins := by
  unfold observedRun at hω
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hω
  obtain ⟨σ, hσ, e, he, z, hz, rfl⟩ := hω
  exact (encGame_data pp σ m e he).1

lemma assigned_record_le (pp : PublicParams P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (p : Poly pp)
    (t : GroupModel.Sorted.PSort) :
    (assigned pp {st with dict := record pp st.dict s l p} t).card ≤
      (assigned pp st t).card + 1 := by
  have h : assigned pp {st with dict := record pp st.dict s l p} t ⊆
      insert l (assigned pp st t) := by
    intro u hu
    by_cases hul : u = l
    · exact Finset.mem_insert.mpr (Or.inl hul)
    · apply Finset.mem_insert.mpr
      right
      by_cases hts : t = s
      · subst t
        simpa [assigned, record, hul] using hu
      · simpa [assigned, record, hts] using hu
  exact (Finset.card_le_card h).trans (Finset.card_insert_le _ _)

lemma assigned_insert_le (pp : PublicParams P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (p : Poly pp)
    (t : GroupModel.Sorted.PSort) :
    (assigned pp (insertResult pp st s l p) t).card ≤ (assigned pp st t).card + 1 := by
  unfold insertResult
  cases hd : st.dict s l with
  | none => exact assigned_record_le pp st s l p t
  | some q =>
    dsimp only
    split_ifs <;> exact Nat.le_add_right _ _

lemma assigned_resolve_le (pp : PublicParams P0) (σ : LabelEncoding P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (t : GroupModel.Sorted.PSort) :
    (assigned pp (resolve pp σ st s l).2 t).card ≤ (assigned pp st t).card + 1 := by
  unfold resolve
  cases hd : st.dict s l with
  | some p => exact Nat.le_add_right _ _
  | none =>
    cases hc : Algebra.decodeLabel (σ s) l with
    | none => exact Nat.le_add_right _ _
    | some a => exact assigned_record_le pp st s l _ t

lemma assigned_observe_le (pp : PublicParams P0) (σ : LabelEncoding P0) (st : State pp)
    (gq : GQuery P0) (R : gq.Result) (t : GroupModel.Sorted.PSort) :
    (assigned pp (observeGroup pp σ st gq R) t).card ≤ (assigned pp st t).card + 3 := by
  cases gq with
  | lin s a b u v =>
    have hx := assigned_resolve_le pp σ st s u t
    have hy := assigned_resolve_le pp σ (resolve pp σ st s u).2 s v t
    have hz : (assigned pp (resolve pp σ (resolve pp σ st s u).2 s v).2 t).card ≤
        (assigned pp st t).card + 2 := by omega
    simp only [observeGroup]
    cases hP : (resolve pp σ st s u).1 with
    | none => exact hz.trans (by omega)
    | some p =>
      cases hQ : (resolve pp σ (resolve pp σ st s u).2 s v).1 with
      | none => exact hz.trans (by omega)
      | some q =>
        cases R with
        | none => exact hz.trans (by omega)
        | some l =>
          have h := assigned_insert_le pp (resolve pp σ (resolve pp σ st s u).2 s v).2
            s l (scalar pp a * p + scalar pp b * q) t
          exact h.trans (by omega)
  | pair u v =>
    have hx := assigned_resolve_le pp σ st .g₁ u t
    have hy := assigned_resolve_le pp σ (resolve pp σ st .g₁ u).2 .g₂ v t
    have hz : (assigned pp (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).2 t).card ≤
        (assigned pp st t).card + 2 := by omega
    simp only [observeGroup]
    cases hP : (resolve pp σ st .g₁ u).1 with
    | none => exact hz.trans (by omega)
    | some p =>
      cases hQ : (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).1 with
      | none => exact hz.trans (by omega)
      | some q =>
        cases R with
        | none => exact hz.trans (by omega)
        | some l =>
          have h := assigned_insert_le pp (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).2
            .gₜ l (p * q) t
          exact h.trans (by omega)
  | name u =>
    cases R with
    | none => exact Nat.le_add_right _ _
    | some nm => exact (assigned_insert_le pp st .gₜ _ _ t).trans (by omega)

lemma newGuesses_length (pp : PublicParams P0) (st st' : State pp) (gq : GQuery P0) :
    (newGuesses pp st st' gq).length ≤ 2 := by
  cases gq with
  | lin s a b u v =>
    unfold newGuesses
    apply Nat.le_trans (List.dedup_sublist _).length_le
    exact (List.length_filter_le _ _).trans_eq (by rfl)
  | pair u v =>
    unfold newGuesses
    exact (List.length_filter_le _ _).trans_eq (by rfl)
  | name u => simp [newGuesses]

lemma fold_size_le {α β : Type} (f : β → α → β) (size : β → ℕ)
    (hf : ∀ st e, size (f st e) ≤ size st + 1) (entries : List α) (st : β) :
    size (entries.foldl f st) ≤ size st + entries.length := by
  induction entries generalizing st with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, List.length_cons]
    exact (ih (f st e)).trans (by have h := hf st e; omega)

set_option maxRecDepth 200000 in
lemma assigned_fold_le (pp : PublicParams P0)
    (entries : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp)
    (t : GroupModel.Sorted.PSort) :
    (assigned pp (entries.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st) t).card ≤
      (assigned pp st t).card + entries.length := by
  let size : State pp → ℕ := fun st => (assigned pp st t).card
  let f : State pp → (GroupModel.Sorted.PSort × Label P0 × Poly pp) → State pp :=
    fun st e => insertResult pp st e.1 e.2.1 e.2.2
  change size (entries.foldl f st) ≤ size st + entries.length
  apply fold_size_le f size
  intro st e
  exact assigned_insert_le pp st e.1 e.2.1 e.2.2 t

lemma assigned_initialise_le (pp : PublicParams P0) (forms : FormMatrix P0) (pv : PubView P0)
    (t : GroupModel.Sorted.PSort) :
    (assigned pp (initialise pp forms pv) t).card ≤ (initialEntries pp forms pv).length := by
  have h := assigned_fold_le pp (initialEntries pp forms pv) (empty pp) t
  have hempty : (assigned pp (empty pp) t).card = 0 := by
    change (Finset.univ.filter (fun _ : Label P0 =>
      (none : Option (Poly pp)).isSome)).card = 0
    simp only [Option.isSome_none, Bool.false_eq_true, Finset.filter_false, Finset.card_empty]
  rw [hempty, zero_add] at h
  exact h

structure SizesObserved (pp : PublicParams P0) (N : ℕ) (st : ObsState pp) : Prop where
  current : ∀ s, (assigned pp st.shadow s).card ≤ N + 3 * logGroups st.steps
  order : st.order.length ≤ 2 * logGroups st.steps
  steps : ∀ step ∈ st.steps,
    (∀ s, (assigned pp step.shadow s).card ≤ N + 3 * logGroups st.steps) ∧
      step.order.length ≤ 2 * logGroups st.steps

lemma sizes_obsHandler (pp : PublicParams P0) (N : ℕ) (σ : LabelEncoding P0) (c : Coins P0)
    (st : ObsState pp) (ht : SizesObserved pp N st) (q : (AdvModel P0).Domain) :
    ∀ z ∈ support ((obsHandler pp σ c q).run st), SizesObserved pp N z.2 := by
  let shadow := match q with
    | .inl (.inl (.inr gq)) => observeGroup pp σ st.shadow gq (groupAnswer σ st.oracle.issuedT gq)
    | _ => st.shadow
  let order := match q with
    | .inl (.inl (.inr gq)) => st.order ++ newGuesses pp st.shadow shadow gq
    | _ => st.order
  have hsh : ∀ s, (assigned pp shadow s).card ≤
      N + 3 * (logGroups st.steps + callCost q .group) := by
    rcases q with ((n | gq) | hf) | kq
    · simpa [shadow, callCost, isGroupQuery] using ht.current
    · intro s
      have h := assigned_observe_le pp σ st.shadow gq (groupAnswer σ st.oracle.issuedT gq) s
      have h' := ht.current s
      simp only [shadow, callCost, isGroupQuery, ite_true]
      omega
    · simpa [shadow, callCost, isGroupQuery] using ht.current
    · simpa [shadow, callCost, isGroupQuery] using ht.current
  have ho : order.length ≤ 2 * (logGroups st.steps + callCost q .group) := by
    rcases q with ((n | gq) | hf) | kq
    · simpa [order, callCost, isGroupQuery] using ht.order
    · have h := newGuesses_length pp st.shadow shadow gq
      have h' := ht.order
      simp only [order, List.length_append, callCost, isGroupQuery, ite_true]
      omega
    · simpa [order, callCost, isGroupQuery] using ht.order
    · simpa [order, callCost, isGroupQuery] using ht.order
  intro z hz
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hlog : logGroups (st.steps ++ [⟨⟨q, w.1⟩, shadow, order⟩]) =
      logGroups st.steps + callCost q .group := by simp
  refine ⟨?_, ?_, ?_⟩
  · rcases q with ((n | gq) | hf) | kq
    all_goals simpa only [shadow, order, logGroups_append, logGroups_singleton] using hsh
  · rcases q with ((n | gq) | hf) | kq
    all_goals simpa only [shadow, order, logGroups_append, logGroups_singleton] using ho
  · intro step hstep
    rcases List.mem_append.mp hstep with hstep | hstep
    · obtain ⟨hs, ho'⟩ := ht.steps step hstep
      constructor
      · intro s
        have h := hs s
        change _ ≤ N + 3 * logGroups (st.steps ++ [⟨⟨q, w.1⟩, shadow, order⟩])
        rw [hlog]
        omega
      · change _ ≤ 2 * logGroups (st.steps ++ [⟨⟨q, w.1⟩, shadow, order⟩])
        rw [hlog]
        omega
    · have hstep' := List.mem_singleton.mp hstep
      subst step
      constructor
      · rcases q with ((n | gq) | hf) | kq
        all_goals simpa only [shadow, order, logGroups_append, logGroups_singleton] using hsh
      · rcases q with ((n | gq) | hf) | kq
        all_goals simpa only [shadow, order, logGroups_append, logGroups_singleton] using ho

lemma usedBefore_card_le (pp : PublicParams P0) (r : Record pp) (c : CoinDomain pp)
    (j : ℕ) (x : ℕ → k) :
    (usedBefore pp r c j x).card ≤ (assigned pp (r.guessShadow j) (r.sortAt j)).card := by
  have h : usedBefore pp r c j x ⊆
      (assigned pp (r.guessShadow j) (r.sortAt j)).image fun l =>
        valueAt pp r.order c x (((r.guessShadow j).dict (r.sortAt j) l).getD 0) := by
    intro a ha
    obtain ⟨l, p, hp, hvars, hval⟩ := (Finset.mem_filter.mp ha).2
    apply Finset.mem_image.mpr
    refine ⟨l, ?_, ?_⟩
    · simp [assigned, hp]
    · simpa only [hp, Option.getD_some] using hval
  exact (Finset.card_le_card h).trans Finset.card_image_le

lemma assigned_pendingShadow_le (pp : PublicParams P0) (r : Record pp)
    (s : GroupModel.Sorted.PSort) :
    (assigned pp r.pendingShadow s).card ≤ (assigned pp r.shadow s).card + r.order.length := by
  have h : assigned pp r.pendingShadow s ⊆
      assigned pp r.shadow s ∪ r.order.toFinset.image Prod.snd := by
    intro l hl
    cases hd : r.shadow.dict s l with
    | some p => exact Finset.mem_union.mpr (Or.inl (by simp [assigned, hd]))
    | none =>
      have hv : (s, l) ∈ r.order := by
        by_contra hv
        have hl' := (Finset.mem_filter.mp hl).2
        change (match r.shadow.dict s l with
          | some P => some P
          | none => if (s, l) ∈ r.order then some (MvPolynomial.X (s, l)) else none).isSome at hl'
        simp only [hd, ite_false, if_neg hv, Option.isSome_none, Bool.false_eq_true] at hl'
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨(s, l), List.mem_toFinset.mpr hv, rfl⟩))
  exact (Finset.card_le_card h).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
      (Finset.card_image_le.trans (List.toFinset_card_le _)) _))

lemma initialEntries_length (pp : PublicParams P0) (σ : LabelEncoding P0)
    (forms : FormMatrix P0) (coins : Coins P0) :
    (initialEntries pp forms (pubView σ pp (formVec forms) coins)).length = Constants.L := by
  simp only [initialEntries, List.length_append, List.length_map,
    GroupModel.pubView_g1_length_main, GroupModel.pubView_g2_length_main, GroupModel.pubView_gt_length_main]
  rfl

lemma sizes_observedRun (pp : PublicParams P0) [Nonempty (CoinDomain pp)] (m : Msg P0)
    (A : Adversary P0) (ω : World pp)
    (hω : ω ∈ support (observedRun pp m A)) :
    SizesObserved pp Constants.L ω.2 := by
  unfold observedRun at hω
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hω
  obtain ⟨σ, hσ, e, he, z, hz, rfl⟩ := hω
  have he' := encGame_data pp σ m e
  generalize (encGame σ pp m).run OracleState.empty = enc at he' he
  obtain ⟨hc, hpv⟩ := he' he
  apply simulateQ_run_preserves_inv_of_query (obsHandler pp σ e.1.coins)
    (SizesObserved pp Constants.L)
    (fun q st ht => sizes_obsHandler _ _ σ e.1.coins st ht q)
    (A.run e.1.pv e.1.header)
    (⟨e.2, initialise pp e.1.forms e.1.pv, [], [], none⟩ : ObsState pp)
    ?_ z hz
  refine ⟨?_, by simp [logGroups], by simp⟩
  intro s
  have h := assigned_initialise_le pp e.1.forms e.1.pv s
  have hlen : (initialEntries pp e.1.forms e.1.pv).length = Constants.L := by
    rw [hpv, initialEntries_length]
  rw [hlen] at h
  simpa only [logGroups, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] using h

lemma cut_order_length (pp : PublicParams P0) (R : FullRecord pp) (B : ℕ)
    (h : ∀ step ∈ R.steps, step.order.length ≤ B) (n : ℕ) :
    ((R.cut n).order).length ≤ B := by
  unfold Record.order FullRecord.cut
  cases hs : R.steps[n]? with
  | some step =>
    exact h step (List.mem_of_getElem? hs)
  | none =>
    simp only [hs, Option.map_none, Option.getD_none]
    unfold Record.lastOrder
    cases ht : (R.steps.take n).getLast? with
    | none => simp [ht]
    | some step =>
      have hm : step ∈ R.steps.take n := List.mem_of_getLast? ht
      simpa [ht] using h step (List.mem_of_mem_take hm)

lemma cut_shadow_bound (pp : PublicParams P0) (R : FullRecord pp) (B : ℕ)
    (hi : ∀ s, (assigned pp (initialise pp R.forms R.pv) s).card ≤ B)
    (h : ∀ step ∈ R.steps, ∀ s, (assigned pp step.shadow s).card ≤ B) (n : ℕ)
    (s : GroupModel.Sorted.PSort) : (assigned pp (R.cut n).shadow s).card ≤ B := by
  unfold Record.shadow FullRecord.cut
  cases ht : (R.steps.take n).getLast? with
  | none => simpa [ht] using hi s
  | some step =>
    have hm : step ∈ R.steps.take n := List.mem_of_getLast? ht
    simpa [ht] using h step (List.mem_of_mem_take hm) s

lemma cut_used_bound (pp : PublicParams P0) (R : FullRecord pp) (Q : ℕ)
    (hi : ∀ s, (assigned pp (initialise pp R.forms R.pv) s).card ≤ Constants.L)
    (h : ∀ step ∈ R.steps,
      (∀ s, (assigned pp step.shadow s).card ≤ Constants.L + 3 * Q) ∧ step.order.length ≤ 2 * Q)
    (n j : ℕ) (c : CoinDomain pp) (x : ℕ → k) :
    (usedBefore pp (R.cut n) c j x).card ≤ Constants.L + 5 * Q := by
  apply (usedBefore_card_le pp (R.cut n) c j x).trans
  have ho := cut_order_length pp R (2 * Q) (fun step hs => (h step hs).2) n
  have hs := cut_shadow_bound pp R (Constants.L + 3 * Q)
    (fun s => (hi s).trans (Nat.le_add_right _ _))
    (fun step hs => (h step hs).1) n ((R.cut n).sortAt j)
  unfold Record.guessShadow
  cases hf : ((R.cut n).steps.find? fun step => decide (j < step.order.length)) with
  | none =>
    simp only [hf, Option.map_none, Option.getD_none]
    have hp := assigned_pendingShadow_le pp (R.cut n) ((R.cut n).sortAt j)
    omega
  | some step =>
    have hm : step ∈ (R.cut n).steps := List.mem_of_find?_eq_some hf
    have hm' : step ∈ R.steps := List.mem_of_mem_take hm
    simp only [hf, Option.map_some, Option.getD_some]
    exact ((h step hm').1 _).trans (by omega)

lemma observed_initial_size (pp : PublicParams P0) [Nonempty (CoinDomain pp)] (m : Msg P0)
    (A : Adversary P0) (ω : World pp) (hω : ω ∈ support (observedRun pp m A))
    (s : GroupModel.Sorted.PSort) :
    (assigned pp (initialise pp ω.1.out.forms ω.1.out.pv) s).card ≤ Constants.L := by
  unfold observedRun at hω
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hω
  obtain ⟨σ, hσ, e, he, z, hz, rfl⟩ := hω
  obtain ⟨hc, hpv⟩ := encGame_data pp σ m e he
  have h := assigned_initialise_le pp e.1.forms e.1.pv s
  have hlen : (initialEntries pp e.1.forms e.1.pv).length = Constants.L := by
    rw [hpv, initialEntries_length]
  rw [hlen] at h
  change (assigned pp (initialise pp e.1.forms e.1.pv) s).card ≤ Constants.L
  exact h

lemma used_observedRun (pp : PublicParams P0) [Nonempty (CoinDomain pp)] (m : Msg P0)
    (A : Adversary P0) (Q QH : ℕ) (hA : InClass A Q QH) (ω : World pp)
    (hω : ω ∈ support (observedRun pp m A)) (n j : ℕ) (c : CoinDomain pp) (x : ℕ → k) :
    (usedBefore pp ((fullRecord ω).cut n) c j x).card ≤
      Constants.L + 3 * Constants.W_budget + 1 := by
  have hsize := sizes_observedRun pp m A
  have hgroup := observed_group_bound pp m A Q QH hA
  have hinit := observed_initial_size pp m A
  generalize observedRun pp m A = obs at hsize hgroup hinit hω
  have hs := hsize ω hω
  have hg := hgroup ω hω
  have hi := hinit ω hω
  have h := cut_used_bound pp (fullRecord ω) Q hi (fun step hstep =>
    ⟨fun s => ((hs.steps step hstep).1 s).trans (by omega),
      ((hs.steps step hstep).2).trans (by omega)⟩) n j c x
  have hQ := hA.Q_lt
  have hw : Constants.W_budget = 2 * Constants.T := by decide
  omega

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild
