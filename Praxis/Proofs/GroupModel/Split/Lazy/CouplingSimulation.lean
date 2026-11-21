import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0)

def tname (c : Coins P0) (σ : LabelEncoding P0) : ClassName P0 :=
  labelName (σ .gₜ) (kappa pp c)

def cacheT (target : ClassName P0) (pad : Msg P0) (st : OracleState P0) : OracleState P0 :=
  { st with kdf := Function.update st.kdf target (some pad) }

def lift (c : Coins P0) (pad : Msg P0) (σ : LabelEncoding P0) (g : GenState pp) :
    ObsState pp :=
  ⟨cacheT (tname pp c σ) pad g.oracle, g.shadow, g.order, g.steps, none⟩

def cutOf (n : ℕ) (steps : List (Step pp)) :
    List (Step pp) × Option (AdvModel P0).Domain × Option (List GuessVar) :=
  (steps.take n, (steps[n]?).map (fun s => s.entry.1), (steps[n]?).map Step.order)

@[irreducible]
def cons (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k) :
    Finset (LabelEncoding P0) :=
  Finset.univ.filter fun σ =>
    (∀ s l P, sh.dict s l = some P → σ s (valueAt pp ord c x P) = l) ∧
      ∀ s l, l ∈ sh.excluded s → ∀ v, σ s v ≠ l

def guessFactor (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (g : ℕ) : ℝ≥0∞ :=
  ∏ t ∈ Finset.Ico g r.order.length,
    if x t ∈ guessPool pp r c t x then ((guessPool pp r c t x).card : ℝ≥0∞)⁻¹ else 0

lemma guessFactor_of_le (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (g : ℕ)
    (h : r.order.length ≤ g) : guessFactor pp r c x g = 1 := by
  unfold guessFactor
  rw [Finset.Ico_eq_empty_of_le h, Finset.prod_empty]

section Steps

variable (σ σ' : LabelEncoding P0)

lemma gameImpl_unif (n : ℕ) (st : OracleState P0) :
    (gameImpl σ (.inl (.inl (.inl n)))).run st =
      (fun u => (u, st)) <$> (liftM (unifSpec.query n) : ProbComp _) := rfl

lemma gameImpl_hf (i : Seed P0 × FormIndex P0) (st : OracleState P0) :
    (gameImpl σ (.inl (.inr i))).run st = (hfLazy i).run st := rfl

lemma gameImpl_kdf (kq : KdfQuery P0) (st : OracleState P0) :
    (gameImpl σ (.inr kq)).run st = (kdfImpl kq).run st := rfl

lemma gameImpl_group (gq : GQuery P0) (st : OracleState P0) :
    (gameImpl σ (.inl (.inl (.inr gq)))).run st = (groupImpl σ gq).run st := rfl

lemma hfLazy_cacheT (target : ClassName P0) (pad : Msg P0)
    (i : Seed P0 × FormIndex P0) (st : OracleState P0) :
    (hfLazy i).run (cacheT target pad st) =
      (fun r => (r.1, cacheT target pad r.2)) <$> (hfLazy i).run st := by
  cases hh : st.hf i <;>
    simp [hfLazy, cacheT, hh, StateT.run_bind, StateT.run_lift,
      StateT.run_modify, StateT.run_pure]

lemma kdfLazy_cacheT_off (target nm : ClassName P0) (pad : Msg P0)
    (hne : nm ≠ target) (st : OracleState P0) :
    (kdfLazy nm).run (cacheT target pad st) =
      (fun r => (r.1, cacheT target pad r.2)) <$> (kdfLazy nm).run st := by
  cases hh : st.kdf nm <;>
    simp [kdfLazy, cacheT, Function.update_of_ne hne, hh, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, StateT.run_pure,
      Function.update_comm hne]

def kdfName (st : OracleState P0) : KdfQuery P0 → Option (ClassName P0)
  | .ref k => st.names[k]?
  | .guess nm => some nm

lemma kdfLog_cacheT_off (target nm : ClassName P0) (pad : Msg P0)
    (hne : nm ≠ target) (st : OracleState P0) :
    ((do
      modify fun st : OracleState P0 =>
        { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }
      some <$> kdfLazy nm : GameM P0 (Option (Msg P0)))).run (cacheT target pad st) =
      (fun r => (r.1, cacheT target pad r.2)) <$> ((do
        modify fun st : OracleState P0 =>
          { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }
        some <$> kdfLazy nm : GameM P0 (Option (Msg P0)))).run st := by
  simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_map]
  have h := kdfLazy_cacheT_off target nm pad hne
    { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }
  have he : ({ cacheT target pad st with
      kdfLog := (cacheT target pad st).kdfLog ++
        [((cacheT target pad st).tr.length, nm)] } : OracleState P0) =
      cacheT target pad { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] } := rfl
  rw [he, h]
  simp only [Functor.map_map]

lemma kdfImpl_cacheT_off (target : ClassName P0) (pad : Msg P0) (kq : KdfQuery P0)
    (st : OracleState P0) (hne : kdfName st kq ≠ some target) :
    (kdfImpl kq).run (cacheT target pad st) =
      (fun r => (r.1, cacheT target pad r.2)) <$> (kdfImpl kq).run st := by
  cases kq with
  | ref k =>
    cases hk : st.names[k]? with
    | none =>
      simp [kdfImpl, cacheT, hk, StateT.run_bind, StateT.run_get, StateT.run_pure]
    | some nm =>
      have hne' : nm ≠ target := fun h => hne (by simp [kdfName, hk, h])
      have hk' : (cacheT target pad st).names[k]? = some nm := hk
      simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind, hk, hk']
      exact kdfLog_cacheT_off target nm pad hne' st
  | guess nm =>
    have hne' : nm ≠ target := fun h => hne (by simp [kdfName, h])
    simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind]
    exact kdfLog_cacheT_off target nm pad hne' st

variable (c : Coins P0) (pad : Msg P0)

lemma gen_nongroup_unif (g : GenState pp) (n : ℕ) :
    (genHandler pp (.inl (.inl (.inl n)))).run g =
      (fun u => (u, (⟨g.oracle, g.shadow, g.order,
        g.steps ++ [⟨⟨.inl (.inl (.inl n)), u⟩, g.shadow, g.order⟩]⟩ : GenState pp))) <$>
        (liftM (unifSpec.query n) : ProbComp _) := by
  simp only [genHandler, StateT.run_mk, gameImpl_unif, Functor.map_map]

lemma obs_unif (σ : LabelEncoding P0) (g : GenState pp) (hf : g.shadow.first = none)
    (n : ℕ) :
    (obsHandler pp σ c (.inl (.inl (.inl n)))).run (lift pp c pad σ g) =
      (fun z => (z.1, lift pp c pad σ z.2)) <$> (genHandler pp (.inl (.inl (.inl n)))).run g := by
  rw [gen_nongroup_unif]
  simp only [obsHandler, lift, StateT.run_mk, gameImpl_unif, Functor.map_map, hf,
    Option.isSome_none, Bool.false_eq_true, or_self, if_false, Option.orElse_none]

lemma obs_hf (σ : LabelEncoding P0) (g : GenState pp) (hf : g.shadow.first = none)
    (i : Seed P0 × FormIndex P0) :
    (obsHandler pp σ c (.inl (.inr i))).run (lift pp c pad σ g) =
      (fun z => (z.1, lift pp c pad σ z.2)) <$> (genHandler pp (.inl (.inr i))).run g := by
  simp only [obsHandler, genHandler, lift, StateT.run_mk, gameImpl_hf, hfLazy_cacheT,
    Functor.map_map, hf, Option.isSome_none, Bool.false_eq_true, or_self, if_false,
    Option.orElse_none]
  all_goals rfl

lemma obs_kdf (σ : LabelEncoding P0) (g : GenState pp) (hf : g.shadow.first = none)
    (kq : KdfQuery P0) (hne : kdfName g.oracle kq ≠ some (tname pp c σ)) :
    (obsHandler pp σ c (.inr kq)).run (lift pp c pad σ g) =
      (fun z => (z.1, lift pp c pad σ z.2)) <$> (genHandler pp (.inr kq)).run g := by
  have hnt : ¬ KdfTarget pp σ c (cacheT (tname pp c σ) pad g.oracle) kq := by
    intro h
    apply hne
    cases kq <;> simpa [KdfTarget, kdfName, tname, cacheT] using h
  simp only [obsHandler, genHandler, lift, StateT.run_mk, gameImpl_kdf,
    kdfImpl_cacheT_off _ _ kq _ hne, Functor.map_map, hf, Option.isSome_none,
    Bool.false_eq_true, false_or, if_neg hnt, Option.orElse_none]
  all_goals rfl

end Steps

section Support

lemma obs_step_support (σ : LabelEncoding P0) (c : Coins P0) (q : (AdvModel P0).Domain)
    (st : ObsState pp) :
    ∀ y ∈ support ((obsHandler pp σ c q).run st),
      (∃ s : Step pp, s.entry.1 = q ∧ y.2.steps = st.steps ++ [s]) ∧
      (∀ b, st.stop = some b → y.2.stop = some b) := by
  intro y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨z, _, rfl⟩ := hy
  refine ⟨⟨_, rfl, rfl⟩, ?_⟩
  intro b hb
  simp [hb]

lemma gen_step_support (q : (AdvModel P0).Domain) (g : GenState pp) :
    ∀ y ∈ support ((genHandler pp q).run g),
      ∃ s : Step pp, s.entry.1 = q ∧ y.2.steps = g.steps ++ [s] := by
  intro y hy
  rcases q with ((n | gq) | i) | kq
  · simp only [genHandler, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨z, _, rfl⟩ := hy
    exact ⟨_, rfl, rfl⟩
  · simp only [genHandler, StateT.run_mk, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hy
    obtain ⟨z, _, w, _, rfl⟩ := hy
    exact ⟨_, rfl, rfl⟩
  · simp only [genHandler, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨z, _, rfl⟩ := hy
    exact ⟨_, rfl, rfl⟩
  · simp only [genHandler, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨z, _, rfl⟩ := hy
    exact ⟨_, rfl, rfl⟩

lemma obs_run_support (σ : LabelEncoding P0) (c : Coins P0) {α : Type}
    (oa : OracleComp (AdvModel P0) α) (st : ObsState pp) :
    ∀ y ∈ support ((simulateQ (obsHandler pp σ c) oa).run st),
      st.steps <+: y.2.steps ∧ (∀ b, st.stop = some b → y.2.stop = some b) := by
  have h := simulateQ_run_preserves_inv_of_query (obsHandler pp σ c)
    (fun s : ObsState pp => st.steps <+: s.steps ∧ (∀ b, st.stop = some b → s.stop = some b))
    (by
      intro t s hs y hy
      obtain ⟨⟨s', _, hs'⟩, hb⟩ := obs_step_support pp σ c t s y hy
      refine ⟨?_, fun b h => hb b (hs.2 b h)⟩
      rw [hs']
      exact hs.1.trans (List.prefix_append _ _))
    oa st ⟨List.prefix_refl _, fun _ h => h⟩
  exact h

lemma gen_run_support {α : Type} (oa : OracleComp (AdvModel P0) α) (g : GenState pp) :
    ∀ y ∈ support ((simulateQ (genHandler pp) oa).run g), g.steps <+: y.2.steps := by
  have h := simulateQ_run_preserves_inv_of_query (genHandler pp)
    (fun s : GenState pp => g.steps <+: s.steps)
    (by
      intro t s hs y hy
      obtain ⟨s', _, hs'⟩ := gen_step_support pp t s y hy
      rw [hs']
      exact hs.trans (List.prefix_append _ _))
    oa g (List.prefix_refl _)
  exact h

end Support

section Main

variable (n : ℕ) (r : Record pp)

def RGood (st : ObsState pp) : Prop :=
  (∀ b, st.stop = some b → n ≤ b) ∧
    cutOf pp n st.steps = (r.steps, r.pending, r.pendingOrder)

def GGood (g : GenState pp) : Prop := cutOf pp n g.steps = (r.steps, r.pending, r.pendingOrder)

lemma cutOf_append (steps more : List (Step pp)) (h : n < steps.length) :
    cutOf pp n (steps ++ more) = cutOf pp n steps := by
  unfold cutOf
  rw [List.take_append_of_le_length h.le, List.getElem?_append_left h]

lemma obs_main {β : Type} (oa : ProbComp β) (f : β → ObsState pp) (steps : List (Step pp))
    (h : n < steps.length) (hsupp : ∀ z ∈ support oa, steps <+: (f z).steps) :
    Pr[fun z => RGood pp n r (f z) | oa] ≤
      if cutOf pp n steps = (r.steps, r.pending, r.pendingOrder) then 1 else 0 := by
  split_ifs with hf
  · exact probEvent_le_one
  · apply le_of_eq
    rw [probEvent_eq_zero_iff]
    intro z hz hg
    apply hf
    obtain ⟨more, hmore⟩ := hsupp z hz
    rw [← hg.2, ← hmore, cutOf_append pp n steps more h]

lemma gen_main {β : Type} (oa : ProbComp β) (f : β → GenState pp) (steps : List (Step pp))
    (h : n < steps.length) (hsupp : ∀ z ∈ support oa, steps <+: (f z).steps) :
    Pr[fun z => GGood pp n r (f z) | oa] =
      if cutOf pp n steps = (r.steps, r.pending, r.pendingOrder) then 1 else 0 := by
  have hcut : ∀ z ∈ support oa, cutOf pp n (f z).steps = cutOf pp n steps := by
    intro z hz
    obtain ⟨more, hmore⟩ := hsupp z hz
    rw [← hmore, cutOf_append pp n steps more h]
  split_ifs with hf
  · rw [probEvent_eq_one_iff]
    refine ⟨probFailure_eq_zero, fun z hz => ?_⟩
    unfold GGood
    rw [hcut z hz, hf]
  · rw [probEvent_eq_zero_iff]
    intro z hz hg
    exact hf ((hcut z hz).symm.trans hg)

lemma obs_bind_support (σ : LabelEncoding P0) (c : Coins P0) (t : (AdvModel P0).Domain)
    {α : Type} (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α) (st : ObsState pp) :
    ∀ z ∈ support ((obsHandler pp σ c t).run st >>= fun y =>
        (simulateQ (obsHandler pp σ c) (cont y.1)).run y.2), st.steps <+: z.2.steps := by
  intro z hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨⟨s, _, hsy⟩, _⟩ := obs_step_support pp σ c t st y hy
  obtain ⟨⟨more, hmore⟩, _⟩ := obs_run_support pp σ c (cont y.1) y.2 z hz
  exact ⟨[s] ++ more, by rw [← hmore, hsy, List.append_assoc]⟩

lemma gen_bind_support (t : (AdvModel P0).Domain) {α : Type}
    (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α) (g : GenState pp) :
    ∀ z ∈ support ((genHandler pp t).run g >>= fun y =>
        (simulateQ (genHandler pp) (cont y.1)).run y.2), g.steps <+: z.2.steps := by
  intro z hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨s, _, hsy⟩ := gen_step_support pp t g y hy
  obtain ⟨more, hmore⟩ := gen_run_support pp (cont y.1) y.2 z hz
  exact ⟨[s] ++ more, by rw [← hmore, hsy, List.append_assoc]⟩

lemma obs_pending (σ : LabelEncoding P0) (c : Coins P0) (t : (AdvModel P0).Domain) {α : Type}
    (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α) (st : ObsState pp)
    (h : n = st.steps.length) :
    Pr[fun z => RGood pp n r z.2 | (obsHandler pp σ c t).run st >>= fun y =>
        (simulateQ (obsHandler pp σ c) (cont y.1)).run y.2] ≤
      Pr[fun y => cutOf pp n y.2.steps = (r.steps, r.pending, r.pendingOrder) |
        (obsHandler pp σ c t).run st] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ support ((obsHandler pp σ c t).run st)
  · obtain ⟨⟨s, _, hsy⟩, _⟩ := obs_step_support pp σ c t st y hy
    have hlt : n < y.2.steps.length := by rw [hsy]; simp [h]
    have hf := obs_main pp n r ((simulateQ (obsHandler pp σ c) (cont y.1)).run y.2) Prod.snd
      y.2.steps hlt (fun z hz => (obs_run_support pp σ c (cont y.1) y.2 z hz).1)
    refine (mul_le_mul' le_rfl hf).trans ?_
    split_ifs <;> simp
  · rw [(probOutput_eq_zero_iff _ _).mpr hy, zero_mul]
    exact zero_le

lemma gen_pending (t : (AdvModel P0).Domain) {α : Type}
    (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α) (g : GenState pp)
    (h : n = g.steps.length) :
    Pr[fun z => GGood pp n r z.2 | (genHandler pp t).run g >>= fun y =>
        (simulateQ (genHandler pp) (cont y.1)).run y.2] =
      Pr[fun y => cutOf pp n y.2.steps = (r.steps, r.pending, r.pendingOrder) |
        (genHandler pp t).run g] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  congr 1
  funext y
  by_cases hy : y ∈ support ((genHandler pp t).run g)
  · obtain ⟨s, _, hsy⟩ := gen_step_support pp t g y hy
    have hlt : n < y.2.steps.length := by rw [hsy]; simp [h]
    rw [gen_main pp n r ((simulateQ (genHandler pp) (cont y.1)).run y.2) Prod.snd
      y.2.steps hlt (fun z hz => gen_run_support pp (cont y.1) y.2 z hz)]
    split_ifs <;> simp
  · rw [(probOutput_eq_zero_iff _ _).mpr hy, zero_mul]
    split_ifs <;> rfl

end Main

def OrdInv (g : GenState pp) : Prop := ∀ s ∈ g.steps, s.order <+: g.order

def RMono (r : Record pp) : Prop := ∀ s ∈ r.steps, s.order <+: r.order

def guessValuesσ (r : Record pp) (σ : LabelEncoding P0) : ℕ → k :=
  fun t => match r.order[t]? with
    | some v => (Algebra.decodeLabel (σ v.1) v.2).getD 0
    | none => 0

lemma order_le_of_cut (n : ℕ) (r : Record pp) (g : GenState pp) (hord : OrdInv pp g)
    (hc : cutOf pp n g.steps = (r.steps, r.pending, r.pendingOrder)) :
    r.order.length ≤ g.order.length := by
  unfold cutOf at hc
  simp only [Prod.mk.injEq] at hc
  obtain ⟨hc1, _, hc3⟩ := hc
  unfold Record.order
  cases hp : r.pendingOrder with
  | some L =>
    rw [hp] at hc3
    obtain ⟨s, hs, hsL⟩ := Option.map_eq_some_iff.mp hc3
    have hm : s ∈ g.steps := List.mem_of_getElem? hs
    simpa [hsL] using (hord s hm).length_le
  | none =>
    simp only [Option.getD_none]
    unfold Record.lastOrder
    cases hl : r.steps.getLast? with
    | none => simp
    | some s =>
      have hs : s ∈ g.steps := by
        have := List.mem_of_getLast? hl
        rw [← hc1] at this
        exact List.mem_of_mem_take this
      simpa using (hord s hs).length_le

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0)

section GroupSteps

lemma groupImpl_factor' (σ : LabelEncoding P0) (gq : GQuery P0) (st : OracleState P0) :
    (groupImpl σ gq).run st = (finishGroup gq (groupAnswer σ st.issuedT gq)).run st := by
  simp only [groupImpl, finishGroup, StateT.run_bind, StateT.run_get, pure_bind]
  cases ht : trEntry gq (groupAnswer σ st.issuedT gq) with
  | none => rfl
  | some e => cases hi : e.issuedGT <;> simp only [hi]

lemma handOut_cacheT (target : ClassName P0) (pad : Msg P0)
    (qr : GQuery P0) (R : qr.Result) (st : OracleState P0) :
    (handOut qr R).run (cacheT target pad st) =
      (fun z => (z.1, cacheT target pad z.2)) <$> (handOut qr R).run st := by
  cases qr with
  | lin s a b u v => simp [handOut, cacheT]
  | pair u v => simp [handOut, cacheT]
  | name v =>
    cases R with
    | none => simp [handOut, cacheT]
    | some nm =>
      simp only [handOut, nameRef, StateT.run_bind, StateT.run_map, StateT.run_get, pure_bind]
      cases hn : st.names.findIdx? (· == nm) <;>
        simp [cacheT, hn, StateT.run_set, StateT.run_pure]

lemma finishGroup_cacheT (target : ClassName P0) (pad : Msg P0)
    (gq : GQuery P0) (R : gq.Result) (st : OracleState P0) :
    (finishGroup gq R).run (cacheT target pad st) =
      (fun z => (z.1, cacheT target pad z.2)) <$> (finishGroup gq R).run st := by
  unfold finishGroup
  cases ht : trEntry gq R with
  | none =>
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    exact handOut_cacheT target pad gq R st
  | some e =>
    simp only [StateT.run_bind, StateT.run_modify, pure_bind]
    exact handOut_cacheT target pad gq R
      { hf := st.hf, kdf := st.kdf, tr := st.tr ++ [e], kdfLog := st.kdfLog,
        issuedT := match e.issuedGT with
          | none => st.issuedT
          | some l => insert l st.issuedT,
        names := st.names }

def realResult (σ : LabelEncoding P0) (g : GenState pp) (gq : GQuery P0) : gq.Result :=
  groupAnswer σ g.oracle.issuedT gq

def realShadow (σ : LabelEncoding P0) (g : GenState pp) (gq : GQuery P0) : State pp :=
  observeGroup pp σ g.shadow gq (realResult pp σ g gq)

def afterGroup (g : GenState pp) (gq : GQuery P0) (sh' : State pp)
    (w : gq.Answer × OracleState P0) : GenState pp :=
  ⟨w.2, sh', g.order ++ newGuesses pp g.shadow sh' gq,
    g.steps ++ [⟨⟨.inl (.inl (.inr gq)), w.1⟩, sh', g.order ++ newGuesses pp g.shadow sh' gq⟩]⟩

lemma gen_group (g : GenState pp) (gq : GQuery P0) :
    (genHandler pp (.inl (.inl (.inr gq)))).run g =
      (referenceGroup pp g.oracle.issuedT gq).run g.shadow >>= fun z =>
        (finishGroup gq z.1).run g.oracle >>= fun w =>
          pure (w.1, afterGroup pp g gq z.2 w) := rfl

lemma obs_group (σ : LabelEncoding P0) (c : Coins P0) (pad : Msg P0) (g : GenState pp)
    (gq : GQuery P0) :
    (obsHandler pp σ c (.inl (.inl (.inr gq)))).run (lift pp c pad σ g) =
      (fun w => (w.1, (⟨cacheT (tname pp c σ) pad (afterGroup pp g gq (realShadow pp σ g gq) w).oracle,
        realShadow pp σ g gq, (afterGroup pp g gq (realShadow pp σ g gq) w).order,
        (afterGroup pp g gq (realShadow pp σ g gq) w).steps,
        if (realShadow pp σ g gq).first.isSome then some g.steps.length else none⟩ :
          ObsState pp))) <$>
        (finishGroup gq (realResult pp σ g gq)).run g.oracle := by
  simp only [obsHandler, lift, StateT.run_mk, gameImpl_group, groupImpl_factor',
    finishGroup_cacheT, Functor.map_map, Option.orElse_none, realShadow, realResult,
    afterGroup, or_false]
  rfl

end GroupSteps

lemma sum_tsum_swap {β : Type} (W : Finset (LabelEncoding P0)) (f : LabelEncoding P0 → β → ℝ≥0∞) :
    ∑ σ ∈ W, ∑' y, f σ y = ∑' y, ∑ σ ∈ W, f σ y :=
  (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

lemma sum_commuting {α : Type} (n : ℕ) (r : Record pp) (c : Coins P0) (pad : Msg P0)
    (t : (AdvModel P0).Domain) (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α)
    (g : GenState pp) (W : Finset (LabelEncoding P0)) (B : ℝ≥0∞)
    (hcomm : ∀ σ ∈ W, (obsHandler pp σ c t).run (lift pp c pad σ g) =
      (fun z => (z.1, lift pp c pad σ z.2)) <$> (genHandler pp t).run g)
    (hIH : ∀ y ∈ support ((genHandler pp t).run g),
      ∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 |
          (simulateQ (obsHandler pp σ c) (cont y.1)).run (lift pp c pad σ y.2)] ≤
        B * Pr[fun z => GGood pp n r z.2 | (simulateQ (genHandler pp) (cont y.1)).run y.2]) :
    ∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 | (obsHandler pp σ c t).run (lift pp c pad σ g) >>=
        fun y => (simulateQ (obsHandler pp σ c) (cont y.1)).run y.2] ≤
      B * Pr[fun z => GGood pp n r z.2 | (genHandler pp t).run g >>= fun y =>
        (simulateQ (genHandler pp) (cont y.1)).run y.2] := by
  calc
    _ = ∑ σ ∈ W, ∑' y, Pr[= y | (genHandler pp t).run g] *
          Pr[fun z => RGood pp n r z.2 |
            (simulateQ (obsHandler pp σ c) (cont y.1)).run (lift pp c pad σ y.2)] := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hcomm σ hσ, bind_map_left, probEvent_bind_eq_tsum]
    _ = ∑' y, Pr[= y | (genHandler pp t).run g] * ∑ σ ∈ W,
          Pr[fun z => RGood pp n r z.2 |
            (simulateQ (obsHandler pp σ c) (cont y.1)).run (lift pp c pad σ y.2)] := by
      rw [sum_tsum_swap]
      congr 1
      funext y
      rw [Finset.mul_sum]
    _ ≤ ∑' y, Pr[= y | (genHandler pp t).run g] *
          (B * Pr[fun z => GGood pp n r z.2 | (simulateQ (genHandler pp) (cont y.1)).run y.2]) := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : y ∈ support ((genHandler pp t).run g)
      · exact mul_le_mul' le_rfl (hIH y hy)
      · rw [(probOutput_eq_zero_iff _ _).mpr hy, zero_mul, zero_mul]
    _ = B * Pr[fun z => GGood pp n r z.2 | (genHandler pp t).run g >>= fun y =>
          (simulateQ (genHandler pp) (cont y.1)).run y.2] := by
      rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
      congr 1
      funext y
      ring

lemma hfLazy_issuedT (i : Seed P0 × FormIndex P0) (st : OracleState P0) :
    ∀ y ∈ support ((hfLazy i).run st), y.2.issuedT = st.issuedT := by
  intro y hy
  cases hh : st.hf i with
  | none =>
    simp only [hfLazy, hh, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff, bind_pure_comp, support_map, Set.mem_image] at hy
    obtain ⟨a, ⟨u, _, rfl⟩, rfl⟩ := hy
    rfl
  | some a =>
    simp only [hfLazy, hh, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hy
    rw [hy]

lemma kdfImpl_issuedT (kq : KdfQuery P0) (st : OracleState P0) :
    ∀ y ∈ support ((kdfImpl kq).run st), y.2.issuedT = st.issuedT := by
  intro y hy
  have key : ∀ (nm : ClassName P0) (st0 : OracleState P0),
      ∀ y ∈ support ((kdfLazy nm).run st0), y.2.issuedT = st0.issuedT := by
    intro nm st0 y hy
    cases hh : st0.kdf nm with
    | none =>
      simp only [kdfLazy, hh, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
        StateT.run_modify, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, bind_pure_comp, support_map, Set.mem_image] at hy
      obtain ⟨a, ⟨u, _, rfl⟩, rfl⟩ := hy
      rfl
    | some a =>
      simp only [kdfLazy, hh, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hy
      rw [hy]
  cases kq with
  | ref k =>
    cases hk : st.names[k]? with
    | none =>
      simp only [kdfImpl, hk, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hy
      rw [hy]
    | some nm =>
      simp only [kdfImpl, hk, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modify,
        StateT.run_map, support_map, Set.mem_image] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      obtain h := key nm _ z hz
      exact h
  | guess nm =>
    simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modify,
      StateT.run_map, support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain h := key nm _ z hz
    exact h

lemma gen_nongroup_support (t : (AdvModel P0).Domain) (ht : ∀ gq, t ≠ .inl (.inl (.inr gq)))
    (g : GenState pp) :
    ∀ y ∈ support ((genHandler pp t).run g),
      y.2.shadow = g.shadow ∧ y.2.order = g.order ∧
      y.2.oracle.issuedT = g.oracle.issuedT ∧
      y.2.steps = g.steps ++ [⟨⟨t, y.1⟩, g.shadow, g.order⟩] := by
  intro y hy
  rcases t with ((m | gq) | i) | kq
  · simp only [genHandler, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [gameImpl_unif, support_map] at hz
    obtain ⟨u, _, rfl⟩ := hz
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exact absurd rfl (ht gq)
  · simp only [genHandler, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [gameImpl_hf] at hz
    exact ⟨rfl, rfl, hfLazy_issuedT i g.oracle z hz, rfl⟩
  · simp only [genHandler, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [gameImpl_kdf] at hz
    exact ⟨rfl, rfl, kdfImpl_issuedT kq g.oracle z hz, rfl⟩

section Induction

variable (n : ℕ) (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (pad : Msg P0)

def Cover (g : GenState pp) : Prop := ∀ l ∈ g.oracle.issuedT, (g.shadow.dict .gₜ l).isSome

def VarsIn (g : GenState pp) : Prop :=
  ∀ s l P, g.shadow.dict s l = some P → ∀ v ∈ P.vars, v ∈ g.order

def OrdGuess (g : GenState pp) : Prop :=
  g.order.Nodup ∧ (∀ v, v ∈ g.order ↔ v ∈ g.shadow.guesses) ∧
    ∀ v ∈ g.shadow.guesses, g.shadow.dict v.1 v.2 = some (MvPolynomial.X v)

def Inv (g : GenState pp) : Prop :=
  g.shadow.first = none ∧ OrdInv pp g ∧ Cover pp g ∧ VarsIn pp g ∧ OrdGuess pp g

def ConsStep : Prop :=
  ∀ (g : GenState pp) (gq : GQuery P0) (σ : LabelEncoding P0),
    Inv pp g → σ ∈ cons pp g.shadow g.order c x → guessValuesσ pp r σ = x →
    (realShadow pp σ g gq).first = none →
    (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq) <+: r.order →
    σ ∈ cons pp (realShadow pp σ g gq)
      (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq) c x

def CoverStep : Prop :=
  ∀ (g : GenState pp) (gq : GQuery P0) (σ : LabelEncoding P0)
    (w : gq.Answer × OracleState P0),
    Inv pp g → σ ∈ cons pp g.shadow g.order c x →
    w ∈ support ((finishGroup gq (realResult pp σ g gq)).run g.oracle) →
    (realShadow pp σ g gq).first = none →
    Cover pp (afterGroup pp g gq (realShadow pp σ g gq) w) ∧
      VarsIn pp (afterGroup pp g gq (realShadow pp σ g gq) w) ∧
      OrdGuess pp (afterGroup pp g gq (realShadow pp σ g gq) w)

def CountStep : Prop :=
  ∀ (g : GenState pp) (gq : GQuery P0) (σ : LabelEncoding P0)
    (w : gq.Answer × OracleState P0),
    Inv pp g → g.steps.length < n → RMono pp r → g.steps <+: r.steps →
    σ ∈ cons pp g.shadow g.order c x →
    guessValuesσ pp r σ = x → (realShadow pp σ g gq).first = none →
    w ∈ support ((finishGroup gq (realResult pp σ g gq)).run g.oracle) →
    r.steps[g.steps.length]? =
      (afterGroup pp g gq (realShadow pp σ g gq) w).steps[g.steps.length]? →
    ((cons pp (realShadow pp σ g gq)
        (afterGroup pp g gq (realShadow pp σ g gq) w).order c x).card : ℝ≥0∞) *
        guessFactor pp r c x (afterGroup pp g gq (realShadow pp σ g gq) w).order.length ≤
      (cons pp g.shadow g.order c x).card *
        Pr[= (realResult pp σ g gq, realShadow pp σ g gq) |
          (referenceGroup pp g.oracle.issuedT gq).run g.shadow] *
        guessFactor pp r c x g.order.length

def ShadowOf (g : GenState pp) : Prop := r.steps = g.steps → r.shadow = g.shadow

def PendingStep : Prop :=
  ∀ (g : GenState pp) (gq : GQuery P0) (W : Finset (LabelEncoding P0)) (L : List GuessVar),
    Inv pp g → r.steps = g.steps → r.shadow = g.shadow → r.pendingOrder = some L →
    (∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x) →
    ((W.filter fun σ => g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq = L).card :
        ℝ≥0∞) ≤
      (cons pp g.shadow g.order c x).card *
        Pr[fun z => g.order ++ newGuesses pp g.shadow z.2 gq = L |
          (referenceGroup pp g.oracle.issuedT gq).run g.shadow] *
        guessFactor pp r c x g.order.length

def IndStmt {α : Type} (oa : OracleComp (AdvModel P0) α) : Prop :=
  ∀ (g : GenState pp) (W : Finset (LabelEncoding P0)), Inv pp g → ShadowOf pp r g →
    (∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x) →
    ∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 |
        (simulateQ (obsHandler pp σ c.val) oa).run (lift pp c.val pad σ g)] ≤
      (cons pp g.shadow g.order c x).card *
        Pr[fun z => GGood pp n r z.2 | (simulateQ (genHandler pp) oa).run g] *
        guessFactor pp r c x g.order.length

lemma inv_nongroup (t : (AdvModel P0).Domain) (ht : ∀ gq, t ≠ .inl (.inl (.inr gq)))
    (g : GenState pp) (hI : Inv pp g) :
    ∀ y ∈ support ((genHandler pp t).run g), Inv pp y.2 ∧ y.2.shadow = g.shadow ∧
      y.2.order = g.order := by
  intro y hy
  obtain ⟨hs, ho, hi, hst⟩ := gen_nongroup_support pp t ht g y hy
  refine ⟨⟨by rw [hs]; exact hI.1, ?_, ?_, ?_⟩, hs, ho⟩
  · intro s hsm
    rw [hst] at hsm
    rw [ho]
    rcases List.mem_append.mp hsm with h | h
    · exact hI.2.1 s h
    · rw [List.mem_singleton.mp h]
  · intro l hl
    rw [hs]
    rw [hi] at hl
    exact hI.2.2.1 l hl
  · refine ⟨?_, ?_⟩
    · intro s l P hP v hv
      rw [ho]
      rw [hs] at hP
      exact hI.2.2.2.1 s l P hP v hv
    · rw [OrdGuess, ho, hs]
      exact hI.2.2.2.2

lemma shadowOf_of_last (g : GenState pp) (steps : List (Step pp)) (s : Step pp)
    (hst : g.steps = steps ++ [s]) (hsh : s.shadow = g.shadow) : ShadowOf pp r g := by
  intro h
  unfold Record.shadow
  rw [h, hst]
  simp [hsh]

lemma card_W_le (g : GenState pp) (W : Finset (LabelEncoding P0))
    (hW : ∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x) :
    (W.card : ℝ≥0∞) ≤ (cons pp g.shadow g.order c x).card :=
  Nat.cast_le.mpr (Finset.card_le_card (fun σ hσ => (hW σ hσ).1))

lemma ind_pure {α : Type} (a : α) : IndStmt pp n r c x pad (pure a : OracleComp _ α) := by
  intro g W hI _ hW
  simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
  by_cases hc : cutOf pp n g.steps = (r.steps, r.pending, r.pendingOrder)
  · have hR : ∀ σ, RGood pp n r (lift pp c.val pad σ g) := fun σ =>
      ⟨fun b hb => by simp [lift] at hb, hc⟩
    have hgf : guessFactor pp r c x g.order.length = 1 :=
      guessFactor_of_le pp r c x _ (order_le_of_cut pp n r g hI.2.1 hc)
    have hG : GGood pp n r g := hc
    simp only [hR, hG, if_true, Finset.sum_const, nsmul_eq_mul, mul_one, hgf]
    exact card_W_le pp r c x g W hW
  · have hR : ∀ σ, ¬ RGood pp n r (lift pp c.val pad σ g) := fun σ h => hc h.2
    rw [Finset.sum_eq_zero (fun σ _ => if_neg (hR σ))]
    exact zero_le

lemma ind_main {α : Type} (t : (AdvModel P0).Domain)
    (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α)
    (g : GenState pp) (W : Finset (LabelEncoding P0)) (hI : Inv pp g)
    (hW : ∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x)
    (hlen : n < g.steps.length) :
    ∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 | (obsHandler pp σ c.val t).run (lift pp c.val pad σ g)
        >>= fun y => (simulateQ (obsHandler pp σ c.val) (cont y.1)).run y.2] ≤
      (cons pp g.shadow g.order c x).card *
        Pr[fun z => GGood pp n r z.2 | (genHandler pp t).run g >>= fun y =>
          (simulateQ (genHandler pp) (cont y.1)).run y.2] *
        guessFactor pp r c x g.order.length := by
  rw [gen_main pp n r _ Prod.snd g.steps hlen (gen_bind_support pp t cont g)]
  refine (Finset.sum_le_sum (fun σ _ =>
    obs_main pp n r _ Prod.snd g.steps hlen
      (obs_bind_support pp σ c.val t cont (lift pp c.val pad σ g)))).trans ?_
  split_ifs with hf
  · have hgf : guessFactor pp r c x g.order.length = 1 :=
      guessFactor_of_le pp r c x _ (order_le_of_cut pp n r g hI.2.1 hf)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hgf]
    exact card_W_le pp r c x g W hW
  · rw [Finset.sum_const_zero]
    exact zero_le

lemma obs_nongroup_steps (σ : LabelEncoding P0) (c : Coins P0) (t : (AdvModel P0).Domain)
    (ht : ∀ gq, t ≠ .inl (.inl (.inr gq))) (st : ObsState pp) :
    ∀ y ∈ support ((obsHandler pp σ c t).run st),
      y.2.steps = st.steps ++ [⟨⟨t, y.1⟩, st.shadow, st.order⟩] := by
  intro y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨z, _, rfl⟩ := hy
  rcases t with ((m | gq) | i) | kq
  · rfl
  · exact absurd rfl (ht gq)
  · rfl
  · rfl

lemma cutOf_last (g : GenState pp) (hlen : n = g.steps.length) (s : Step pp) :
    cutOf pp n (g.steps ++ [s]) = (g.steps, some s.entry.1, some s.order) := by
  subst hlen
  unfold cutOf
  rw [List.take_append_of_le_length le_rfl, List.take_length,
    List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

lemma ind_pending_nongroup {α : Type} (t : (AdvModel P0).Domain)
    (ht : ∀ gq, t ≠ .inl (.inl (.inr gq)))
    (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α)
    (g : GenState pp) (W : Finset (LabelEncoding P0))
    (hW : ∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x)
    (hlen : n = g.steps.length) :
    ∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 | (obsHandler pp σ c.val t).run (lift pp c.val pad σ g)
        >>= fun y => (simulateQ (obsHandler pp σ c.val) (cont y.1)).run y.2] ≤
      (cons pp g.shadow g.order c x).card *
        Pr[fun z => GGood pp n r z.2 | (genHandler pp t).run g >>= fun y =>
          (simulateQ (genHandler pp) (cont y.1)).run y.2] *
        guessFactor pp r c x g.order.length := by
  rw [gen_pending pp n r t cont g hlen]
  refine (Finset.sum_le_sum (fun σ _ =>
    obs_pending pp n r σ c.val t cont (lift pp c.val pad σ g) hlen)).trans ?_
  have hreal : ∀ σ, Pr[fun y => cutOf pp n y.2.steps = (r.steps, r.pending, r.pendingOrder) |
      (obsHandler pp σ c.val t).run (lift pp c.val pad σ g)] ≤
      if (g.steps, some t, some g.order) = (r.steps, r.pending, r.pendingOrder) then 1 else 0 := by
    intro σ
    split_ifs with hm
    · exact probEvent_le_one
    · apply le_of_eq
      rw [probEvent_eq_zero_iff]
      intro y hy hc
      apply hm
      rw [obs_nongroup_steps pp σ c.val t ht _ y hy] at hc
      exact (cutOf_last pp n g hlen ⟨⟨t, y.1⟩, g.shadow, g.order⟩).symm.trans hc
  have hgen : Pr[fun y => cutOf pp n y.2.steps = (r.steps, r.pending, r.pendingOrder) |
      (genHandler pp t).run g] =
      if (g.steps, some t, some g.order) = (r.steps, r.pending, r.pendingOrder) then 1 else 0 := by
    split_ifs with hm
    · rw [probEvent_eq_one_iff]
      refine ⟨probFailure_eq_zero, fun y hy => ?_⟩
      obtain ⟨_, _, _, hst⟩ := gen_nongroup_support pp t ht g y hy
      rw [hst, cutOf_last pp n g hlen]
      exact hm
    · rw [probEvent_eq_zero_iff]
      intro y hy hc
      apply hm
      obtain ⟨_, _, _, hst⟩ := gen_nongroup_support pp t ht g y hy
      rw [hst, cutOf_last pp n g hlen] at hc
      exact hc
  rw [hgen]
  refine (Finset.sum_le_sum (fun σ _ => hreal σ)).trans ?_
  split_ifs with hm
  · have hord : r.order = g.order := by
      simp only [Prod.mk.injEq] at hm
      unfold Record.order
      rw [← hm.2.2]
      rfl
    have hgf : guessFactor pp r c x g.order.length = 1 :=
      guessFactor_of_le pp r c x _ (by rw [hord])
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hgf]
    exact card_W_le pp r c x g W hW
  · rw [Finset.sum_const_zero]
    exact zero_le

lemma ind_pending_group (hpend : PendingStep pp r c x) {α : Type} (gq : GQuery P0)
    (cont : (AdvModel P0).Range (.inl (.inl (.inr gq))) → OracleComp (AdvModel P0) α)
    (g : GenState pp) (W : Finset (LabelEncoding P0)) (hI : Inv pp g) (hS : ShadowOf pp r g)
    (hW : ∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x)
    (hlen : n = g.steps.length) :
    ∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 |
        (obsHandler pp σ c.val (.inl (.inl (.inr gq)))).run (lift pp c.val pad σ g)
        >>= fun y => (simulateQ (obsHandler pp σ c.val) (cont y.1)).run y.2] ≤
      (cons pp g.shadow g.order c x).card *
        Pr[fun z => GGood pp n r z.2 | (genHandler pp (.inl (.inl (.inr gq)))).run g >>= fun y =>
          (simulateQ (genHandler pp) (cont y.1)).run y.2] *
        guessFactor pp r c x g.order.length := by
  rw [gen_pending pp n r _ cont g hlen]
  refine (Finset.sum_le_sum (fun σ _ =>
    obs_pending pp n r σ c.val _ cont (lift pp c.val pad σ g) hlen)).trans ?_
  have hcut := cutOf_last pp n g hlen
  have hreal : ∀ σ, Pr[fun y => cutOf pp n y.2.steps = (r.steps, r.pending, r.pendingOrder) |
      (obsHandler pp σ c.val (.inl (.inl (.inr gq)))).run (lift pp c.val pad σ g)] ≤
      if (g.steps, (some (.inl (.inl (.inr gq))) : Option (AdvModel P0).Domain),
        some (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq)) =
          (r.steps, r.pending, r.pendingOrder) then 1 else 0 := by
    intro σ
    split_ifs with hm
    · exact probEvent_le_one
    · apply le_of_eq
      rw [probEvent_eq_zero_iff]
      intro y hy hc
      apply hm
      rw [obs_group, support_map] at hy
      obtain ⟨w, _, rfl⟩ := hy
      rw [← hc]
      exact (hcut ⟨⟨.inl (.inl (.inr gq)), w.1⟩, realShadow pp σ g gq,
        g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq⟩).symm
  have hgen : Pr[fun y => cutOf pp n y.2.steps = (r.steps, r.pending, r.pendingOrder) |
      (genHandler pp (.inl (.inl (.inr gq)))).run g] =
      Pr[fun z => (g.steps, (some (.inl (.inl (.inr gq))) : Option (AdvModel P0).Domain),
        some (g.order ++ newGuesses pp g.shadow z.2 gq)) = (r.steps, r.pending, r.pendingOrder) |
        (referenceGroup pp g.oracle.issuedT gq).run g.shadow] := by
    rw [gen_group, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    congr 1
    funext z
    split_ifs with hm
    · rw [probEvent_eq_one_iff.mpr ⟨probFailure_eq_zero, ?_⟩, mul_one]
      intro y hy
      rw [mem_support_bind_iff] at hy
      obtain ⟨w, _, hy⟩ := hy
      rw [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      rw [← hm]
      exact hcut _
    · rw [probEvent_eq_zero_iff.mpr ?_, mul_zero]
      intro y hy hc
      apply hm
      rw [mem_support_bind_iff] at hy
      obtain ⟨w, _, hy⟩ := hy
      rw [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      rw [← hc]
      exact (hcut ⟨⟨.inl (.inl (.inr gq)), w.1⟩, z.2,
        g.order ++ newGuesses pp g.shadow z.2 gq⟩).symm
  rw [hgen]
  refine (Finset.sum_le_sum (fun σ _ => hreal σ)).trans ?_
  by_cases hpre : g.steps = r.steps ∧ (some (.inl (.inl (.inr gq))) : Option (AdvModel P0).Domain) =
      r.pending ∧ r.pendingOrder.isSome
  · obtain ⟨h1, h2, h3⟩ := hpre
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp h3
    have hsum : ∑ σ ∈ W, (if (g.steps, (some (.inl (.inl (.inr gq))) : Option (AdvModel P0).Domain),
          some (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq)) =
            (r.steps, r.pending, r.pendingOrder) then (1 : ℝ≥0∞) else 0) =
        ((W.filter fun σ => g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq = L).card :
          ℝ≥0∞) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [h1, h2, hL, Prod.mk.injEq, true_and, Option.some.injEq]
      split_ifs <;> simp
    have hev : Pr[fun z => (g.steps, (some (.inl (.inl (.inr gq))) : Option (AdvModel P0).Domain),
        some (g.order ++ newGuesses pp g.shadow z.2 gq)) = (r.steps, r.pending, r.pendingOrder) |
        (referenceGroup pp g.oracle.issuedT gq).run g.shadow] =
        Pr[fun z => g.order ++ newGuesses pp g.shadow z.2 gq = L |
          (referenceGroup pp g.oracle.issuedT gq).run g.shadow] := by
      congr 1
      funext z
      simp only [h1, h2, hL, Prod.mk.injEq, true_and, Option.some.injEq]
    rw [hsum, hev]
    exact hpend g gq W L hI h1.symm (hS h1.symm) hL hW
  · have hz : ∀ σ ∈ W, (if (g.steps, (some (.inl (.inl (.inr gq))) : Option (AdvModel P0).Domain),
          some (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq)) =
            (r.steps, r.pending, r.pendingOrder) then (1 : ℝ≥0∞) else 0) = 0 := by
      intro σ _
      rw [if_neg]
      intro h
      simp only [Prod.mk.injEq] at h
      exact hpre ⟨h.1, h.2.1, by rw [← h.2.2]; rfl⟩
    rw [Finset.sum_eq_zero hz]
    exact zero_le

lemma obs_kdf_target (σ : LabelEncoding P0) (g : GenState pp) (kq : KdfQuery P0)
    (ht : kdfName g.oracle kq = some (tname pp c.val σ)) :
    ∀ y ∈ support ((obsHandler pp σ c.val (.inr kq)).run (lift pp c.val pad σ g)),
      y.2.stop = some g.steps.length := by
  intro y hy
  have hbad : KdfTarget pp σ c.val (cacheT (tname pp c.val σ) pad g.oracle) kq := by
    cases kq <;> simpa [KdfTarget, kdfName, tname, cacheT] using ht
  simp only [obsHandler, lift, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨z, _, rfl⟩ := hy
  simp [hbad]

lemma bad_zero {α : Type} (σ : LabelEncoding P0) (t : (AdvModel P0).Domain)
    (cont : (AdvModel P0).Range t → OracleComp (AdvModel P0) α) (st : ObsState pp)
    (b : ℕ) (hb : b < n)
    (hstop : ∀ y ∈ support ((obsHandler pp σ c.val t).run st), y.2.stop = some b) :
    Pr[fun z => RGood pp n r z.2 | (obsHandler pp σ c.val t).run st >>= fun y =>
      (simulateQ (obsHandler pp σ c.val) (cont y.1)).run y.2] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz hg
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  have h1 := (obs_run_support pp σ c.val (cont y.1) y.2 z hz).2 b (hstop y hy)
  have := hg.1 b h1
  omega

section Group

variable {α : Type} (gq : GQuery P0)
  (cont : (AdvModel P0).Range (.inl (.inl (.inr gq))) → OracleComp (AdvModel P0) α)
  (g : GenState pp)

lemma group_summand (σ : LabelEncoding P0) (hlen : g.steps.length < n) :
    Pr[fun z => RGood pp n r z.2 |
        (obsHandler pp σ c.val (.inl (.inl (.inr gq)))).run (lift pp c.val pad σ g) >>= fun y =>
          (simulateQ (obsHandler pp σ c.val) (cont y.1)).run y.2] =
      if (realShadow pp σ g gq).first = none then
        ∑' w, Pr[= w | (finishGroup gq (realResult pp σ g gq)).run g.oracle] *
          Pr[fun z => RGood pp n r z.2 | (simulateQ (obsHandler pp σ c.val) (cont w.1)).run
            (lift pp c.val pad σ (afterGroup pp g gq (realShadow pp σ g gq) w))]
      else 0 := by
  split_ifs with hcl
  · rw [obs_group, bind_map_left, probEvent_bind_eq_tsum]
    congr 1
    funext w
    congr 2
    simp only [lift, afterGroup, hcl, Option.isSome_none, Bool.false_eq_true, if_false]
  · apply bad_zero pp n r c σ _ cont _ g.steps.length hlen
    intro y hy
    rw [obs_group, support_map] at hy
    obtain ⟨w, _, rfl⟩ := hy
    have hs : (realShadow pp σ g gq).first.isSome = true := by
      cases h : (realShadow pp σ g gq).first with
      | none => exact absurd h hcl
      | some _ => rfl
    simp only [hs, if_true]

lemma group_generic :
    Pr[fun z => GGood pp n r z.2 | (genHandler pp (.inl (.inl (.inr gq)))).run g >>= fun y =>
        (simulateQ (genHandler pp) (cont y.1)).run y.2] =
      ∑' z, Pr[= z | (referenceGroup pp g.oracle.issuedT gq).run g.shadow] *
        ∑' w, Pr[= w | (finishGroup gq z.1).run g.oracle] *
          Pr[fun z' => GGood pp n r z'.2 |
            (simulateQ (genHandler pp) (cont w.1)).run (afterGroup pp g gq z.2 w)] := by
  rw [gen_group, bind_assoc, probEvent_bind_eq_tsum]
  congr 1
  funext z
  congr 1
  rw [bind_assoc, probEvent_bind_eq_tsum]
  simp only [pure_bind]

lemma afterGroup_inv (sh : State pp) (w : gq.Answer × OracleState P0) (hI : Inv pp g)
    (hf : sh.first = none)
    (hcov : Cover pp (afterGroup pp g gq sh w) ∧ VarsIn pp (afterGroup pp g gq sh w) ∧
      OrdGuess pp (afterGroup pp g gq sh w)) :
    Inv pp (afterGroup pp g gq sh w) := by
  refine ⟨hf, ?_, hcov.1, hcov.2.1, hcov.2.2⟩
  intro s hs
  simp only [afterGroup, List.mem_append, List.mem_singleton] at hs ⊢
  rcases hs with hs | rfl
  · exact (hI.2.1 s hs).trans (List.prefix_append _ _)
  · exact List.prefix_refl _

lemma group_fiber (hcons : ConsStep pp r c x) (hcover : CoverStep pp c x)
    (hcount : CountStep pp n r c x) (hr : RMono pp r)
    (ih : ∀ u, IndStmt pp n r c x pad (cont u)) (hI : Inv pp g) (hlen : g.steps.length < n)
    (Wz : Finset (LabelEncoding P0)) (R : gq.Result) (sh : State pp)
    (σ₀ : LabelEncoding P0) (hσ₀ : σ₀ ∈ Wz)
    (hWz : ∀ σ ∈ Wz, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x ∧
      realResult pp σ g gq = R ∧ realShadow pp σ g gq = sh ∧ sh.first = none) :
    ∑ σ ∈ Wz, ∑' w, Pr[= w | (finishGroup gq R).run g.oracle] *
        Pr[fun z => RGood pp n r z.2 | (simulateQ (obsHandler pp σ c.val) (cont w.1)).run
          (lift pp c.val pad σ (afterGroup pp g gq sh w))] ≤
      ∑' w, Pr[= w | (finishGroup gq R).run g.oracle] *
        ((cons pp g.shadow g.order c x).card *
          Pr[= (R, sh) | (referenceGroup pp g.oracle.issuedT gq).run g.shadow] *
          guessFactor pp r c x g.order.length *
          Pr[fun z => GGood pp n r z.2 |
            (simulateQ (genHandler pp) (cont w.1)).run (afterGroup pp g gq sh w)]) := by
  rw [sum_tsum_swap]
  apply ENNReal.tsum_le_tsum
  intro w
  rw [← Finset.mul_sum]
  by_cases hw : w ∈ support ((finishGroup gq R).run g.oracle)
  swap
  · rw [(probOutput_eq_zero_iff _ _).mpr hw, zero_mul, zero_mul]
  apply mul_le_mul' le_rfl
  obtain ⟨hc0, hg0, hR0, hsh0, hcl⟩ := hWz σ₀ hσ₀
  subst hR0 hsh0
  by_cases hm' : r.steps[g.steps.length]? =
      (afterGroup pp g gq (realShadow pp σ₀ g gq) w).steps[g.steps.length]? ∧
      g.steps <+: r.steps
  · obtain ⟨hm, hgp⟩ := hm'
    have hstep : (afterGroup pp g gq (realShadow pp σ₀ g gq) w).steps[g.steps.length]? =
        some ⟨⟨.inl (.inl (.inr gq)), w.1⟩, realShadow pp σ₀ g gq,
          (afterGroup pp g gq (realShadow pp σ₀ g gq) w).order⟩ := by
      simp [afterGroup]
    have hpre : (afterGroup pp g gq (realShadow pp σ₀ g gq) w).order <+: r.order := by
      rw [hstep] at hm
      exact hr _ (List.mem_of_getElem? hm)
    have hsub : ∀ σ ∈ Wz, σ ∈ cons pp (afterGroup pp g gq (realShadow pp σ₀ g gq) w).shadow
        (afterGroup pp g gq (realShadow pp σ₀ g gq) w).order c x ∧ guessValuesσ pp r σ = x := by
      intro σ hσ
      obtain ⟨hc, hgv, _, hsh, _⟩ := hWz σ hσ
      refine ⟨?_, hgv⟩
      have hcl' : (realShadow pp σ g gq).first = none := by rw [hsh]; exact hcl
      have h := hcons g gq σ hI hc hgv hcl' (by rw [hsh]; exact hpre)
      rw [hsh] at h
      exact h
    have hInv : Inv pp (afterGroup pp g gq (realShadow pp σ₀ g gq) w) :=
      afterGroup_inv pp gq g _ w hI hcl (hcover g gq σ₀ w hI hc0 hw hcl)
    have hih := ih w.1 (afterGroup pp g gq (realShadow pp σ₀ g gq) w) Wz hInv
      (shadowOf_of_last pp r _ g.steps _ rfl rfl) hsub
    have hcnt := hcount g gq σ₀ w hI hlen hr hgp hc0 hg0 hcl hw hm
    calc
      _ ≤ _ := hih
      _ = ((cons pp (realShadow pp σ₀ g gq)
            (afterGroup pp g gq (realShadow pp σ₀ g gq) w).order c x).card *
            guessFactor pp r c x (afterGroup pp g gq (realShadow pp σ₀ g gq) w).order.length) *
          Pr[fun z => GGood pp n r z.2 | (simulateQ (genHandler pp) (cont w.1)).run
            (afterGroup pp g gq (realShadow pp σ₀ g gq) w)] := by
        simp only [afterGroup]
        ring
      _ ≤ _ := mul_le_mul' hcnt le_rfl
  · rw [Finset.sum_eq_zero]
    · exact zero_le
    intro σ _
    rw [probEvent_eq_zero_iff]
    intro z hz hg
    apply hm'
    obtain ⟨⟨more, hmore⟩, _⟩ := obs_run_support pp σ c.val (cont w.1) _ z hz
    have ht : z.2.steps.take n = r.steps := congrArg Prod.fst hg.2
    have hl : g.steps.length <
        (lift pp c.val pad σ (afterGroup pp g gq (realShadow pp σ₀ g gq) w)).steps.length := by
      simp [lift, afterGroup]
    refine ⟨?_, ?_⟩
    · rw [← ht, List.getElem?_take_of_lt hlen, ← hmore, List.getElem?_append_left hl]
      rfl
    · rw [← ht, ← hmore]
      have hpre : g.steps <+: (lift pp c.val pad σ
          (afterGroup pp g gq (realShadow pp σ₀ g gq) w)).steps ++ more := by
        simp only [lift, afterGroup, List.append_assoc]
        exact List.prefix_append _ _
      exact (List.prefix_take_iff.mpr ⟨hpre, hlen.le⟩)

lemma ind_group (hcons : ConsStep pp r c x) (hcover : CoverStep pp c x)
    (hcount : CountStep pp n r c x) (hr : RMono pp r)
    (ih : ∀ u, IndStmt pp n r c x pad (cont u)) (W : Finset (LabelEncoding P0)) (hI : Inv pp g)
    (hW : ∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x)
    (hlen : g.steps.length < n) :
    ∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 |
        (obsHandler pp σ c.val (.inl (.inl (.inr gq)))).run (lift pp c.val pad σ g) >>= fun y =>
          (simulateQ (obsHandler pp σ c.val) (cont y.1)).run y.2] ≤
      (cons pp g.shadow g.order c x).card *
        Pr[fun z => GGood pp n r z.2 | (genHandler pp (.inl (.inl (.inr gq)))).run g >>= fun y =>
          (simulateQ (genHandler pp) (cont y.1)).run y.2] *
        guessFactor pp r c x g.order.length := by
  set C : ℝ≥0∞ := ((cons pp g.shadow g.order c x).card : ℝ≥0∞) with hC
  set γ : ℝ≥0∞ := guessFactor pp r c x g.order.length with hγ
  let key : LabelEncoding P0 → gq.Result × State pp := fun σ =>
    (realResult pp σ g gq, realShadow pp σ g gq)
  let Wc := W.filter fun σ => (realShadow pp σ g gq).first = none
  let Gz : gq.Result × State pp → ℝ≥0∞ := fun z =>
    ∑' w, Pr[= w | (finishGroup gq z.1).run g.oracle] *
      Pr[fun z' => GGood pp n r z'.2 |
        (simulateQ (genHandler pp) (cont w.1)).run (afterGroup pp g gq z.2 w)]
  calc
    _ = ∑ σ ∈ W, if (realShadow pp σ g gq).first = none then
          ∑' w, Pr[= w | (finishGroup gq (realResult pp σ g gq)).run g.oracle] *
            Pr[fun z => RGood pp n r z.2 | (simulateQ (obsHandler pp σ c.val) (cont w.1)).run
              (lift pp c.val pad σ (afterGroup pp g gq (realShadow pp σ g gq) w))]
          else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      exact group_summand pp n r c pad gq cont g σ hlen
    _ = ∑ σ ∈ Wc, ∑' w, Pr[= w | (finishGroup gq (realResult pp σ g gq)).run g.oracle] *
            Pr[fun z => RGood pp n r z.2 | (simulateQ (obsHandler pp σ c.val) (cont w.1)).run
              (lift pp c.val pad σ (afterGroup pp g gq (realShadow pp σ g gq) w))] := by
      rw [Finset.sum_filter]
    _ = ∑ z ∈ Wc.image key, ∑ σ ∈ Wc with key σ = z,
          ∑' w, Pr[= w | (finishGroup gq z.1).run g.oracle] *
            Pr[fun z' => RGood pp n r z'.2 | (simulateQ (obsHandler pp σ c.val) (cont w.1)).run
              (lift pp c.val pad σ (afterGroup pp g gq z.2 w))] := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := Wc.image key)
        (fun σ hσ => Finset.mem_image_of_mem key hσ)]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro σ hσ
      have hk : key σ = z := (Finset.mem_filter.mp hσ).2
      rw [← hk]
    _ ≤ ∑ z ∈ Wc.image key, ∑' w, Pr[= w | (finishGroup gq z.1).run g.oracle] *
          (C * Pr[= z | (referenceGroup pp g.oracle.issuedT gq).run g.shadow] * γ *
            Pr[fun z' => GGood pp n r z'.2 |
              (simulateQ (genHandler pp) (cont w.1)).run (afterGroup pp g gq z.2 w)]) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨σ₀, hσ₀, hk0⟩ := Finset.mem_image.mp hz
      refine group_fiber pp n r c x pad gq cont g hcons hcover hcount hr ih hI hlen
        (Wc.filter fun σ => key σ = z) z.1 z.2 σ₀ ?_ ?_
      · exact Finset.mem_filter.mpr ⟨hσ₀, hk0⟩
      · intro σ hσ
        obtain ⟨hσW, hk⟩ := Finset.mem_filter.mp hσ
        obtain ⟨hσW', hcl⟩ := Finset.mem_filter.mp hσW
        refine ⟨(hW σ hσW').1, (hW σ hσW').2, congrArg Prod.fst hk, congrArg Prod.snd hk, ?_⟩
        rw [← congrArg Prod.snd hk]
        exact hcl
    _ = ∑ z ∈ Wc.image key, C * γ *
          (Pr[= z | (referenceGroup pp g.oracle.issuedT gq).run g.shadow] * Gz z) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Gz]
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
      congr 1
      funext w
      ring
    _ ≤ ∑' z, C * γ *
          (Pr[= z | (referenceGroup pp g.oracle.issuedT gq).run g.shadow] * Gz z) :=
      ENNReal.sum_le_tsum _
    _ = C * Pr[fun z => GGood pp n r z.2 | (genHandler pp (.inl (.inl (.inr gq)))).run g >>=
          fun y => (simulateQ (genHandler pp) (cont y.1)).run y.2] * γ := by
      rw [group_generic pp n r gq cont g, ENNReal.tsum_mul_left]
      ring

end Group

theorem ind (hcons : ConsStep pp r c x) (hcover : CoverStep pp c x)
    (hcount : CountStep pp n r c x) (hpend : PendingStep pp r c x) (hr : RMono pp r) {α : Type}
    (oa : OracleComp (AdvModel P0) α) : IndStmt pp n r c x pad oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ind_pure pp n r c x pad a
  | query_bind t cont ih =>
    intro g W hI hS hW
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    by_cases hlen : n < g.steps.length
    · exact ind_main pp n r c x pad t cont g W hI hW hlen
    by_cases hlen' : n = g.steps.length
    · rcases t with ((m | gq) | i) | kq
      · exact ind_pending_nongroup pp n r c x pad _ (by intro gq h; cases h) cont g W hW hlen'
      · exact ind_pending_group pp n r c x pad hpend gq cont g W hI hS hW hlen'
      · exact ind_pending_nongroup pp n r c x pad _ (by intro gq h; cases h) cont g W hW hlen'
      · exact ind_pending_nongroup pp n r c x pad _ (by intro gq h; cases h) cont g W hW hlen'
    have hlen : g.steps.length < n := by omega
    have hcomm_case : ∀ (t' : (AdvModel P0).Domain) (ht' : ∀ gq, t' ≠ .inl (.inl (.inr gq)))
        (cont' : (AdvModel P0).Range t' → OracleComp (AdvModel P0) α)
        (ih' : ∀ u, IndStmt pp n r c x pad (cont' u)) (W' : Finset (LabelEncoding P0)),
        (∀ σ ∈ W', σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x) →
        (∀ σ ∈ W', (obsHandler pp σ c.val t').run (lift pp c.val pad σ g) =
          (fun z => (z.1, lift pp c.val pad σ z.2)) <$> (genHandler pp t').run g) →
        ∑ σ ∈ W', Pr[fun z => RGood pp n r z.2 | (obsHandler pp σ c.val t').run
            (lift pp c.val pad σ g) >>= fun y =>
              (simulateQ (obsHandler pp σ c.val) (cont' y.1)).run y.2] ≤
          (cons pp g.shadow g.order c x).card *
            Pr[fun z => GGood pp n r z.2 | (genHandler pp t').run g >>= fun y =>
              (simulateQ (genHandler pp) (cont' y.1)).run y.2] *
            guessFactor pp r c x g.order.length := by
      intro t' ht' cont' ih' W' hW' hcomm
      have h := sum_commuting pp n r c.val pad t' cont' g W'
        ((cons pp g.shadow g.order c x).card * guessFactor pp r c x g.order.length) hcomm
        (by
          intro y hy
          obtain ⟨hIy, hsy, hoy⟩ := inv_nongroup pp t' ht' g hI y hy
          obtain ⟨_, _, _, hst⟩ := gen_nongroup_support pp t' ht' g y hy
          have hSy : ShadowOf pp r y.2 := shadowOf_of_last pp r y.2 g.steps _ hst hsy.symm
          have := ih' y.1 y.2 W' hIy hSy (by rw [hsy, hoy]; exact hW')
          rw [hsy, hoy] at this
          calc _ ≤ _ := this
            _ = _ := by ring)
      calc _ ≤ _ := h
        _ = _ := by ring
    rcases t with ((m | gq) | i) | kq
    · exact hcomm_case _ (by intro gq h; cases h) cont ih W hW
        (fun σ _ => obs_unif pp c.val pad σ g hI.1 m)
    · exact ind_group pp n r c x pad gq cont g hcons hcover hcount hr ih W hI hW hlen
    · exact hcomm_case _ (by intro gq h; cases h) cont ih W hW
        (fun σ _ => obs_hf pp c.val pad σ g hI.1 i)
    ·
      let Wnt := W.filter fun σ => kdfName g.oracle kq ≠ some (tname pp c.val σ)
      rw [← Finset.sum_filter_add_sum_filter_not W
        (fun σ => kdfName g.oracle kq ≠ some (tname pp c.val σ))]
      have hzero : ∑ σ ∈ W with ¬ (kdfName g.oracle kq ≠ some (tname pp c.val σ)),
          Pr[fun z => RGood pp n r z.2 | (obsHandler pp σ c.val (.inr kq)).run
            (lift pp c.val pad σ g) >>= fun y =>
              (simulateQ (obsHandler pp σ c.val) (cont y.1)).run y.2] = 0 := by
        apply Finset.sum_eq_zero
        intro σ hσ
        have ht : kdfName g.oracle kq = some (tname pp c.val σ) := by
          have := (Finset.mem_filter.mp hσ).2
          push Not at this
          exact this
        exact bad_zero pp n r c σ _ cont _ g.steps.length hlen
          (obs_kdf_target pp c pad σ g kq ht)
      rw [hzero, add_zero]
      exact hcomm_case _ (by intro gq h; cases h) cont ih Wnt
        (fun σ hσ => hW σ (Finset.mem_filter.mp hσ).1)
        (fun σ hσ => obs_kdf pp c.val pad σ g hI.1 kq (Finset.mem_filter.mp hσ).2)

end Induction

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation
