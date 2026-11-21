import Praxis.Proofs.KeyOracle
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Relation
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Coupling

open OracleComp OracleSpec

variable {P : Params}

def Agree (n : ClassName P) (s t : OracleState P) : Prop :=
  s.hf = t.hf ∧ s.tr = t.tr ∧ s.kdfLog = t.kdfLog ∧
    s.issuedT = t.issuedT ∧ s.names = t.names ∧
      ∀ k, k ≠ n → s.kdf k = t.kdf k

def Avoids (n : ClassName P) (s : OracleState P) : Prop :=
  ∀ e ∈ s.kdfLog, e.2 ≠ n

theorem avoids_iff (n : ClassName P) (s : OracleState P) :
    Avoids n s ↔ ¬ ∃ e ∈ s.kdfLog, e.2 = n := by
  constructor
  · intro h ⟨e, he, hn⟩
    exact h e he hn
  · intro h e he hn
    exact h ⟨e, he, hn⟩

theorem hfLazy_log [NeZero P.q] (i : Seed P × FormIndex P) (s : OracleState P)
    (z : Rq P × OracleState P) (hz : z ∈ support ((hfLazy i).run s)) :
    z.2.kdfLog = s.kdfLog ∧ z.2.names = s.names := by
  classical
  cases h : s.hf i <;>
    simp [hfLazy, h, StateT.run_bind, StateT.run_lift] at hz <;>
    rcases hz with ⟨a, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem kdfLazy_log (n : ClassName P) (s : OracleState P)
    (z : Msg P × OracleState P) (hz : z ∈ support ((kdfLazy n).run s)) :
    z.2.kdfLog = s.kdfLog ∧ z.2.names = s.names := by
  classical
  cases h : s.kdf n <;>
    simp [kdfLazy, h, StateT.run_bind, StateT.run_lift] at hz <;>
    rcases hz with ⟨a, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem handOut_log (q : GQuery P) (r : q.Result) (s : OracleState P)
    (z : q.Answer × OracleState P) (hz : z ∈ support ((handOut q r).run s)) :
    z.2.kdfLog = s.kdfLog := by
  classical
  cases q with
  | lin a b c d e =>
    simp [handOut] at hz
    subst z
    rfl
  | pair u v =>
    simp [handOut] at hz
    subst z
    rfl
  | name v =>
    cases r with
    | none =>
      simp [handOut] at hz
      subst z
      rfl
    | some nm =>
      cases h : s.names.findIdx? (· == nm) <;>
        simp [handOut, nameRef, h] at hz <;> subst z <;> rfl

theorem groupImpl_log (σ : LabelEncoding P) (q : GQuery P) (s : OracleState P)
    (z : q.Answer × OracleState P) (hz : z ∈ support ((groupImpl σ q).run s)) :
    z.2.kdfLog = s.kdfLog := by
  classical
  cases h : trEntry q (groupAnswer σ s.issuedT q) with
  | none =>
    simp only [groupImpl, StateT.run_bind, StateT.run_get, pure_bind, h] at hz
    exact handOut_log q _ s z hz
  | some e =>
    simp only [groupImpl, StateT.run_bind, StateT.run_get, pure_bind, h,
      StateT.run_modify] at hz
    have hlog := handOut_log q _ _ z hz
    exact hlog

theorem kdfImpl_log_mono (q : KdfQuery P) (s : OracleState P)
    (z : Option (Msg P) × OracleState P) (hz : z ∈ support ((kdfImpl q).run s)) :
    ∀ e ∈ s.kdfLog, e ∈ z.2.kdfLog := by
  classical
  cases q with
  | ref k =>
    cases h : s.names[k]? with
    | none =>
      simp [kdfImpl, h] at hz
      subst z
      exact fun _ he => he
    | some nm =>
      simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind, h,
        StateT.run_modify, StateT.run_map, support_map, Set.mem_image] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      rw [(kdfLazy_log nm _ a ha).1]
      exact fun _ he => List.mem_append_left _ he
  | guess nm =>
    simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_modify, StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [(kdfLazy_log nm _ a ha).1]
    exact fun _ he => List.mem_append_left _ he

theorem gameImpl_log_mono [NeZero P.q] (σ : LabelEncoding P) (q : (AdvModel P).Domain)
    (s : OracleState P) (z : (AdvModel P).Range q × OracleState P)
    (hz : z ∈ support ((gameImpl σ q).run s)) :
    ∀ e ∈ s.kdfLog, e ∈ z.2.kdfLog := by
  rcases q with ((n | q) | i) | q
  · simp [gameImpl] at hz
    obtain ⟨a, rfl⟩ := hz
    exact fun _ he => he
  · rw [groupImpl_log σ q s z hz]
    exact fun _ he => he
  · rw [(hfLazy_log i s z hz).1]
    exact fun _ he => he
  · exact kdfImpl_log_mono q s z hz

theorem run_log_mono [NeZero P.q] (σ : LabelEncoding P) {α : Type}
    (c : OracleComp (AdvModel P) α) (s : OracleState P) (z : α × OracleState P)
    (hz : z ∈ support ((simulateQ (gameImpl σ) c).run s)) :
    ∀ e ∈ s.kdfLog, e ∈ z.2.kdfLog := by
  induction c using OracleComp.inductionOn generalizing s z with
  | pure a =>
    have he : z = (a, s) := by simpa using hz
    subst z
    exact fun _ he => he
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨a, ha, hz⟩ := hz
    intro e he
    exact ih a.1 a.2 z hz e (gameImpl_log_mono σ q s a ha e he)

theorem run_hit_zero [NeZero P.q] (σ : LabelEncoding P) (n : ClassName P) {α : Type}
    (c : OracleComp (AdvModel P) α) (B : α → Prop) (s : OracleState P)
    (hn : ¬ Avoids n s) :
    Pr[fun z => B z.1 ∧ Avoids n z.2 | (simulateQ (gameImpl σ) c).run s] = 0 := by
  classical
  apply probEvent_eq_zero
  intro z hz hB
  apply hn
  intro e he
  exact hB.2 e (run_log_mono σ c s z hz e he)

theorem hf_step_congr [NeZero P.q] (n : ClassName P) (i : Seed P × FormIndex P)
    {β : Type} (K : Rq P → OracleState P → ProbComp β) (B : β → Prop)
    (hK : ∀ a s t, Agree n s t → Pr[B | K a s] = Pr[B | K a t])
    (s t : OracleState P) (h : Agree n s t) :
    Pr[B | (hfLazy i).run s >>= fun z => K z.1 z.2] =
      Pr[B | (hfLazy i).run t >>= fun z => K z.1 z.2] := by
  classical
  rcases s with ⟨hf, ks, tr, log, issued, names⟩
  rcases t with ⟨hf', kt, tr', log', issued', names'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  cases hc : hf i with
  | some a =>
    simp only [hfLazy, StateT.run_bind, StateT.run_get, pure_bind, hc, StateT.run_pure]
    exact hK a _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  | none =>
    simp only [hfLazy, StateT.run_bind, StateT.run_get, pure_bind, hc,
      StateT.run_lift, bind_assoc, StateT.run_modify, StateT.run_pure]
    apply probEvent_bind_congr'
    intro a
    exact hK a _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩

theorem kdf_step_congr (n nm : ClassName P) (hne : nm ≠ n)
    {β : Type} (K : Msg P → OracleState P → ProbComp β) (B : β → Prop)
    (hK : ∀ a s t, Agree n s t → Pr[B | K a s] = Pr[B | K a t])
    (s t : OracleState P) (h : Agree n s t) :
    Pr[B | (kdfLazy nm).run s >>= fun z => K z.1 z.2] =
      Pr[B | (kdfLazy nm).run t >>= fun z => K z.1 z.2] := by
  classical
  rcases s with ⟨hf, ks, tr, log, issued, names⟩
  rcases t with ⟨hf', kt, tr', log', issued', names'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  have he : ks nm = kt nm := hk nm hne
  cases hc : kt nm with
  | some a =>
    simp only [kdfLazy, StateT.run_bind, StateT.run_get, pure_bind, he, hc,
      StateT.run_pure]
    exact hK a _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  | none =>
    simp only [kdfLazy, StateT.run_bind, StateT.run_get, pure_bind, he, hc,
      StateT.run_lift, bind_assoc, StateT.run_modify, StateT.run_pure]
    apply probEvent_bind_congr'
    intro a
    apply hK a
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro k hn
    by_cases heq : k = nm
    · subst k
      simp
    · simpa only [Function.update_of_ne heq] using hk k hn

theorem handOut_step_congr (n : ClassName P) (q : GQuery P) (r : q.Result)
    {β : Type} (K : q.Answer → OracleState P → ProbComp β) (B : β → Prop)
    (hK : ∀ a s t, Agree n s t → Pr[B | K a s] = Pr[B | K a t])
    (s t : OracleState P) (h : Agree n s t) :
    Pr[B | (handOut q r).run s >>= fun z => K z.1 z.2] =
      Pr[B | (handOut q r).run t >>= fun z => K z.1 z.2] := by
  classical
  rcases s with ⟨hf, ks, tr, log, issued, names⟩
  rcases t with ⟨hf', kt, tr', log', issued', names'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  cases q with
  | lin a b c d e =>
    simp only [handOut, StateT.run_pure, pure_bind]
    exact hK r _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  | pair u v =>
    simp only [handOut, StateT.run_pure, pure_bind]
    exact hK r _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  | name v =>
    cases r with
    | none =>
      simp only [handOut, StateT.run_pure, pure_bind]
      exact hK none _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
    | some nm =>
      cases hc : names.findIdx? (· == nm) <;>
        simp only [handOut, nameRef, StateT.run_map, StateT.run_bind,
          StateT.run_get, pure_bind, hc, StateT.run_pure, StateT.run_set, map_pure]
      all_goals exact hK _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩

theorem group_step_congr (σ : LabelEncoding P) (n : ClassName P) (q : GQuery P)
    {β : Type} (K : q.Answer → OracleState P → ProbComp β) (B : β → Prop)
    (hK : ∀ a s t, Agree n s t → Pr[B | K a s] = Pr[B | K a t])
    (s t : OracleState P) (h : Agree n s t) :
    Pr[B | (groupImpl σ q).run s >>= fun z => K z.1 z.2] =
      Pr[B | (groupImpl σ q).run t >>= fun z => K z.1 z.2] := by
  classical
  rcases s with ⟨hf, ks, tr, log, issued, names⟩
  rcases t with ⟨hf', kt, tr', log', issued', names'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  cases hc : trEntry q (groupAnswer σ issued q) <;>
    simp only [groupImpl, StateT.run_bind, StateT.run_get, pure_bind, hc,
      StateT.run_modify]
  all_goals apply handOut_step_congr n q _ K B hK
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, hk⟩

theorem kdf_hit_zero (n : ClassName P) {β : Type}
    (K : Msg P → OracleState P → ProbComp β) (B : β → Prop)
    (hzero : ∀ a s, ¬ Avoids n s → Pr[B | K a s] = 0)
    (s : OracleState P) (j : ℕ) :
    Pr[B | (kdfLazy n).run {s with kdfLog := s.kdfLog ++ [(j, n)]} >>=
      fun z => K z.1 z.2] = 0 := by
  classical
  rw [probEvent_bind_of_const (r := 0)]
  · simp
  · intro z hz
    apply hzero
    intro ha
    have hlog := (kdfLazy_log n _ z hz).1
    exact ha (j, n) (by rw [hlog]; simp) rfl

theorem kdfImpl_step_congr (n : ClassName P) (q : KdfQuery P)
    {β : Type} (K : Option (Msg P) → OracleState P → ProbComp β) (B : β → Prop)
    (hK : ∀ a s t, Agree n s t → Pr[B | K a s] = Pr[B | K a t])
    (hzero : ∀ a s, ¬ Avoids n s → Pr[B | K a s] = 0)
    (s t : OracleState P) (h : Agree n s t) :
    Pr[B | (kdfImpl q).run s >>= fun z => K z.1 z.2] =
      Pr[B | (kdfImpl q).run t >>= fun z => K z.1 z.2] := by
  classical
  rcases s with ⟨hf, ks, tr, log, issued, names⟩
  rcases t with ⟨hf', kt, tr', log', issued', names'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  cases q with
  | ref k =>
    cases hr : names[k]? with
    | none =>
      simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind, hr,
        StateT.run_pure]
      exact hK none _ _ ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
    | some nm =>
      simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind, hr,
        StateT.run_modify, StateT.run_map, bind_map_left]
      by_cases he : nm = n
      · subst nm
        rw [kdf_hit_zero n (fun a s => K (some a) s) B (fun a => hzero (some a))
          ⟨hf, ks, tr, log, issued, names⟩ tr.length,
          kdf_hit_zero n (fun a s => K (some a) s) B (fun a => hzero (some a))
          ⟨hf, kt, tr, log, issued, names⟩ tr.length]
      · apply kdf_step_congr n nm he (fun a s => K (some a) s) B
          (fun a => hK (some a))
        exact ⟨rfl, rfl, rfl, rfl, rfl, hk⟩
  | guess nm =>
    simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_modify, StateT.run_map, bind_map_left]
    by_cases he : nm = n
    · subst nm
      rw [kdf_hit_zero n (fun a s => K (some a) s) B (fun a => hzero (some a))
          ⟨hf, ks, tr, log, issued, names⟩ tr.length,
        kdf_hit_zero n (fun a s => K (some a) s) B (fun a => hzero (some a))
          ⟨hf, kt, tr, log, issued, names⟩ tr.length]
    · apply kdf_step_congr n nm he (fun a s => K (some a) s) B
        (fun a => hK (some a))
      exact ⟨rfl, rfl, rfl, rfl, rfl, hk⟩

set_option maxHeartbeats 1000000 in

theorem run_stopped_congr [NeZero P.q] (σ : LabelEncoding P) (n : ClassName P)
    {α : Type} (c : OracleComp (AdvModel P) α) (B : α → Prop)
    (s t : OracleState P) (h : Agree n s t) :
    Pr[fun z => B z.1 ∧ Avoids n z.2 | (simulateQ (gameImpl σ) c).run s] =
      Pr[fun z => B z.1 ∧ Avoids n z.2 | (simulateQ (gameImpl σ) c).run t] := by
  classical
  induction c using OracleComp.inductionOn generalizing s t with
  | pure a =>
    have ha : Avoids n s ↔ Avoids n t := by unfold Avoids; rw [h.2.2.1]
    simp [ha]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rcases q with ((u | q) | i) | q
    · change Pr[fun z => B z.1 ∧ Avoids n z.2 |
          (unifSpec.query u : ProbComp _) >>= fun a =>
            (simulateQ (gameImpl σ) (k a)).run s] =
        Pr[fun z => B z.1 ∧ Avoids n z.2 |
          (unifSpec.query u : ProbComp _) >>= fun a =>
            (simulateQ (gameImpl σ) (k a)).run t]
      exact probEvent_bind_congr' _ _ (fun a => ih a s t h)
    · exact group_step_congr σ n q _ _ ih s t h
    · exact hf_step_congr n i _ _ ih s t h
    · exact kdfImpl_step_congr n q _ _ ih
        (fun a s hs => run_hit_zero σ n (k a) B s hs) s t h

theorem hfReads_names [NeZero P.q] (seed : Seed P) (l : List (FormIndex P))
    (s : OracleState P) (z : List (FormIndex P × Rq P) × OracleState P)
    (hz : z ∈ support ((l.mapM fun i => do
      let a ← hfLazy (seed, i)
      pure (i, a)).run s)) : z.2.names = s.names := by
  induction l generalizing s z with
  | nil =>
    have he : z = ([], s) := by simpa using hz
    subst z
    rfl
  | cons i l ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, pure_bind,
      bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    exact (ih a.2 b hb).trans (hfLazy_log (seed, i) s a ha).2

theorem enc_names [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (z : EncOut P × OracleState P)
    (hz : z ∈ support ((encGame σ pp m).run OracleState.empty)) : z.2.names = [] := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [encGame, encAt, StateT.run_bind, StateT.run_lift, bind_assoc,
    pure_bind, StateT.run_modify, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨seed, _, es, hes, cs, _, pad, hpad, rfl⟩ := hz
  exact (kdfLazy_log _ es.2 pad hpad).2.trans (hfReads_names seed _ _ es hes)

def encPublic (r : EncOut P × OracleState P) :=
  (r.1.pv, r.1.header.seed, r.1.header.cm, r.1.forms, r.1.coins, r.2.hf, r.2.issuedT)

def publicInitial
    (r : PubView P × Seed P × Msg P × FormMatrix P × Coins P ×
      (Seed P × FormIndex P → Option (Rq P)) × Finset (Label P)) :
    EncOut P × OracleState P :=
  (⟨r.1, ⟨r.2.1, r.2.2.1⟩, r.2.2.2.1, r.2.2.2.2.1⟩,
    ⟨r.2.2.2.2.2.1, fun _ => none, [], [], r.2.2.2.2.2.2, []⟩)

theorem publicInitial_out (r : EncOut P × OracleState P) :
    (publicInitial (encPublic r)).1 = r.1 := by
  cases r with
  | mk e s => cases e; rfl

theorem enc_agree_public (σ : LabelEncoding P0) (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0)
    (r : EncOut P0 × OracleState P0)
    (hr : r ∈ support ((encGame σ pp m).run OracleState.empty)) :
    Agree (labelName (σ .gₜ) (kappa pp r.1.coins)) r.2 (publicInitial (encPublic r)).2 := by
  obtain ⟨hk, hl, ht⟩ := KeyOracle.enc_target_cache σ pp m r hr
  refine ⟨rfl, ht, hl, rfl, enc_names σ pp m r hr, ?_⟩
  intro k hn
  simp only [hk, Function.update_of_ne hn]
  rfl

noncomputable def stoppedLaw (σ : LabelEncoding P0) (pp : PublicParams P0)
    (A : Adversary P0) (o : Bool) (r : EncOut P0 × OracleState P0) : ProbComp Bool := by
  classical
  exact (fun z : Bool × OracleState P0 => decide
    (z.1 = o ∧ Avoids (labelName (σ .gₜ) (kappa pp r.1.coins)) z.2)) <$>
      (simulateQ (gameImpl σ) (A.run r.1.pv r.1.header)).run r.2

theorem stoppedLaw_public (σ : LabelEncoding P0) (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0)
    (A : Adversary P0) (o : Bool) (r : EncOut P0 × OracleState P0)
    (hr : r ∈ support ((encGame σ pp m).run OracleState.empty)) :
    Pr[= true | stoppedLaw σ pp A o r] =
      Pr[= true | stoppedLaw σ pp A o (publicInitial (encPublic r))] := by
  classical
  simp only [stoppedLaw, publicInitial_out, probOutput_map, decide_eq_true_eq]
  exact run_stopped_congr σ _ _ (· = o) _ _ (enc_agree_public σ pp m r hr)

theorem stopped_enc_indep (σ : LabelEncoding P0) (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m0 m1 : Msg P0)
    (A : Adversary P0) (o : Bool) :
    Pr[= true | (encGame σ pp m0).run OracleState.empty >>= stoppedLaw σ pp A o] =
      Pr[= true | (encGame σ pp m1).run OracleState.empty >>= stoppedLaw σ pp A o] := by
  let K := fun r => stoppedLaw σ pp A o (publicInitial r)
  have hcanon (m : Msg P0) :
      Pr[= true | (encGame σ pp m).run OracleState.empty >>= stoppedLaw σ pp A o] =
        Pr[= true | (encPublic <$> (encGame σ pp m).run OracleState.empty) >>= K] := by
    simp only [bind_map_left]
    exact probOutput_bind_congr (fun r hr => stoppedLaw_public σ pp m A o r hr)
  rw [hcanon m0, hcanon m1, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro r
  have h := evalSPMF_ext_iff.mp (KeyOracle.enc_public_indep σ pp m0 m1) r
  change Pr[= r | encPublic <$> (encGame σ pp m0).run OracleState.empty] =
    Pr[= r | encPublic <$> (encGame σ pp m1).run OracleState.empty] at h
  rw [h]

theorem world_stopped_eq (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0)
    (A : Adversary P0) (o : Bool) :
    Pr[fun w => w.o = o ∧ ¬ TargetQueried pp w | worldRun pp m A] =
      Pr[= true | do
        let σ ← (sampleEncoding : ProbComp (LabelEncoding P0))
        (encGame σ pp m).run OracleState.empty >>= stoppedLaw σ pp A o] := by
  classical
  simp only [worldRun, runWith, StateT.run_bind, StateT.run_map, stoppedLaw, bind_pure_comp, probEvent_bind_eq_tsum,
    probOutput_bind_eq_tsum, probEvent_map, probOutput_map, Function.comp_def,
    decide_eq_true_eq, TargetQueried, targetName, ← avoids_iff]

theorem couple_stopped (ch : AdmissibleChoice P0) (S : Relation P0) (A : Adversary P0)
    (m0 m1 : Msg P0) (o : Bool) :
    Pr[fun w => w.o = o ∧ ¬ TargetQueried (ppOf ch S) w | worldRun (ppOf ch S) m0 A] =
      Pr[fun w => w.o = o ∧ ¬ TargetQueried (ppOf ch S) w | worldRun (ppOf ch S) m1 A] := by
  rw [world_stopped_eq, world_stopped_eq]
  exact probOutput_bind_congr' _ true
    (fun σ => stopped_enc_indep σ (ppOf ch S) m0 m1 A o)

end Praxis.Proofs.Coupling
