import Praxis.Proofs.Query.Ops
import Praxis.Proofs.KeyOracle
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Reduction

namespace Praxis.Proofs.Query

open OracleComp OracleSpec

private theorem idealEvent_preserves_mark {P : Params} (cx : IdealCtx P)
    (st : IdealState P) (e : MonEvent P) (h : st.mark ≠ none) :
    (idealEvent cx st e).mark ≠ none := by
  unfold idealEvent
  cases hm : st.mark with
  | none => exact False.elim (h hm)
  | some k => exact h

private theorem idealEvents_preserve_mark {P : Params} (cx : IdealCtx P)
    (es : List (MonEvent P)) (st : IdealState P) (h : st.mark ≠ none) :
    (es.foldl (idealEvent cx) st).mark ≠ none := by
  induction es generalizing st with
  | nil => exact h
  | cons e es ih => exact ih _ (idealEvent_preserves_mark cx st e h)

private theorem idealKdf_target_marked {P : Params} (cx : IdealCtx P)
    (st : IdealState P) : (idealKdf cx st cx.target).mark ≠ none := by
  classical
  unfold idealKdf
  simp only [ite_true]
  split
  · simp
  · split <;> simp

private theorem idealEvents_target_marked {P : Params} (cx : IdealCtx P)
    (es : List (MonEvent P)) (st : IdealState P) (h : MonEvent.kdf cx.target ∈ es) :
    (es.foldl (idealEvent cx) st).mark ≠ none := by
  induction es generalizing st with
  | nil => simp at h
  | cons e es ih =>
    rcases List.mem_cons.mp h with he | he
    · subst e
      change (es.foldl (idealEvent cx) (idealEvent cx st (.kdf cx.target))).mark ≠ none
      apply idealEvents_preserve_mark cx es
      unfold idealEvent
      cases hm : st.mark with
      | none => exact idealKdf_target_marked cx st
      | some k => simp [hm]
    · exact ih _ he

private theorem kdf_mem_monEvents {P : Params} (tr : List (TrOp P))
    (kl : List (ℕ × ClassName P)) (e : ℕ × ClassName P) (he : e ∈ kl)
    (hi : e.1 ≤ tr.length) : MonEvent.kdf e.2 ∈ monEvents tr kl := by
  unfold monEvents
  apply List.mem_flatMap.mpr
  refine ⟨e.1, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨e, List.mem_filter.mpr ⟨he, by simp⟩, rfl⟩

private theorem kdfLazy_preserves_logs {P : Params} (nm : ClassName P)
    (st : OracleState P) (z : Msg P × OracleState P)
    (hz : z ∈ support ((kdfLazy nm).run st)) :
    z.2.tr = st.tr ∧ z.2.kdfLog = st.kdfLog := by
  unfold kdfLazy at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp at hz
    subst z
    exact ⟨rfl, rfl⟩
  · simp [StateT.run_bind, StateT.run_modify] at hz
    obtain ⟨a, rfl⟩ := hz
    exact ⟨rfl, rfl⟩

private theorem hfLazy_preserves_logs {P : Params} [NeZero P.q]
    (i : Seed P × FormIndex P) (st : OracleState P) (z : Rq P × OracleState P)
    (hz : z ∈ support ((hfLazy i).run st)) :
    z.2.tr = st.tr ∧ z.2.kdfLog = st.kdfLog := by
  unfold hfLazy at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp at hz
    subst z
    exact ⟨rfl, rfl⟩
  · simp [StateT.run_bind, StateT.run_modify] at hz
    obtain ⟨a, rfl⟩ := hz
    exact ⟨rfl, rfl⟩

private theorem nameRef_preserves_logs {P : Params} (nm : ClassName P)
    (st : OracleState P) (z : NameRef × OracleState P)
    (hz : z ∈ support ((nameRef nm).run st)) :
    z.2.tr = st.tr ∧ z.2.kdfLog = st.kdfLog := by
  unfold nameRef at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz <;> simp [StateT.run_set] at hz <;> subst z <;> exact ⟨rfl, rfl⟩

private theorem handOut_preserves_logs {P : Params} (qr : GQuery P) (r : qr.Result)
    (st : OracleState P) (z : qr.Answer × OracleState P)
    (hz : z ∈ support ((handOut qr r).run st)) :
    z.2.tr = st.tr ∧ z.2.kdfLog = st.kdfLog := by
  cases qr with
  | lin => simpa [handOut] using hz ▸ (And.intro rfl rfl : st.tr = st.tr ∧ st.kdfLog = st.kdfLog)
  | pair => simpa [handOut] using hz ▸ (And.intro rfl rfl : st.tr = st.tr ∧ st.kdfLog = st.kdfLog)
  | name u =>
    cases r with
    | none =>
      simp [handOut] at hz
      subst z
      exact ⟨rfl, rfl⟩
    | some nm =>
      simp only [handOut, StateT.run_map, support_map, Set.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact nameRef_preserves_logs nm st y hy

private theorem groupImpl_log_positions {P : Params} (σ : LabelEncoding P)
    (qr : GQuery P) (st : OracleState P)
    (hs : ∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length)
    (z : qr.Answer × OracleState P) (hz : z ∈ support ((groupImpl σ qr).run st)) :
    ∀ e ∈ z.2.kdfLog, e.1 ≤ z.2.tr.length := by
  unfold groupImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases htr : trEntry qr (groupAnswer σ st.issuedT qr) with
  | none =>
    simp only [htr] at hz
    obtain ⟨ht, hl⟩ := handOut_preserves_logs qr _ _ z hz
    simpa only [ht, hl] using hs
  | some op =>
    simp only [htr] at hz
    obtain ⟨ht, hl⟩ := handOut_preserves_logs qr _ _ z hz
    rw [ht, hl]
    intro e he
    exact (hs e he).trans (by simp)

private theorem loggedKdf_log_positions {P : Params} (nm : ClassName P)
    (st : OracleState P) (hs : ∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length)
    (z : Option (Msg P) × OracleState P)
    (hz : z ∈ support ((fun y : Msg P × OracleState P => (some y.1, y.2)) <$>
      (kdfLazy nm).run { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] })) :
    ∀ e ∈ z.2.kdfLog, e.1 ≤ z.2.tr.length := by
  rw [support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨ht, hl⟩ := kdfLazy_preserves_logs _ _ y hy
  rw [ht, hl]
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hs e he
  · have he' : e = (st.tr.length, nm) := List.mem_singleton.mp he
    subst e
    exact Nat.le_refl _

private theorem kdfImpl_log_positions {P : Params} (qk : KdfQuery P)
    (st : OracleState P) (hs : ∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length)
    (z : Option (Msg P) × OracleState P) (hz : z ∈ support ((kdfImpl qk).run st)) :
    ∀ e ∈ z.2.kdfLog, e.1 ≤ z.2.tr.length := by
  cases qk with
  | ref k =>
    cases hnm : st.names[k]? with
    | none =>
      simp [kdfImpl, StateT.run_bind, hnm] at hz
      subst z
      exact hs
    | some nm =>
      apply loggedKdf_log_positions nm st hs z
      simpa only [kdfImpl, StateT.run_bind, StateT.run_get, StateT.run_modify,
        StateT.run_map, pure_bind, hnm] using hz
  | guess nm =>
    apply loggedKdf_log_positions nm st hs z
    simpa only [kdfImpl, StateT.run_bind, StateT.run_get, StateT.run_modify,
      StateT.run_map, pure_bind] using hz

private theorem gameImpl_log_positions {P : Params} [NeZero P.q]
    (σ : LabelEncoding P) (t : (AdvModel P).Domain) (st : OracleState P)
    (hs : ∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length)
    (z : (AdvModel P).Range t × OracleState P)
    (hz : z ∈ support ((gameImpl σ t).run st)) :
    ∀ e ∈ z.2.kdfLog, e.1 ≤ z.2.tr.length := by
  rcases t with ((t | t) | t) | t
  · simp [gameImpl] at hz
    obtain ⟨a, rfl⟩ := hz
    exact hs
  · exact groupImpl_log_positions σ t st hs z hz
  · obtain ⟨ht, hl⟩ := hfLazy_preserves_logs t st z hz
    simpa only [ht, hl] using hs
  · exact kdfImpl_log_positions t st hs z hz

private theorem simulateQ_log_positions {P : Params} [NeZero P.q]
    (σ : LabelEncoding P) {α : Type} (oa : OracleComp (AdvModel P) α)
    (st : OracleState P) (hs : ∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length) :
    ∀ z ∈ support ((simulateQ (gameImpl σ) oa).run st),
      ∀ e ∈ z.2.kdfLog, e.1 ≤ z.2.tr.length := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simpa using hs
  | query_bind t k ih =>
    intro z hz
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact ih y.1 y.2 (gameImpl_log_positions σ t st hs y hy) z hz

private theorem worldRun_log_positions {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) (A : Adversary P)
    (henc : ∀ (σ : LabelEncoding P) es,
      es ∈ support ((encGame σ pp m).run OracleState.empty) → es.2.kdfLog = [])
    (w : WorldOut P) (hw : w ∈ support (worldRun pp m A)) :
    ∀ e ∈ w.st.kdfLog, e.1 ≤ w.st.tr.length := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  unfold worldRun at hw
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨σ, _, r, hr, rfl⟩ := hw
  unfold runWith at hr
  simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨es, hes, z, hz, rfl⟩ := hr
  have hlog := henc σ es hes
  exact simulateQ_log_positions σ (A.run es.1.pv es.1.header) es.2
    (by simp [hlog]) z hz

private theorem target_marked_of_log_positions {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (w : WorldOut P)
    (hpos : ∀ e ∈ w.st.kdfLog, e.1 ≤ w.st.tr.length)
    (hq : TargetQueried pp w) : firstMark pp w ≠ none := by
  obtain ⟨e, he, ht⟩ := hq
  unfold firstMark idealMonitor
  apply idealEvents_target_marked
  change MonEvent.kdf (targetName pp w) ∈ monEvents w.st.tr w.st.kdfLog
  rw [← ht]
  exact kdf_mem_monEvents _ _ e he (hpos e he)

private theorem encGame_log_empty (σ : LabelEncoding P0) (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0)
    (es : EncOut P0 × OracleState P0)
    (hes : es ∈ support ((encGame σ pp m).run OracleState.empty)) :
    es.2.kdfLog = [] := by
  have h := KeyOracle.enc_target_cache σ pp m es hes
  exact h.2.1

private theorem target_marked_general {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) (A : Adversary P)
    (henc : ∀ (σ : LabelEncoding P) es,
      es ∈ support ((encGame σ pp m).run OracleState.empty) → es.2.kdfLog = []) :
    ∀ w ∈ support (worldRun pp m A), TargetQueried pp w → firstMark pp w ≠ none := by
  intro w hw hq
  exact target_marked_of_log_positions pp w (worldRun_log_positions pp m A henc w hw) hq

theorem target_marked (pp : PublicParams P0) [Nonempty {c : Coins P0 // ValidCoins pp.qap c}]
    (m : Msg P0) (A : Adversary P0) :
    ∀ w ∈ support (worldRun pp m A), TargetQueried pp w → firstMark pp w ≠ none := by
  exact target_marked_general pp m A (fun σ es hes => encGame_log_empty σ pp m es hes)

end Praxis.Proofs.Query
