import Praxis.Proofs.NamesInvariant
import Praxis.Proofs.NamesBudget
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesMonitor
import Praxis.Proofs.NamesPhase
import Praxis.Proofs.NamesReservoir
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting

namespace Praxis.Proofs.Names

open OracleComp OracleSpec

variable {P : Params}

def VisibleEq (st st' : OracleState P) : Prop :=
  st'.tr = st.tr ∧ st'.kdfLog = st.kdfLog ∧ st'.issuedT = st.issuedT

theorem VisibleEq.monitor (cx : IdealCtx P) (pv : PubView P) {st st' : OracleState P}
    (h : VisibleEq st st') : monitorState cx pv st' = monitorState cx pv st := by
  simp only [monitorState, h.1, h.2.1]

def RunInv (cx : IdealCtx P) (pv : PubView P) (l r : Label P)
    (st : OracleState P) (p : Reservoir.Phase) : Prop :=
  (∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length) ∧
    IssuedGood st.issuedT (monitorState cx pv st) ∧
    PhaseGood l r (monitorState cx pv st) p

theorem RunInv.visible (cx : IdealCtx P) (pv : PubView P) (l r : Label P)
    {st st' : OracleState P} (p : Reservoir.Phase) (h : RunInv cx pv l r st p)
    (he : VisibleEq st st') : RunInv cx pv l r st' p := by
  simpa only [RunInv, he.monitor cx pv, he.1, he.2.1, he.2.2] using h

theorem handOut_visible (qr : GQuery P) (r : qr.Result) (st : OracleState P) :
    ∀ z ∈ support ((handOut qr r).run st), VisibleEq st z.2 := by
  cases qr with
  | lin s a b u v => simp [handOut, VisibleEq]
  | pair u v => simp [handOut, VisibleEq]
  | name v =>
    cases r with
    | none => simp [handOut, VisibleEq]
    | some nm =>
      cases hn : st.names.findIdx? (· == nm) <;>
        simp [handOut, nameRef, StateT.run_map, StateT.run_bind, StateT.run_get,
          StateT.run_set, hn, VisibleEq]

theorem kdfLazy_visible (nm : ClassName P) (st : OracleState P) :
    ∀ z ∈ support ((kdfLazy nm).run st), VisibleEq st z.2 := by
  cases hk : st.kdf nm <;>
    simp [kdfLazy, StateT.run_bind, StateT.run_get, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, hk, VisibleEq]

theorem hfLazy_visible [NeZero P.q] (i : Seed P × FormIndex P) (st : OracleState P) :
    ∀ z ∈ support ((hfLazy i).run st), VisibleEq st z.2 := by
  cases hk : st.hf i <;>
    simp [hfLazy, StateT.run_bind, StateT.run_get, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, hk, VisibleEq]

namespace Game

noncomputable def groupNext (st : OracleState P) (qr : GQuery P) (raw : qr.Result) :
    OracleState P :=
  match trEntry qr raw with
  | none => st
  | some e => { st with tr := st.tr ++ [e], issuedT :=
      match e.issuedGT with | some l => insert l st.issuedT | none => st.issuedT }

theorem group_tracked (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (qr : GQuery P) (st : OracleState P) (p : Reservoir.Phase) :
    Reservoir.run κ (-κ) σ ((group src qr).run st) p =
      (fun z => (z, answerPhase src σ κ st.issuedT qr p)) <$>
        (handOut qr (groupAnswer (withGT src σ) st.issuedT qr)).run
          (groupNext st qr (groupAnswer (withGT src σ) st.issuedT qr)) := by
  classical
  simp only [group, StateT.run_bind, StateT.run_get, pure_bind, Reservoir.run_bind]
  rw [answer_tracked]
  simp only [pure_bind]
  split <;> simp_all [groupNext, StateT.run_bind, StateT.run_modify,
    Reservoir.run_bind, liftGame_tracked]
  all_goals rfl

theorem groupNext_log_bound (st : OracleState P) (qr : GQuery P) (raw : qr.Result)
    (h : ∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length) :
    ∀ e ∈ (groupNext st qr raw).kdfLog, e.1 ≤ (groupNext st qr raw).tr.length := by
  unfold groupNext
  split
  · exact h
  · simp only
    intro e he
    have hh := h e he
    simp only [List.length_append, List.length_singleton]
    omega

theorem groupNext_inv (src : LabelEncoding P) (σ : Fq P ↪ Label P) (κ : Fq P)
    (cx : IdealCtx P) (pv : PubView P) (qr : GQuery P) (st : OracleState P)
    (p : Reservoir.Phase) (h : RunInv cx pv (σ κ) (σ (-κ)) st p) :
    RunInv cx pv (σ κ) (σ (-κ))
      (groupNext st qr (groupAnswer (withGT src σ) st.issuedT qr))
      (answerPhase src σ κ st.issuedT qr p) := by
  classical
  let raw := groupAnswer (withGT src σ) st.issuedT qr
  let p' := answerPhase src σ κ st.issuedT qr p
  have hs : p = .success → p' = .success := fun hp => by
    simp [p', hp, answerPhase_success]
  have hd := answerPhase_dead src σ κ st.issuedT qr p
  refine ⟨groupNext_log_bound st qr raw h.1, ?_, ?_⟩
  · cases he : trEntry qr raw with
    | none =>
      simp only [raw] at he
      simpa [groupNext, he, monitorState] using h.2.1
    | some e =>
      simp only [raw] at he
      have hm : monitorState cx pv (groupNext st qr raw) =
          idealEvent cx (monitorState cx pv st) (.op e) := by
        simp only [groupNext, raw, he, monitorState]
        rw [monEvents_append_op _ _ _ h.1, List.foldl_append]
        rfl
      rw [hm]
      cases hi : e.issuedGT <;>
        simpa [groupNext, he, raw, hi] using
          event_issued_op cx (monitorState cx pv st) e st.issuedT h.2.1
  · cases he : trEntry qr raw with
    | none =>
      simp only [raw] at he
      have hm : monitorState cx pv (groupNext st qr raw) = monitorState cx pv st := by
        simp [groupNext, raw, he]
      rw [hm]
      refine ⟨fun hh => hs (h.2.2.1 hh), ?_⟩
      intro hm hdead
      rcases hd hdead with hp | hl | hr
      · exact h.2.2.2 hm hp
      · exact Or.inl (h.2.1 hm _ (by simpa [issuedAfter, he] using hl))
      · exact Or.inr (h.2.1 hm _ (by simpa [issuedAfter, he] using hr))
    | some e =>
      simp only [raw] at he
      have hm : monitorState cx pv (groupNext st qr raw) =
          idealEvent cx (monitorState cx pv st) (.op e) := by
        simp only [groupNext, raw, he, monitorState]
        rw [monEvents_append_op _ _ _ h.1, List.foldl_append]
        rfl
      rw [hm]
      apply phaseGood_op cx (monitorState cx pv st) e st.issuedT (σ κ) (σ (-κ)) p p'
        h.2.1 h.2.2 hs
      intro hdead
      cases hi : e.issuedGT <;> simpa only [issuedAfter, he, hi] using hd hdead

theorem group_inv (src : LabelEncoding P) (σ : Fq P ↪ Label P) (κ : Fq P)
    (cx : IdealCtx P) (pv : PubView P) (qr : GQuery P) (st : OracleState P)
    (p : Reservoir.Phase) (h : RunInv cx pv (σ κ) (σ (-κ)) st p) :
    ∀ z ∈ support (Reservoir.run κ (-κ) σ ((group src qr).run st) p),
      RunInv cx pv (σ κ) (σ (-κ)) z.1.2 z.2 := by
  rw [group_tracked]
  intro z hz
  obtain ⟨r, hr, rfl⟩ := mem_support_map_peel _ _ hz
  exact (groupNext_inv src σ κ cx pv qr st p h).visible cx pv _ _ _
    (handOut_visible qr _ _ r hr)

end Game

end Praxis.Proofs.Names
