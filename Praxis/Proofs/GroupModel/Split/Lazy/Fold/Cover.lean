import Praxis.Proofs.GroupModel.Split.Lazy.Fold.History
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Initial
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Operations
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Sync
import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Reduction
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option linter.constructorNameAsVariable false

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0) (z : WorldOut P0)

def cmpStep (s : Step pp) : Option (Collision pp) :=
  match s.entry.1 with
  | .inl (.inl (.inr _)) => s.shadow.first
  | .inr _ => keyCmp pp z s.shadow
  | _ => none

def Stopped (st : ObsState pp) : Prop :=
  ∃ b s, st.stop = some b ∧ st.steps[b]? = some s ∧
    ((cmpStep pp z s).isSome ∨
      (monitor (idealCtx pp z) z.out.pv st.oracle).mark = some .guessName)

def Running (st : ObsState pp) : Prop :=
  st.stop = none ∧ st.shadow.first = none ∧
    (monitor (idealCtx pp z) z.out.pv st.oracle).mark = none ∧
    Projects pp (formVec z.out.forms) (monitor (idealCtx pp z) z.out.pv st.oracle) st.shadow ∧
    Named pp z.enc (monitor (idealCtx pp z) z.out.pv st.oracle).named st.shadow ∧
    ∀ l ∈ st.oracle.issuedT, ∃ P, st.shadow.dict .gₜ l = some P

def Inv (st : ObsState pp) : Prop :=
  LogBound st.oracle ∧
    ((monitor (idealCtx pp z) z.out.pv st.oracle).mark = some .init ∨
      (initialise pp z.out.forms z.out.pv).first = none ∧
        (Running pp z st ∨ Stopped pp z st))

lemma stopped_extend (st st' : ObsState pp) (h : Stopped pp z st)
    (hstop : ∀ b, st.stop = some b → st'.stop = some b)
    (hsteps : st.steps <+: st'.steps)
    (hmark : (monitor (idealCtx pp z) z.out.pv st.oracle).mark = some .guessName →
      (monitor (idealCtx pp z) z.out.pv st'.oracle).mark = some .guessName) :
    Stopped pp z st' := by
  obtain ⟨b, s, hb, hs, hc⟩ := h
  refine ⟨b, s, hstop b hb, ?_, hc.imp_right hmark⟩
  obtain ⟨more, hm⟩ := hsteps
  rw [← hm, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hs).1, hs]

lemma step_inv (q : (AdvModel P0).Domain) (st : ObsState pp) (h : Inv pp z st) :
    ∀ y ∈ support ((obsHandler pp z.enc z.out.coins q).run st), Inv pp z y.2 := by
  classical
  intro y hy
  obtain ⟨hlog, hi⟩ := h
  have hgrow := Simulation.obs_step_support pp z.enc z.out.coins q st y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  have hevents := game_events z.enc q st.oracle hlog r hr
  have hm := monitor_step (idealCtx pp z) z.out.pv z.enc q st.oracle hlog r hr
  refine ⟨hevents.2, ?_⟩
  have h_absorb (k : Mark P0)
      (hk : (monitor (idealCtx pp z) z.out.pv st.oracle).mark = some k) :
      (monitor (idealCtx pp z) z.out.pv r.2).mark = some k := by
    rw [hm, Exposure.fold_absorbs _ _ k hk]
    exact hk
  rcases hi with hi | ⟨hinit, hi⟩
  · exact Or.inl (h_absorb .init hi)
  right
  refine ⟨hinit, ?_⟩
  rcases hi with hrun | hstop
  swap
  · right
    exact stopped_extend pp z st _ hstop hgrow.2
      (by obtain ⟨s, _, hs⟩ := hgrow.1; rw [hs]; exact List.prefix_append _ _)
      (h_absorb .guessName)
  obtain ⟨hstop, hfirst, hmark, hproj, hnamed, hcover⟩ := hrun
  have h1 : ∀ E F, Exposure.value1 pp E = Exposure.value1 pp F →
      (idealCtx pp z).eq1 E F := fun E F hh => (Exposure.value1_eq_iff pp E F).mp hh
  have h2 : ∀ E F, Exposure.value2 pp (formVec z.out.forms) E =
      Exposure.value2 pp (formVec z.out.forms) F → (idealCtx pp z).eq2 E F :=
    fun E F hh => (Exposure.value2_eq_iff pp (formVec z.out.forms) E F).mp hh
  have hT : ∀ E F, Exposure.valueT pp (formVec z.out.forms) E =
      Exposure.valueT pp (formVec z.out.forms) F → (idealCtx pp z).eqT E F :=
    fun E F hh => (Exposure.valueT_eq_iff pp (formVec z.out.forms) E F).mp hh
  rcases q with ((n | gq) | i) | kq
  · have horacle : r.2 = st.oracle := by
      rw [Simulation.gameImpl_unif, support_map] at hr
      obtain ⟨a, _, ha⟩ := hr
      exact (congrArg Prod.snd ha).symm
    left
    simpa only [Running, hstop, hfirst, horacle, Option.isSome_none,
      Bool.false_eq_true, false_or, or_self, if_false, Option.orElse_none] using
      And.intro hstop (And.intro hfirst (And.intro hmark (And.intro hproj (And.intro hnamed hcover))))
  · let sh := observeGroup pp z.enc st.shadow gq (groupAnswer z.enc st.oracle.issuedT gq)
    cases hf : sh.first with
    | some e =>
      right
      refine ⟨st.steps.length,
        (⟨⟨.inl (.inl (.inr gq)), r.1⟩, sh,
          st.order ++ newGuesses pp st.shadow sh gq⟩ : Step pp), ?_, ?_, Or.inl ?_⟩
      · simp only [hstop, Option.orElse_none, sh, hf, Option.isSome_some, true_or, if_true]
      · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
        rfl
      · simpa only [cmpStep] using (show sh.first.isSome from by rw [hf]; rfl)
    | none =>
      have hc : (observeGroup pp z.enc st.shadow gq (groupAnswer z.enc st.oracle.issuedT gq)).first = none := hf
      have hh := group_clear pp (formVec z.out.forms) (idealCtx pp z) h1 h2 hT
        z.enc _ st.shadow hproj hnamed st.oracle.issuedT hcover gq hc
      have hn := group_named pp (idealCtx pp z) z.enc _ st.shadow hnamed
        st.oracle.issuedT hcover gq hc
      have hmon : monitor (idealCtx pp z) z.out.pv r.2 =
          groupIdeal (idealCtx pp z) (monitor (idealCtx pp z) z.out.pv st.oracle)
            gq (groupAnswer z.enc st.oracle.issuedT gq) := by
        rw [hm]
        simp only [queryEvents, groupIdeal]
        cases he : trEntry gq (groupAnswer z.enc st.oracle.issuedT gq) <;>
          simp [he, idealEvent, hmark]
      have hcov : ∀ l ∈ r.2.issuedT, ∃ P, sh.dict .gₜ l = some P := by
        have hraw : r ∈ support ((finishGroup gq (groupAnswer z.enc st.oracle.issuedT gq)).run st.oracle) := by
          simpa only [Simulation.gameImpl_group, Simulation.groupImpl_factor'] using hr
        intro l hl
        rcases Simulation.finishGroup_issued gq _ st.oracle r hraw l hl with hl | ⟨op, hop, hol⟩
        · obtain ⟨P, hp⟩ := hcover l hl
          exact ⟨P, Simulation.observeGroup_mono pp z.enc st.shadow gq _ .gₜ l P hp⟩
        · exact Option.isSome_iff_exists.mp (Simulation.observeGroup_result pp z.enc st.shadow
            st.oracle.issuedT gq l op hop hol)
      left
      refine ⟨?_, hc, ?_, ?_, ?_, hcov⟩
      · simp only [hstop, Option.orElse_none, sh, hf, Option.isSome_none, Bool.false_eq_true,
          or_self, if_false]
      · rw [hmon, hh.2, hmark]
      · rw [hmon]; exact hh.1
      · rw [hmon]; exact hn
  · have hmon : monitor (idealCtx pp z) z.out.pv r.2 =
        monitor (idealCtx pp z) z.out.pv st.oracle := by simpa [queryEvents] using hm
    have hiss := Simulation.hfLazy_issuedT i st.oracle r (by simpa only [Simulation.gameImpl_hf] using hr)
    left
    simpa only [Running, hstop, hfirst, hmon, hiss, Option.isSome_none,
      Bool.false_eq_true, false_or, or_self, if_false, Option.orElse_none] using
      And.intro hstop (And.intro hfirst (And.intro hmark (And.intro hproj (And.intro hnamed hcover))))
  · by_cases ht : KdfTarget pp z.enc z.out.coins st.oracle kq
    · right
      have hname : Simulation.kdfName st.oracle kq = some (targetName pp z) := by
        cases kq <;> exact ht
      refine ⟨st.steps.length,
        (⟨⟨.inr kq, r.1⟩, st.shadow, st.order⟩ : Step pp), ?_, ?_, ?_⟩
      · simp only [hstop, Option.orElse_none, hfirst, Option.isSome_none,
          Bool.false_eq_true, false_or, ht, if_true]
      · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
      · cases he : keyCmp pp z st.shadow with
        | some e => left; simpa only [cmpStep, he] using (show (some e : Option (Collision pp)).isSome from rfl)
        | none =>
          right
          rw [hm]
          simpa only [queryEvents, hname, Option.toList_some, List.map_cons, List.map_nil,
            List.foldl_cons, List.foldl_nil, idealEvent, hmark] using
            key_none pp z _ st.shadow hproj.gt he
    · have hmon : monitor (idealCtx pp z) z.out.pv r.2 =
          monitor (idealCtx pp z) z.out.pv st.oracle := by
        rw [hm]
        cases hn : Simulation.kdfName st.oracle kq with
        | none => simp [queryEvents, hn]
        | some nm =>
          have hne : nm ≠ targetName pp z := by
            intro he
            apply ht
            cases kq <;> simpa only [KdfTarget, Simulation.kdfName, he, targetName] using hn
          have hneq : nm ≠ (idealCtx pp z).target := hne
          simp only [queryEvents, hn, Option.toList_some, List.map_cons, List.map_nil,
            List.foldl_cons, List.foldl_nil, idealEvent, hmark]
          simp only [idealKdf, if_neg hneq]
      have hiss := Simulation.kdfImpl_issuedT kq st.oracle r (by simpa only [Simulation.gameImpl_kdf] using hr)
      left
      simpa only [Running, hstop, hfirst, hmon, hiss, Option.isSome_none,
        Bool.false_eq_true, false_or, ht, if_false, Option.orElse_none] using
        And.intro hstop (And.intro hfirst (And.intro hmark (And.intro hproj (And.intro hnamed hcover))))

lemma initial_inv [Nonempty (CoinDomain pp)] (m : Msg P0) (st0 : OracleState P0)
    (he : (z.out, st0) ∈ support ((encGame z.enc pp m).run OracleState.empty)) :
    Inv pp z ⟨st0, initialise pp z.out.forms z.out.pv, [], [], none⟩ := by
  obtain ⟨htr, hkl, hiss⟩ := encGame_initial pp z.enc m (z.out, st0) he
  change st0.tr = [] at htr
  change st0.kdfLog = [] at hkl
  change st0.issuedT = (z.out.pv.gT.map Prod.snd).toFinset at hiss
  have hmon : monitor (idealCtx pp z) z.out.pv st0 = idealInit (idealCtx pp z) z.out.pv := by
    simp [monitor, htr, hkl, monEvents]
  refine ⟨by intro e he; simp [hkl] at he, ?_⟩
  rcases initial_rel pp z with ⟨hm, hf, hd⟩ | ⟨hm, hf⟩
  · right
    refine ⟨hf, Or.inl ⟨rfl, hf, ?_, ?_, ?_, ?_⟩⟩
    · rw [hmon]; exact hm
    · rw [hmon]; exact const_projects pp (formVec z.out.forms) _ _ hd
    · rw [hmon]
      intro u hu
      rw [initial_named] at hu
      cases hu
    · rw [hiss]
      exact initial_cover pp z.out.forms z.out.pv
  · left
    rw [hmon]
    exact hm

lemma inv_supported [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0) :
    ∀ ω ∈ support (observedRun pp m A), Inv pp ω.1 ω.2 := by
  intro ω hω
  unfold observedRun at hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨σ, hσ, hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨e, he, hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨r, hr, hω⟩ := hω
  rw [support_pure, Set.mem_singleton_iff] at hω
  rw [hω]
  exact simulateQ_run_preserves_inv_of_query (obsHandler pp σ e.1.coins)
    (Inv pp (⟨σ, e.1, r.1, r.2.oracle⟩ : WorldOut P0))
    (step_inv pp (⟨σ, e.1, r.1, r.2.oracle⟩ : WorldOut P0))
    (A.run e.1.pv e.1.header) _
    (initial_inv pp (⟨σ, e.1, r.1, r.2.oracle⟩ : WorldOut P0) m e.2 he) r hr

lemma charged_not_none (hc : ChargedCmp pp z) : firstMark pp z ≠ none := by
  obtain ⟨k, hk, _⟩ := hc
  rw [hk]
  simp

lemma charged_not_init (hc : ChargedCmp pp z) : firstMark pp z ≠ some .init := by
  obtain ⟨k, hk, hc⟩ := hc
  intro hm
  have he : k = .init := Option.some.inj (hk.symm.trans hm)
  subst k
  simp [Mark.data] at hc

lemma charged_not_guessName (hc : ChargedCmp pp z) : firstMark pp z ≠ some .guessName := by
  obtain ⟨k, hk, hc⟩ := hc
  intro hm
  have he : k = .guessName := Option.some.inj (hk.symm.trans hm)
  subst k
  simp [Mark.data] at hc

lemma oracle_supported [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0) :
    ∀ ω ∈ support (observedRun pp m A), ω.2.oracle = ω.1.st := by
  intro ω hω
  unfold observedRun at hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨σ, _, hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨e, _, hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨r, _, hω⟩ := hω
  rw [support_pure, Set.mem_singleton_iff] at hω
  rw [hω]

lemma cover_bad [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0) :
    ∀ ω ∈ support (observedRun pp m A), ChargedCmp pp ω.1 → ∃ e, BadAt ω e := by
  intro ω hω hc
  have hinv := inv_supported pp m A
  have hor := oracle_supported pp m A
  generalize observedRun pp m A = obs at hinv hor hω
  obtain ⟨_, hi⟩ := hinv ω hω
  have hmon : monitor (idealCtx pp ω.1) ω.1.out.pv ω.2.oracle =
      (monEvents ω.1.st.tr ω.1.st.kdfLog).foldl (idealEvent (idealCtx pp ω.1))
        (idealInit (idealCtx pp ω.1) ω.1.out.pv) := by
    rw [hor ω hω]
    rfl

  rcases hi with hi | ⟨hinit, hi⟩
  · exact False.elim (charged_not_init pp ω.1 hc (by simpa only [firstMark, idealMonitor, hmon] using hi))
  rcases hi with hi | hi
  · exact False.elim (charged_not_none pp ω.1 hc (by simpa only [firstMark, idealMonitor, hmon] using hi.2.2.1))
  obtain ⟨b, s, hb, hs, he | hm⟩ := hi
  · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp he
    refine ⟨e, b, hb, ⟨hinit, ?_⟩, ?_⟩
    · intro b' hb'
      have hh : b = b' := Option.some.inj (hb.symm.trans hb')
      omega
    · simp only [badCmp, hb, hs]
      unfold cmpStep at he
      generalize s.entry.1 = q at he ⊢
      rcases q with ((n | gq) | i) | kq <;> exact he
  · exact False.elim (charged_not_guessName pp ω.1 hc (by simpa only [firstMark, idealMonitor, hmon] using hm))

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync
