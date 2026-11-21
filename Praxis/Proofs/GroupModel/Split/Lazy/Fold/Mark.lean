import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Cover
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Boundary
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.History
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Initial
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Operations
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Sync
import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Disintegration
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

def MarkInfo (oracle : OracleState P0) (s : Step pp) : Prop :=
  ∀ e, cmpStep pp z s = some e → GuessFree e → e.sort = .gₜ →
    ∃ (D : ExprT P0) (ι : k) (mark : Mark P0),
      e.value = Exposure.valueT pp (formVec z.out.forms) D - ι • Exposure.valueKey pp ∧
      (monitor (idealCtx pp z) z.out.pv oracle).mark = some mark ∧ mark.data = some (D, ι)

def Extra (st : ObsState pp) : Prop :=
  (monitor (idealCtx pp z) z.out.pv st.oracle).mark = some .init ∨
    (st.stop = none ∧ Orphans pp (monitor (idealCtx pp z) z.out.pv st.oracle) st.shadow ∧
      ∀ l ∈ st.oracle.issuedT, ((monitor (idealCtx pp z) z.out.pv st.oracle).dT l).isSome) ∨
    ∃ b s, st.stop = some b ∧ st.steps[b]? = some s ∧ MarkInfo pp z st.oracle s

lemma step_extra [Nonempty (CoinDomain pp)]
    (noKey : ∀ E, ¬ FormalKey pp (formVec z.out.forms) E)
    (q : (AdvModel P0).Domain) (st : ObsState pp) (h : Inv pp z st) (hx : Extra pp z st) :
    ∀ y ∈ support ((obsHandler pp z.enc z.out.coins q).run st), Extra pp z y.2 := by
  classical
  intro y hy
  have hgrow := Simulation.obs_step_support pp z.enc z.out.coins q st y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  have hm := monitor_step (idealCtx pp z) z.out.pv z.enc q st.oracle h.1 r hr
  have h_absorb (k : Mark P0)
      (hk : (monitor (idealCtx pp z) z.out.pv st.oracle).mark = some k) :
      (monitor (idealCtx pp z) z.out.pv r.2).mark = some k := by
    rw [hm, Exposure.fold_absorbs _ _ k hk]
    exact hk
  rcases hx with hinitmark | hrun | ⟨b, s, hb, hs, hinfo⟩
  · exact Or.inl (h_absorb .init hinitmark)
  swap
  · right; right
    refine ⟨b, s, hgrow.2 b hb, ?_, ?_⟩
    · obtain ⟨s', _, hsteps⟩ := hgrow.1
      rw [hsteps, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hs).1, hs]
    · intro e he hg hsort
      obtain ⟨D, ι, mark, hval, hmark, hdata⟩ := hinfo e he hg hsort
      exact ⟨D, ι, mark, hval, h_absorb mark hmark, hdata⟩
  obtain ⟨hstop0, horph, hideal⟩ := hrun
  rcases h.2 with hinitmark | ⟨hinit, hrun | hstopped⟩
  · exact Or.inl (h_absorb .init hinitmark)
  swap
  · obtain ⟨b, s, hb, _⟩ := hstopped
    simp [hstop0] at hb
  obtain ⟨hstop, hfirst, hmark, hproj, hnamed, hcover⟩ := hrun
  rcases q with ((n | gq) | i) | kq
  · have horacle : r.2 = st.oracle := by
      rw [Simulation.gameImpl_unif, support_map] at hr
      obtain ⟨a, _, ha⟩ := hr
      exact (congrArg Prod.snd ha).symm
    right; left
    simpa only [hstop, hfirst, horacle, Option.isSome_none, Bool.false_eq_true,
      false_or, or_self, if_false, Option.orElse_none] using And.intro hstop (And.intro horph hideal)
  · let sh := observeGroup pp z.enc st.shadow gq (groupAnswer z.enc st.oracle.issuedT gq)
    have hmon : monitor (idealCtx pp z) z.out.pv r.2 =
        groupIdeal (idealCtx pp z) (monitor (idealCtx pp z) z.out.pv st.oracle)
          gq (groupAnswer z.enc st.oracle.issuedT gq) := by
      rw [hm]
      simp only [queryEvents, groupIdeal]
      cases he : trEntry gq (groupAnswer z.enc st.oracle.issuedT gq) <;>
        simp [he, idealEvent, hmark]
    cases hf : sh.first with
    | some e =>
      right; right
      refine ⟨st.steps.length,
        (⟨⟨.inl (.inl (.inr gq)), r.1⟩, sh,
          st.order ++ newGuesses pp st.shadow sh gq⟩ : Step pp), ?_, ?_, ?_⟩
      · simp only [hstop, Option.orElse_none, sh, hf, Option.isSome_some, true_or, if_true]
      · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
        rfl
      · intro e' he hg hsort
        change sh.first = some e' at he
        have heq : e = e' := Option.some.inj (hf.symm.trans he)
        subst e'
        obtain ⟨D, hD, hval⟩ := group_boundary pp (formVec z.out.forms) (idealCtx pp z)
          (fun _ _ => Iff.rfl) z.enc _ st.shadow hfirst hproj horph hnamed
          st.oracle.issuedT hideal hcover gq e hf hg hsort
        refine ⟨D, 0, .diff D, ?_, ?_, rfl⟩
        · simpa only [zero_smul, sub_zero] using hval
        · rw [hmon]; exact hD
    | none =>
      have ho := group_orphans pp (idealCtx pp z) z.enc _ st.shadow horph hnamed
        st.oracle.issuedT hideal hcover gq
      have hraw : r ∈ support ((finishGroup gq (groupAnswer z.enc st.oracle.issuedT gq)).run st.oracle) := by
        simpa only [Simulation.gameImpl_group, Simulation.groupImpl_factor'] using hr
      have hi := group_issued (idealCtx pp z) _ st.oracle hideal gq _ r hraw
      right; left
      refine ⟨?_, ?_, ?_⟩
      · simp only [hstop, Option.orElse_none, sh, hf, Option.isSome_none, Bool.false_eq_true,
          or_self, if_false]
      · rw [hmon]; exact ho
      · rw [hmon]; exact hi
  · have hmon : monitor (idealCtx pp z) z.out.pv r.2 =
        monitor (idealCtx pp z) z.out.pv st.oracle := by simpa [queryEvents] using hm
    have hiss := Simulation.hfLazy_issuedT i st.oracle r (by simpa only [Simulation.gameImpl_hf] using hr)
    right; left
    simpa only [hstop, hfirst, hmon, hiss, Option.isSome_none, Bool.false_eq_true,
      false_or, or_self, if_false, Option.orElse_none] using And.intro hstop (And.intro horph hideal)
  · by_cases ht : KdfTarget pp z.enc z.out.coins st.oracle kq
    · have hname : Simulation.kdfName st.oracle kq = some (targetName pp z) := by
        cases kq <;> exact ht
      right; right
      refine ⟨st.steps.length, (⟨⟨.inr kq, r.1⟩, st.shadow, st.order⟩ : Step pp), ?_, ?_, ?_⟩
      · simp only [hstop, Option.orElse_none, hfirst, Option.isSome_none,
          Bool.false_eq_true, false_or, ht, if_true]
      · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
      · intro e he hg hsort
        change keyCmp pp z st.shadow = some e at he
        obtain ⟨D, hD, hval⟩ := key_boundary pp z noKey _ st.shadow hproj.gt horph e he hg
        refine ⟨D, 1, .key D, ?_, ?_, rfl⟩
        · simpa only [one_smul] using hval
        · rw [hm]
          simpa only [queryEvents, hname, Option.toList_some, List.map_cons, List.map_nil,
            List.foldl_cons, List.foldl_nil, idealEvent, hmark] using hD
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
      right; left
      simpa only [hstop, hfirst, hmon, hiss, Option.isSome_none, Bool.false_eq_true,
        false_or, ht, if_false, Option.orElse_none] using And.intro hstop (And.intro horph hideal)

lemma initial_extra [Nonempty (CoinDomain pp)] (m : Msg P0) (st0 : OracleState P0)
    (he : (z.out, st0) ∈ support ((encGame z.enc pp m).run OracleState.empty)) :
    Extra pp z ⟨st0, initialise pp z.out.forms z.out.pv, [], [], none⟩ := by
  obtain ⟨htr, hkl, hiss⟩ := encGame_initial pp z.enc m (z.out, st0) he
  change st0.tr = [] at htr
  change st0.kdfLog = [] at hkl
  change st0.issuedT = (z.out.pv.gT.map Prod.snd).toFinset at hiss
  have hmon : monitor (idealCtx pp z) z.out.pv st0 = idealInit (idealCtx pp z) z.out.pv := by
    simp [monitor, htr, hkl, monEvents]
  rcases initial_rel pp z with ⟨hm, hf, hd⟩ | ⟨hm, hf⟩
  · right; left
    refine ⟨rfl, ?_, ?_⟩
    · rw [hmon]
      exact const_orphans pp (formVec z.out.forms) _ _ hd
    · intro l hl
      rw [hmon]
      obtain ⟨P, hP⟩ := initial_cover pp z.out.forms z.out.pv l (hiss ▸ hl)
      exact const_domain pp (formVec z.out.forms) _ _ hd l P hP
  · left
    rw [hmon]
    exact hm

lemma extra_supported [Nonempty (CoinDomain pp)]
    (noKey : ∀ forms E, ¬ FormalKey pp (formVec forms) E) (m : Msg P0) (A : Adversary P0) :
    ∀ ω ∈ support (observedRun pp m A), Extra pp ω.1 ω.2 := by
  intro ω hω
  unfold observedRun at hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨σ, _, hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨e, he, hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨r, hr, hω⟩ := hω
  rw [support_pure, Set.mem_singleton_iff] at hω
  rw [hω]
  let z : WorldOut P0 := ⟨σ, e.1, r.1, r.2.oracle⟩
  have hh := simulateQ_run_preserves_inv_of_query (obsHandler pp σ e.1.coins)
    (fun st => Inv pp z st ∧ Extra pp z st)
    (by
      intro q st h y hy
      exact ⟨step_inv pp z q st h.1 y hy,
        step_extra pp z (noKey e.1.forms) q st h.1 h.2 y hy⟩)
    (A.run e.1.pv e.1.header) _
    ⟨initial_inv pp z m e.2 he, initial_extra pp z m e.2 he⟩ r hr
  exact hh.2

lemma cover_mark [Nonempty (CoinDomain pp)]
    (noKey : ∀ forms E, ¬ FormalKey pp (formVec forms) E) (m : Msg P0) (A : Adversary P0) :
    ∀ ω ∈ support (observedRun pp m A), ChargedCmp pp ω.1 → ∀ e, BadAt ω e →
      GuessFree e → e.sort = .gₜ → ∃ (D : ExprT P0) (ι : k),
        e.value = Exposure.valueT pp (formVec ω.1.out.forms) D - ι • Exposure.valueKey pp ∧
          ¬ GoodCmp pp ω.1 D ι := by
  intro ω hω hc e he hg hsort
  have hx := extra_supported pp noKey m A
  have hor := oracle_supported pp m A
  generalize observedRun pp m A = obs at hx hor hω
  have hmon : (monitor (idealCtx pp ω.1) ω.1.out.pv ω.2.oracle).mark = firstMark pp ω.1 := by
    rw [hor ω hω]
    rfl
  rcases hx ω hω with hinit | ⟨hstop, _⟩ | ⟨b, s, hb, hs, hinfo⟩
  · exact False.elim (charged_not_init pp ω.1 hc (hmon.symm.trans hinit))
  · obtain ⟨b, hb, _⟩ := he
    simp [hstop] at hb
  · obtain ⟨b', hb', _, hcmp⟩ := he
    have hbb : b' = b := Option.some.inj (hb'.symm.trans hb)
    subst b'
    have hcmp' : cmpStep pp ω.1 s = some e := by
      simp only [badCmp, hb, hs] at hcmp
      unfold cmpStep
      generalize s.entry.1 = q at hcmp ⊢
      rcases q with ((n | gq) | i) | kq <;> exact hcmp
    obtain ⟨D, ι, mark, hval, hm, hdata⟩ := hinfo e hcmp' hg hsort
    refine ⟨D, ι, hval, ?_⟩
    intro hgood
    exact Exposure.charged_not_goodMark pp ω.1 D ι hc
      ⟨mark, hmon.symm.trans hm, hdata, hgood⟩

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync
