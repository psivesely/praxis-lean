import Praxis.Proofs.NamesRun
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesInvariant
import Praxis.Proofs.NamesMonitor
import Praxis.Proofs.NamesPhase
import Praxis.Proofs.NamesReservoir
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Games

namespace Praxis.Proofs.Names.Game

open OracleComp OracleSpec

variable {P : Params}

noncomputable def kdfPhase (σ : Fq P ↪ Label P) (κ : Fq P) (nm : ClassName P)
    (p : Reservoir.Phase) : Reservoir.Phase :=
  Reservoir.advance κ (-κ)
    (Reservoir.advance κ (-κ) p (.decode nm.out.1) (Algebra.decodeLabel σ nm.out.1))
    (.decode nm.out.2) (Algebra.decodeLabel σ nm.out.2)

theorem kdfPhase_success (σ : Fq P ↪ Label P) (κ : Fq P) (nm : ClassName P) :
    kdfPhase σ κ nm .success = .success := by simp [kdfPhase]

theorem kdfPhase_dead (σ : Fq P ↪ Label P) (κ : Fq P) (nm : ClassName P)
    (p : Reservoir.Phase) : kdfPhase σ κ nm p = .dead ↔ p = .dead := by
  simp [kdfPhase, Reservoir.advance_decode_dead_iff]

theorem kdfPhase_target (σ : Fq P ↪ Label P) (κ : Fq P) (hne : κ ≠ -κ)
    (nm : ClassName P) (hn : nm = labelName σ κ) (p : Reservoir.Phase) (hp : p ≠ .dead) :
    kdfPhase σ κ nm p = .success := by
  have ht := (targetPair_out_iff σ κ nm).mpr hn
  rcases ht with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · simp only [kdfPhase, hx, hy]
    exact Reservoir.decode_pair_success κ (-κ) hne p hp _ _
  · simp only [kdfPhase, hx, hy]
    exact Reservoir.decode_pair_success_rev κ (-κ) hne p hp _ _

def logNext (st : OracleState P) (nm : ClassName P) : OracleState P :=
  { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }

theorem logNext_monitor (cx : IdealCtx P) (pv : PubView P) (st : OracleState P)
    (nm : ClassName P) : monitorState cx pv (logNext st nm) =
      idealEvent cx (monitorState cx pv st) (.kdf nm) := by
  simp only [logNext, monitorState]
  rw [monEvents_append_kdf, List.foldl_append]
  rfl

theorem logNext_inv (σ : Fq P ↪ Label P) (κ : Fq P) (hne : κ ≠ -κ)
    (cx : IdealCtx P) (pv : PubView P) (ht : cx.target = labelName σ κ)
    (hl : (σ κ, (1 : Fq P)) ∈ cx.keyLabels) (hr : (σ (-κ), (-1 : Fq P)) ∈ cx.keyLabels)
    (nm : ClassName P) (st : OracleState P) (p : Reservoir.Phase)
    (h : RunInv cx pv (σ κ) (σ (-κ)) st p) :
    RunInv cx pv (σ κ) (σ (-κ)) (logNext st nm) (kdfPhase σ κ nm p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact h.1 e he
    · obtain rfl := List.mem_singleton.mp he
      exact le_refl _
  · rw [logNext_monitor]
    exact issuedGood_kdf cx _ nm _ h.2.1
  · rw [logNext_monitor]
    apply phaseGood_kdf cx _ nm (σ κ) (σ (-κ)) hl hr p (kdfPhase σ κ nm p) h.2.2
    · intro hp
      simp [hp, kdfPhase_success]
    · exact (kdfPhase_dead σ κ nm p).mp
    · intro hn hp
      exact kdfPhase_target σ κ hne nm (hn.trans ht) p hp

theorem resolvedKdf_tracked (σ : Fq P ↪ Label P) (κ : Fq P) (pad : Msg P)
    (nm : ClassName P) (st : OracleState P) (p : Reservoir.Phase) :
    Reservoir.run κ (-κ) σ ((resolvedKdf κ pad nm).run st) p =
      if targetPair κ (Algebra.decodeLabel σ nm.out.1) (Algebra.decodeLabel σ nm.out.2) then
        pure ((some pad, logNext st nm), kdfPhase σ κ nm p)
      else (fun z => ((some z.1, z.2), kdfPhase σ κ nm p)) <$>
        (kdfLazy nm).run (logNext st nm) := by
  simp only [resolvedKdf, StateT.run_bind, StateT.run_modify, pure_bind,
    Reservoir.run_bind, decodeGT_tracked]
  split <;> simp [logNext, kdfPhase, liftGame_tracked, StateT.run_map, Functor.map_map]

theorem resolvedKdf_inv (σ : Fq P ↪ Label P) (κ : Fq P) (hne : κ ≠ -κ)
    (pad : Msg P) (cx : IdealCtx P) (pv : PubView P) (ht : cx.target = labelName σ κ)
    (hl : (σ κ, (1 : Fq P)) ∈ cx.keyLabels) (hr : (σ (-κ), (-1 : Fq P)) ∈ cx.keyLabels)
    (nm : ClassName P) (st : OracleState P) (p : Reservoir.Phase)
    (h : RunInv cx pv (σ κ) (σ (-κ)) st p) :
    ∀ z ∈ support (Reservoir.run κ (-κ) σ ((resolvedKdf κ pad nm).run st) p),
      RunInv cx pv (σ κ) (σ (-κ)) z.1.2 z.2 := by
  rw [resolvedKdf_tracked]
  have hi := logNext_inv σ κ hne cx pv ht hl hr nm st p h
  split
  · intro z hz
    have he := eq_of_mem_support_pure _ hz
    simpa only [he] using hi
  · intro z hz
    obtain ⟨r, hr, rfl⟩ := mem_support_map_peel _ _ hz
    exact hi.visible cx pv _ _ _ (kdfLazy_visible nm _ r hr)

theorem kdf_inv (σ : Fq P ↪ Label P) (κ : Fq P) (hne : κ ≠ -κ)
    (pad : Msg P) (cx : IdealCtx P) (pv : PubView P) (ht : cx.target = labelName σ κ)
    (hl : (σ κ, (1 : Fq P)) ∈ cx.keyLabels) (hr : (σ (-κ), (-1 : Fq P)) ∈ cx.keyLabels)
    (q : KdfQuery P) (st : OracleState P) (p : Reservoir.Phase)
    (h : RunInv cx pv (σ κ) (σ (-κ)) st p) :
    ∀ z ∈ support (Reservoir.run κ (-κ) σ ((kdf κ pad q).run st) p),
      RunInv cx pv (σ κ) (σ (-κ)) z.1.2 z.2 := by
  simp only [kdf, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simpa using h
  · exact resolvedKdf_inv σ κ hne pad cx pv ht hl hr _ st p h

theorem handler_inv [NeZero P.q] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (hne : κ ≠ -κ) (pad : Msg P) (cx : IdealCtx P) (pv : PubView P)
    (ht : cx.target = labelName σ κ) (hl : (σ κ, (1 : Fq P)) ∈ cx.keyLabels)
    (hr : (σ (-κ), (-1 : Fq P)) ∈ cx.keyLabels)
    (t : (AdvModel P).Domain) (st : OracleState P) (p : Reservoir.Phase)
    (h : RunInv cx pv (σ κ) (σ (-κ)) st p) :
    ∀ z ∈ support (Reservoir.run κ (-κ) σ ((handler src κ pad t).run st) p),
      RunInv cx pv (σ κ) (σ (-κ)) z.1.2 z.2 := by
  rcases t with (((n | qr) | i) | q)
  · simpa [handler, liftGame_tracked, QueryImpl.liftTarget, StateT.run_lift] using h
  · simpa [handler] using group_inv src σ κ cx pv qr st p h
  · simp only [handler, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, liftGame_tracked]
    intro z hz
    obtain ⟨r, hr, rfl⟩ := mem_support_map_peel _ _ hz
    exact h.visible cx pv _ _ _ (hfLazy_visible i st r hr)
  · simpa [handler] using kdf_inv σ κ hne pad cx pv ht hl hr q st p h

theorem simulate_inv [NeZero P.q] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (hne : κ ≠ -κ) (pad : Msg P) (cx : IdealCtx P) (pv : PubView P)
    (ht : cx.target = labelName σ κ) (hl : (σ κ, (1 : Fq P)) ∈ cx.keyLabels)
    (hr : (σ (-κ), (-1 : Fq P)) ∈ cx.keyLabels)
    {α : Type} (oa : OracleComp (AdvModel P) α) (st : OracleState P) (p : Reservoir.Phase)
    (h : RunInv cx pv (σ κ) (σ (-κ)) st p) :
    ∀ z ∈ support (Reservoir.run κ (-κ) σ ((simulateQ (handler src κ pad) oa).run st) p),
      RunInv cx pv (σ κ) (σ (-κ)) z.1.2 z.2 := by
  induction oa using OracleComp.inductionOn generalizing st p with
  | pure a => simpa using h
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, Reservoir.run_bind]
    intro z hz
    obtain ⟨u, hu, hz⟩ := mem_support_bind_peel _ _ hz
    exact ih u.1.1 u.1.2 u.2 (handler_inv src σ κ hne pad cx pv ht hl hr t st p h u hu) z hz

end Praxis.Proofs.Names.Game
