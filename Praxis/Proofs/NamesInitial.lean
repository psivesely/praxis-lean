import Praxis.Proofs.NamesKdfRun
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Cap
import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesInvariant
import Praxis.Proofs.NamesMonitor
import Praxis.Proofs.NamesPhase
import Praxis.Proofs.NamesReservoir
import Praxis.Proofs.NamesRun
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting

namespace Praxis.Proofs.Names.Game

open OracleComp OracleSpec

variable {P : Params}

def initialState (pv : PubView P) (hf : Seed P × FormIndex P → Option (Rq P)) : OracleState P :=
  { OracleState.empty with hf := hf, issuedT := (pv.gT.map Prod.snd).toFinset }

noncomputable def initialPhase (σ : Fq P ↪ Label P) (κ a : Fq P) : Reservoir.Phase :=
  Reservoir.advance κ (-κ) (Reservoir.advance κ (-κ) .fresh (.encode 1) (σ 1))
    (.encode a) (σ a)

noncomputable def fixedOut [Fact (Nat.Prime P.q)] (src : LabelEncoding P)
    (pp : PublicParams P) (forms : FormMatrix P) (c : Coins P) (hdr : Header P) : EncOut P :=
  ⟨pubView src pp (formVec forms) c, hdr, forms, c⟩

theorem initial_tracked [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (pp : PublicParams P) (forms : FormMatrix P) (c : Coins P) (hdr : Header P)
    (hf : Seed P × FormIndex P → Option (Rq P)) (st : OracleState P) :
    Reservoir.run (kappa pp c) (-kappa pp c) σ ((initial src pp forms c hdr hf).run st) .fresh =
      pure ((fixedOut (withGT src σ) pp forms c hdr,
        initialState (pubView (withGT src σ) pp (formVec forms) c) hf),
        initialPhase σ (kappa pp c) (gtExp pp c)) := by
  simp [initial, StateT.run_bind, Reservoir.run_bind, Reservoir.run_map, encodeGT_tracked,
    StateT.run_set, StateT.run_pure, fixedOut, initialState, initialPhase, pubView, withGT]

theorem initial_inv [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (pp : PublicParams P) (forms : FormMatrix P) (c : Coins P) (cx : IdealCtx P)
    (hf : Seed P × FormIndex P → Option (Rq P)) :
    RunInv cx (pubView (withGT src σ) pp (formVec forms) c)
      (σ (kappa pp c)) (σ (-kappa pp c))
      (initialState (pubView (withGT src σ) pp (formVec forms) c) hf)
      (initialPhase σ (kappa pp c) (gtExp pp c)) := by
  classical
  let pv := pubView (withGT src σ) pp (formVec forms) c
  let κ := kappa pp c
  have hm : monitorState cx pv (initialState pv hf) = idealInit cx pv := by
    simp [monitorState, initialState, OracleState.empty, monEvents]
  have hi : IssuedGood (initialState pv hf).issuedT (idealInit cx pv) := by
    intro hnone l hl
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
    exact idealInit_gt_has cx pv hnone e he
  refine ⟨by simp [initialState, OracleState.empty], ?_, ?_⟩
  · rwa [hm]
  · rw [hm]
    refine ⟨fun hg => False.elim (idealInit_not_guessName cx pv hg), ?_⟩
    intro hnone hdead
    have hk : σ κ ∈ (initialState pv hf).issuedT ∨
        σ (-κ) ∈ (initialState pv hf).issuedT := by
      rcases Reservoir.advance_encode_dead_imp _ _ _ _ _ hdead with hd | hl | hr
      · rcases Reservoir.advance_encode_dead_imp _ _ _ _ _ hd with hd | hl | hr
        · cases hd
        · exact Or.inl (by simp [initialState, pv, pubView, withGT, κ, ← hl])
        · exact Or.inr (by simp [initialState, pv, pubView, withGT, κ, ← hr])
      · exact Or.inl (by simp [initialState, pv, pubView, withGT, κ, ← hl])
      · exact Or.inr (by simp [initialState, pv, pubView, withGT, κ, ← hr])
    exact hk.imp (hi hnone _) (hi hnone _)

noncomputable def restoredWorld [Fact (Nat.Prime P.q)] (src : LabelEncoding P)
    (σ : Fq P ↪ Label P) (κ : Fq P) (pad : Msg P)
    (r : (EncOut P × Bool) × OracleState P) : WorldOut P :=
  ⟨withGT src σ, r.1.1, r.1.2, cacheTarget (labelName σ κ) pad r.2⟩

theorem program_guess_implies_success [Fact (Nat.Prime P.q)]
    (src : LabelEncoding P) (σ : Fq P ↪ Label P) (pp : PublicParams P)
    (forms : FormMatrix P) (c : Coins P) (hne : kappa pp c ≠ -kappa pp c)
    (hdr : Header P) (pad : Msg P) (hf : Seed P × FormIndex P → Option (Rq P))
    (A : Adversary P) (Q QH : ℕ) :
    ∀ z ∈ support (Reservoir.run (kappa pp c) (-kappa pp c) σ
      (program src pp forms c hdr pad hf A Q QH) .fresh),
      firstMark pp (restoredWorld src σ (kappa pp c) pad z.1) = some .guessName →
        z.2 = .success := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  let e := fixedOut (withGT src σ) pp forms c hdr
  let cx := idealCtx pp (⟨withGT src σ, e, false, OracleState.empty⟩ : WorldOut P)
  have ht : cx.target = labelName σ (kappa pp c) := rfl
  have hl : (σ (kappa pp c), (1 : Fq P)) ∈ cx.keyLabels := by simp [cx, idealCtx, e, fixedOut, withGT]
  have hr : (σ (-kappa pp c), (-1 : Fq P)) ∈ cx.keyLabels := by simp [cx, idealCtx, e, fixedOut, withGT]
  simp only [program, StateT.run_bind, Reservoir.run_bind, initial_tracked, pure_bind]
  intro z hz hg
  simp only [StateT.run_pure, Reservoir.run_pure] at hz
  obtain ⟨u, hu, hz⟩ := mem_support_bind_peel _ _ hz
  obtain rfl := eq_of_mem_support_pure _ hz
  have hi := simulate_inv src σ (kappa pp c) hne pad cx e.pv ht hl hr
    ((cap Q QH A).run e.pv e.header) _ _ (initial_inv src σ pp forms c cx hf) u hu
  apply hi.2.2.1
  exact hg

end Praxis.Proofs.Names.Game
