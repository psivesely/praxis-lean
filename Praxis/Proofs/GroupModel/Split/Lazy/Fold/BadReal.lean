import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Proofs.GroupModel.Init.World
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.BadReal

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0)

private lemma fold_dict_mono (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp))
    (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (h : st.dict s l = some P) :
    (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).dict s l = some P := by
  induction es generalizing st with
  | nil => exact h
  | cons e es ih =>
    exact ih _ ((Simulation.insertResult_props pp st e.1 e.2.1 e.2.2).2.2.1 s l P h)

private lemma fold_dict_covers (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp))
    (st : State pp) (e : GroupModel.Sorted.PSort × Label P0 × Poly pp) (he : e ∈ es) :
    ((es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).dict e.1 e.2.1).isSome := by
  induction es generalizing st with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with heq | he
    · subst e
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp
        (Simulation.insertResult_isSome pp st a.1 a.2.1 a.2.2)
      rw [List.foldl_cons, fold_dict_mono pp es _ _ _ P hP]
      rfl
    · exact ih _ he

private lemma initialise_covers (forms : FormMatrix P0) (pv : PubView P0)
    (l : Label P0) (hl : l ∈ (pv.gT.map Prod.snd).toFinset) :
    ((initialise pp forms pv).dict .gₜ l).isSome := by
  simp only [List.mem_toFinset, List.mem_map] at hl
  obtain ⟨e, he, rfl⟩ := hl
  apply fold_dict_covers pp (initialEntries pp forms pv) (empty pp)
    (.gₜ, e.2, baseT pp forms (gtInit e.1))
  simp only [initialEntries, List.mem_append, List.mem_map]
  exact Or.inr ⟨e, he, rfl⟩

def ObsSound (σ : LabelEncoding P0) (c : CoinDomain pp) (st : ObsState pp) : Prop :=
  Sound pp σ c st.shadow ∧
    (∀ l ∈ st.oracle.issuedT, (st.shadow.dict .gₜ l).isSome) ∧
    ∀ step ∈ st.steps, Sound pp σ c step.shadow

private lemma append_sound (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : ObsState pp) (hs : ObsSound pp σ c st) (oracle : OracleState P0)
    (shadow : State pp) (order : List GuessVar) (entry : Entry) (stop : Option ℕ)
    (hsh : Sound pp σ c shadow)
    (hcov : ∀ l ∈ oracle.issuedT, (shadow.dict .gₜ l).isSome) :
    ObsSound pp σ c ⟨oracle, shadow, order, st.steps ++ [⟨entry, shadow, order⟩], stop⟩ := by
  refine ⟨hsh, hcov, ?_⟩
  intro step hstep
  rcases List.mem_append.mp hstep with h | h
  · exact hs.2.2 step h
  · simp only [List.mem_singleton] at h
    subst step
    exact hsh

lemma obsHandler_sound (σ : LabelEncoding P0) (c : CoinDomain pp)
    (q : (AdvModel P0).Domain) (st : ObsState pp) (hs : ObsSound pp σ c st) :
    ∀ y ∈ support ((obsHandler pp σ c.val q).run st), ObsSound pp σ c y.2 := by
  intro y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rcases q with ((n | gq) | i) | kq
  · rw [Simulation.gameImpl_unif, support_map] at hz
    obtain ⟨u, _, rfl⟩ := hz
    exact append_sound pp σ c st hs _ _ _ _ _ hs.1 hs.2.1
  · have hsh := observeGroup_sound pp σ c st.shadow st.oracle.issuedT gq hs.1
      (fun l hl => Option.isSome_iff_exists.mp (hs.2.1 l hl))
    apply append_sound pp σ c st hs _ _ _ _ _ hsh
    intro l hl
    rw [Simulation.gameImpl_group, Simulation.groupImpl_factor'] at hz
    rcases Simulation.finishGroup_issued gq _ st.oracle z hz l hl with hold | ⟨e, he, hel⟩
    · obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (hs.2.1 l hold)
      rw [Simulation.observeGroup_mono pp σ st.shadow gq _ .gₜ l P hP]
      rfl
    · exact Simulation.observeGroup_result pp σ st.shadow st.oracle.issuedT gq l e he hel
  · apply append_sound pp σ c st hs _ _ _ _ _ hs.1
    intro l hl
    rw [Simulation.gameImpl_hf] at hz
    exact hs.2.1 l ((Simulation.hfLazy_issuedT i st.oracle z hz) ▸ hl)
  · apply append_sound pp σ c st hs _ _ _ _ _ hs.1
    intro l hl
    rw [Simulation.gameImpl_kdf] at hz
    exact hs.2.1 l ((Simulation.kdfImpl_issuedT kq st.oracle z hz) ▸ hl)

lemma obsRun_sound (σ : LabelEncoding P0) (c : CoinDomain pp) {α : Type}
    (oa : OracleComp (AdvModel P0) α) (st : ObsState pp) (hs : ObsSound pp σ c st) :
    ∀ y ∈ support ((simulateQ (obsHandler pp σ c.val) oa).run st),
      ObsSound pp σ c y.2 :=
  simulateQ_run_preserves_inv_of_query (obsHandler pp σ c.val) (ObsSound pp σ c)
    (fun q st hs y hy => obsHandler_sound pp σ c q st hs y hy) oa st hs

private lemma mapM_issued {α β : Type} (f : α → GameM P0 β)
    (hf : ∀ a st z, z ∈ support ((f a).run st) → z.2.issuedT = st.issuedT)
    (l : List α) (st : OracleState P0) :
    ∀ z ∈ support ((l.mapM f).run st), z.2.issuedT = st.issuedT := by
  induction l generalizing st with
  | nil => simp
  | cons a l ih =>
    intro z hz
    simp only [List.mapM_cons, StateT.run_bind] at hz
    obtain ⟨y, hy, hz⟩ := mem_support_bind_peel _ _ hz
    obtain ⟨v, hv, hz⟩ := mem_support_bind_peel _ _ hz
    have he := eq_of_mem_support_pure _ hz
    subst z
    exact (ih y.2 v hv).trans (hf a st y hy)

private lemma kdfLazy_issued (nm : ClassName P0) (st : OracleState P0) :
    ∀ z ∈ support ((kdfLazy nm).run st), z.2.issuedT = st.issuedT := by
  intro z hz
  cases hh : st.kdf nm with
  | none =>
    simp only [kdfLazy, hh, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff, bind_pure_comp, support_map, Set.mem_image] at hz
    obtain ⟨a, ⟨u, _, rfl⟩, rfl⟩ := hz
    rfl
  | some a =>
    simp only [kdfLazy, hh, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    rw [hz]

private lemma encGame_issued [Nonempty (CoinDomain pp)]
    (σ : LabelEncoding P0) (m : Msg P0) (z : EncOut P0 × OracleState P0)
    (hz : z ∈ support ((encGame σ pp m).run OracleState.empty)) :
    z.2.issuedT = (z.1.pv.gT.map Prod.snd).toFinset := by
  have : NeZero P0.q := ⟨(Fact.out : Nat.Prime P0.q).ne_zero⟩
  unfold encGame at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨seed, hseed, hz⟩ := mem_support_bind_peel _ _ hz
  unfold encAt at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨es, hes, hz⟩ := mem_support_bind_peel _ _ hz
  have hreads : es.2.issuedT = seed.2.issuedT := by
    apply mapM_issued _ _ _ _ es hes
    intro i s y hy
    simp only [StateT.run_bind] at hy
    obtain ⟨a, ha, hy⟩ := mem_support_bind_peel _ _ hy
    have he := eq_of_mem_support_pure _ hy
    have hey := congrArg (fun t => t.2.issuedT) he
    exact hey.trans (Simulation.hfLazy_issuedT _ _ a ha)
  rw [mem_support_bind_iff] at hz
  obtain ⟨c, hc, hz⟩ := hz
  obtain ⟨pad, hpad, hz⟩ := mem_support_bind_peel _ _ hz
  have hpadissued := kdfLazy_issued _ _ pad hpad
  simp at hz
  rw [hz]
  have hseedstate : seed.2 = OracleState.empty := by
    obtain ⟨a, ha, he⟩ := mem_support_bind_peel _ _ hseed
    exact congrArg Prod.snd (eq_of_mem_support_pure _ he)
  have hcstate : c.2 = es.2 := by
    rw [StateT.run_lift, bind_pure_comp, support_map] at hc
    obtain ⟨a, _, he⟩ := hc
    exact congrArg Prod.snd he.symm
  simp [hpadissued, hcstate, hreads, hseedstate, OracleState.empty]

lemma observedRun_sound [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0) :
    ∀ ω ∈ support (observedRun pp m A), ∀ hc : ValidCoins pp.qap ω.1.out.coins,
      ObsSound pp ω.1.enc ⟨ω.1.out.coins, hc⟩ ω.2 := by
  intro ω hω hc
  unfold observedRun at hω
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hω
  obtain ⟨σ, _, es, hes, z, hz, rfl⟩ := hω
  have hv := Praxis.Proofs.GroupModel.encGame_view σ pp m es hes
  have hi := encGame_issued pp σ m es hes
  apply obsRun_sound pp σ ⟨es.1.coins, hc⟩ _ _ ?_ z hz
  refine ⟨?_, ?_, by simp⟩
  · simpa only [hv] using initialise_sound pp σ ⟨es.1.coins, hc⟩ es.1.forms
  · intro l hl
    apply initialise_covers pp es.1.forms es.1.pv l
    exact hi ▸ hl

lemma keyCmp_real (z : WorldOut P0) (hc : ValidCoins pp.qap z.out.coins)
    (sh : State pp) (hsh : Faithful pp z.enc ⟨z.out.coins, hc⟩ sh) (e : Collision pp)
    (he : keyCmp pp z sh = some e) :
    evaluate pp z.enc ⟨z.out.coins, hc⟩ e.new = evaluate pp z.enc ⟨z.out.coins, hc⟩ e.old := by
  let c : CoinDomain pp := ⟨z.out.coins, hc⟩
  unfold keyCmp at he
  cases hp : sh.dict .gₜ (z.enc .gₜ (kappa pp z.out.coins)) with
  | some P =>
    simp only [hp, Option.some.injEq] at he
    subst e
    exact ((z.enc .gₜ).injective (hsh .gₜ _ P hp)).trans (evaluate_key pp z.enc c).symm
  | none =>
    simp only [hp] at he
    cases hn : sh.dict .gₜ (z.enc .gₜ (-kappa pp z.out.coins)) with
    | none => simp [hn] at he
    | some P =>
      simp only [hn, Option.some.injEq] at he
      subst e
      have hv := (z.enc .gₜ).injective (hsh .gₜ _ P hn)
      change evaluate pp z.enc c (scalar pp (-1) * P) = evaluate pp z.enc c (key pp)
      rw [map_mul, evaluate_scalar, hv, evaluate_key]
      ring

lemma bad_real (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)
    (ω : World (ppOf ch S)) (hω : ω ∈ support (observedRun (ppOf ch S) m A))
    (e : Collision (ppOf ch S)) (he : BadAt ω e)
    (hc : ValidCoins (ppOf ch S).qap ω.1.out.coins) :
    evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.new =
      evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.old := by
  have hs := observedRun_sound (ppOf ch S) m A
  generalize observedRun (ppOf ch S) m A = obs at hs hω ⊢
  have hlog := (hs ω hω hc).2.2
  obtain ⟨b, hb, _, he⟩ := he
  unfold badCmp at he
  rw [hb] at he
  cases hstep : ω.2.steps[b]? with
  | none => simp [hstep] at he
  | some step =>
    simp only [hstep] at he
    have hsound := hlog step (List.mem_of_getElem? hstep)
    rcases hq : step.entry.1 with ((n | gq) | i) | kq
    · simp [hq] at he
    · exact (hsound.2 e (by simpa only [hq] using he)).2.1
    · simp [hq] at he
    · exact keyCmp_real (ppOf ch S) ω.1 hc step.shadow hsound.1 e
        (by simpa only [hq] using he)

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.BadReal
