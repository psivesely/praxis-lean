import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Operations
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Params
import Praxis.Reduction
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 800000

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable {P : Params}

theorem monEvents_append_kdf (tr : List (TrOp P)) (kl : List (ℕ × ClassName P))
    (nm : ClassName P) :
    monEvents tr (kl ++ [(tr.length, nm)]) = monEvents tr kl ++ [.kdf nm] := by
  have hp :
      (List.range tr.length).flatMap (fun k =>
        ((kl ++ [(tr.length, nm)]).filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          (tr[k]?).toList.map MonEvent.op) =
      (List.range tr.length).flatMap (fun k =>
        (kl.filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          (tr[k]?).toList.map MonEvent.op) := by
    apply List.flatMap_congr
    intro k hk
    have hk' := List.mem_range.mp hk
    simp [List.filter_append, show tr.length ≠ k by omega]
  unfold monEvents
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [hp]
  simp [List.filter_append, List.append_assoc]

theorem monEvents_append_op (tr : List (TrOp P)) (kl : List (ℕ × ClassName P))
    (op : TrOp P) (hkl : ∀ e ∈ kl, e.1 ≤ tr.length) :
    monEvents (tr ++ [op]) kl = monEvents tr kl ++ [.op op] := by
  have hp :
      (List.range tr.length).flatMap (fun k =>
        (kl.filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          ((tr ++ [op])[k]?).toList.map MonEvent.op) =
      (List.range tr.length).flatMap (fun k =>
        (kl.filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          (tr[k]?).toList.map MonEvent.op) := by
    apply List.flatMap_congr
    intro k hk
    rw [List.getElem?_append_left (List.mem_range.mp hk)]
  have hf : (kl.filter fun e => e.1 == tr.length + 1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    have hh := hkl e he
    simp [show e.1 ≠ tr.length + 1 by omega]
  unfold monEvents
  simp only [List.length_append, List.length_singleton, List.range_succ,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hp, hf]
  simp [List.append_assoc]

def Visible (st st' : OracleState P) : Prop :=
  st'.tr = st.tr ∧ st'.kdfLog = st.kdfLog ∧ st'.issuedT = st.issuedT

lemma handOut_visible (qr : GQuery P) (R : qr.Result) (st : OracleState P) :
    ∀ z ∈ support ((handOut qr R).run st), Visible st z.2 := by
  cases qr with
  | lin s a b u w => simp [handOut, Visible]
  | pair u w => simp [handOut, Visible]
  | name u =>
    cases R with
    | none => simp [handOut, Visible]
    | some nm =>
      cases hn : st.names.findIdx? (· == nm) <;>
        simp [handOut, nameRef, StateT.run_map, StateT.run_bind, StateT.run_get,
          StateT.run_set, hn, Visible]

lemma kdfLazy_visible (nm : ClassName P) (st : OracleState P) :
    ∀ z ∈ support ((kdfLazy nm).run st), Visible st z.2 := by
  cases hk : st.kdf nm <;>
    simp [kdfLazy, StateT.run_bind, StateT.run_get, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, hk, Visible]

lemma hfLazy_visible [NeZero P.q] (i : Seed P × FormIndex P) (st : OracleState P) :
    ∀ z ∈ support ((hfLazy i).run st), Visible st z.2 := by
  cases hk : st.hf i <;>
    simp [hfLazy, StateT.run_bind, StateT.run_get, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, hk, Visible]

variable (pp : PublicParams P0)

def LogBound (st : OracleState P0) : Prop := ∀ e ∈ st.kdfLog, e.1 ≤ st.tr.length

def queryEvents (σ : LabelEncoding P0) (st : OracleState P0) :
    (AdvModel P0).Domain → List (MonEvent P0)
  | .inl (.inl (.inr gq)) => (trEntry gq (groupAnswer σ st.issuedT gq)).toList.map MonEvent.op
  | .inr kq => (Simulation.kdfName st kq).toList.map MonEvent.kdf
  | _ => []

lemma finishGroup_events (q : GQuery P0) (R : q.Result) (st : OracleState P0)
    (h : LogBound st) :
    ∀ z ∈ support ((finishGroup q R).run st),
      monEvents z.2.tr z.2.kdfLog = monEvents st.tr st.kdfLog ++
        (trEntry q R).toList.map MonEvent.op ∧ LogBound z.2 := by
  unfold finishGroup
  cases he : trEntry q R with
  | none =>
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    intro z hz
    obtain ⟨htr, hkl, _⟩ := handOut_visible q R st z hz
    exact ⟨by simp [he, htr, hkl], by simpa only [LogBound, htr, hkl] using h⟩
  | some e =>
    simp only [StateT.run_bind, StateT.run_modify, pure_bind]
    intro z hz
    obtain ⟨htr, hkl, _⟩ := handOut_visible q R _ z hz
    refine ⟨?_, ?_⟩
    · simpa only [htr, hkl, he, Option.toList_some, List.map_cons, List.map_nil] using
        monEvents_append_op st.tr st.kdfLog e h
    · intro a ha
      rw [hkl] at ha
      have hh := h a ha
      simp only [htr, List.length_append, List.length_singleton]
      omega

lemma kdf_events (kq : KdfQuery P0) (st : OracleState P0) (h : LogBound st) :
    ∀ z ∈ support ((kdfImpl kq).run st),
      monEvents z.2.tr z.2.kdfLog = monEvents st.tr st.kdfLog ++
        (Simulation.kdfName st kq).toList.map MonEvent.kdf ∧ LogBound z.2 := by
  have hh (nm : ClassName P0) :
      ∀ z ∈ support ((do
        modify fun s : OracleState P0 => {s with kdfLog := s.kdfLog ++ [(s.tr.length, nm)]}
        some <$> kdfLazy nm : GameM P0 (Option (Msg P0))).run st),
        monEvents z.2.tr z.2.kdfLog = monEvents st.tr st.kdfLog ++ [.kdf nm] ∧
          LogBound z.2 := by
    simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_map, support_map,
      Set.mem_image]
    intro z hz
    obtain ⟨r, hr, rfl⟩ := hz
    obtain ⟨htr, hkl, _⟩ := kdfLazy_visible nm _ r hr
    refine ⟨?_, ?_⟩
    · simpa only [htr, hkl] using monEvents_append_kdf st.tr st.kdfLog nm
    · intro e he
      rw [hkl, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · simpa only [htr] using h e he
      · simpa only [htr] using le_refl st.tr.length
  cases kq with
  | guess nm => simpa only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind,
      Simulation.kdfName, Option.toList_some, List.map_cons, List.map_nil] using hh nm
  | ref k =>
    cases hn : st.names[k]? with
    | none =>
      simp only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind, hn, StateT.run_pure,
        support_pure, Set.mem_singleton_iff]
      intro z hz
      subst z
      exact ⟨by simp [Simulation.kdfName, hn], h⟩
    | some nm => simpa only [kdfImpl, StateT.run_bind, StateT.run_get, pure_bind, hn,
        Simulation.kdfName, Option.toList_some, List.map_cons, List.map_nil] using hh nm

lemma game_events (σ : LabelEncoding P0) (q : (AdvModel P0).Domain)
    (st : OracleState P0) (h : LogBound st) :
    ∀ z ∈ support ((gameImpl σ q).run st),
      monEvents z.2.tr z.2.kdfLog = monEvents st.tr st.kdfLog ++ queryEvents σ st q ∧
        LogBound z.2 := by
  rcases q with ((n | gq) | i) | kq
  · rw [Simulation.gameImpl_unif, support_map]
    rintro z ⟨a, _, rfl⟩
    exact ⟨by simp [queryEvents], h⟩
  · rw [Simulation.gameImpl_group, Simulation.groupImpl_factor']
    exact finishGroup_events gq (groupAnswer σ st.issuedT gq) st h
  · rw [Simulation.gameImpl_hf]
    intro z hz
    obtain ⟨htr, hkl, _⟩ := hfLazy_visible i st z hz
    exact ⟨by simp [queryEvents, htr, hkl], by simpa only [LogBound, htr, hkl] using h⟩
  · rw [Simulation.gameImpl_kdf]
    exact kdf_events kq st h

def monitor (cx : IdealCtx P0) (pv : PubView P0) (st : OracleState P0) : IdealState P0 :=
  (monEvents st.tr st.kdfLog).foldl (idealEvent cx) (idealInit cx pv)

lemma monitor_step (cx : IdealCtx P0) (pv : PubView P0) (σ : LabelEncoding P0)
    (q : (AdvModel P0).Domain) (st : OracleState P0) (h : LogBound st)
    (z : (AdvModel P0).Range q × OracleState P0)
    (hz : z ∈ support ((gameImpl σ q).run st)) :
    monitor cx pv z.2 = (queryEvents σ st q).foldl (idealEvent cx) (monitor cx pv st) := by
  unfold monitor
  rw [(game_events σ q st h z hz).1, List.foldl_append]

lemma visible_trans {a b c : OracleState P} (h : Visible a b) (h' : Visible b c) :
    Visible a c := ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

lemma mapM_visible {α β : Type} (f : α → GameM P β)
    (hf : ∀ a st z, z ∈ support ((f a).run st) → Visible st z.2)
    (xs : List α) (st : OracleState P) :
    ∀ z ∈ support ((xs.mapM f).run st), Visible st z.2 := by
  induction xs generalizing st with
  | nil => simp [Visible]
  | cons a xs ih =>
    intro z hz
    simp only [List.mapM_cons, StateT.run_bind] at hz
    obtain ⟨y, hy, hz⟩ := mem_support_bind_peel _ _ hz
    obtain ⟨w, hw, hz⟩ := mem_support_bind_peel _ _ hz
    have he := eq_of_mem_support_pure _ hz
    subst z
    exact visible_trans (hf a st y hy) (ih y.2 w hw)

lemma encGame_initial [Fact (Nat.Prime P.q)] (pp' : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp'.qap c}] (σ : LabelEncoding P) (m : Msg P) :
    ∀ z ∈ support ((encGame σ pp' m).run OracleState.empty),
      z.2.tr = [] ∧ z.2.kdfLog = [] ∧ z.2.issuedT = (z.1.pv.gT.map Prod.snd).toFinset := by
  intro z hz
  unfold encGame at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨seed, hseed, hz⟩ := mem_support_bind_peel _ _ hz
  unfold encAt at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨es, hes, hz⟩ := mem_support_bind_peel _ _ hz
  have hreads : Visible seed.2 es.2 := by
    apply mapM_visible _ _ _ _ es hes
    intro i st y hy
    simp only [StateT.run_bind] at hy
    obtain ⟨a, ha, hy⟩ := mem_support_bind_peel _ _ hy
    have he := eq_of_mem_support_pure _ hy
    rw [he]
    exact hfLazy_visible _ _ a ha
  obtain ⟨c, hc, hz⟩ := mem_support_bind_peel _ _ hz
  obtain ⟨pad, hpad, hz⟩ := mem_support_bind_peel _ _ hz
  have hpadvis := kdfLazy_visible _ _ pad hpad
  have hseedst : seed.2 = OracleState.empty := by
    obtain ⟨a, ha, he⟩ := mem_support_bind_peel _ _ hseed
    exact congrArg Prod.snd (eq_of_mem_support_pure _ he)
  have hcst : c.2 = es.2 := by
    obtain ⟨a, ha, he⟩ := mem_support_bind_peel _ _ hc
    exact congrArg Prod.snd (eq_of_mem_support_pure _ he)
  have hvis : Visible OracleState.empty pad.2 := by
    apply visible_trans (b := es.2)
    · simpa only [hseedst] using hreads
    · simpa only [hcst] using hpadvis
  simp at hz
  rw [hz]
  rcases hvis with ⟨htr, hkl, hiss⟩
  simp only [OracleState.empty] at htr hkl hiss
  exact ⟨htr, hkl, by simp only [hiss, Finset.empty_union]⟩

lemma initial_named (cx : IdealCtx P0) (pv : PubView P0) :
    (idealInit cx pv).named = fun _ => false := by
  have fold_named {α : Type} (f : IdealState P0 → α → IdealState P0)
      (hf : ∀ st a, (f st a).named = st.named) (xs : List α) (st : IdealState P0) :
      (xs.foldl f st).named = st.named := by
    induction xs generalizing st with
    | nil => rfl
    | cons a xs ih => exact (ih _).trans (hf st a)
  unfold idealInit
  rw [fold_named _ (by intro st e; cases st.mark <;> simp),
    fold_named _ (by intro st e; cases st.mark <;> simp),
    fold_named _ (by intro st e; cases st.mark <;> simp)]

lemma fold_insert_isSome (entries : List (GroupModel.Sorted.PSort × Label P0 × Poly pp))
    (sh : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h : (sh.dict s l).isSome) :
    (((entries.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) sh).dict s l).isSome) := by
  induction entries generalizing sh with
  | nil => exact h
  | cons e entries ih =>
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp h
    exact ih _ (Option.isSome_iff_exists.mpr ⟨P, (Simulation.insertResult_props pp sh e.1 e.2.1 e.2.2).2.2.1 s l P hP⟩)

lemma fold_insert_mem (entries : List (GroupModel.Sorted.PSort × Label P0 × Poly pp))
    (sh : State pp) (e : GroupModel.Sorted.PSort × Label P0 × Poly pp) (he : e ∈ entries) :
    (((entries.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) sh).dict e.1 e.2.1).isSome) := by
  induction entries generalizing sh with
  | nil => simp at he
  | cons a entries ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact fold_insert_isSome pp entries _ _ _ (Simulation.insertResult_isSome pp sh e.1 e.2.1 e.2.2)
    · exact ih _ he

lemma initial_cover (forms : FormMatrix P0) (pv : PubView P0) :
    ∀ l ∈ (pv.gT.map Prod.snd).toFinset,
      ∃ P, (initialise pp forms pv).dict .gₜ l = some P := by
  intro l hl
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
  apply Option.isSome_iff_exists.mp
  exact fold_insert_mem pp (initialEntries pp forms pv) (empty pp)
    (.gₜ, e.2, baseT pp forms (gtInit e.1))
    (by simp only [initialEntries, List.mem_append, List.mem_map]; exact Or.inr ⟨e, he, rfl⟩)

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync
