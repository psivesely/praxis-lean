import Praxis.Proofs.NamesReservoir
import Praxis.Proofs.Basic
import Praxis.Proofs.Cap
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Label.Injections
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Names.Game

open OracleComp OracleSpec GroupModel.Sorted

variable {P : Params}

abbrev ObsModel (P : Params) := Reservoir.Definitions (Fq P) (Label P)

abbrev ObsComp (P : Params) := OracleComp (ObsModel P)

abbrev ObsM (P : Params) := StateT (OracleState P) (ObsComp P)

def withGT (src : LabelEncoding P) (σ : Fq P ↪ Label P) : LabelEncoding P
  | .g₁ => src .g₁
  | .g₂ => src .g₂
  | .gₜ => σ

noncomputable def liftCoins {α : Type} (oc : ProbComp α) : ObsComp P α :=
  simulateQ (fun n => liftM ((ObsModel P).query (.inl n))) oc

noncomputable def liftGame {α : Type} (oc : GameM P α) : ObsM P α :=
  StateT.mk fun st => liftCoins (oc.run st)

noncomputable def encodeGT (x : Fq P) : ObsM P (Label P) :=
  StateT.lift (liftM ((ObsModel P).query (.inr (.encode x))))

noncomputable def decodeGT (t : Label P) : ObsM P (Option (Fq P)) :=
  StateT.lift (liftM ((ObsModel P).query (.inr (.decode t))))

theorem liftCoins_bound {α : Type} (oc : ProbComp α) :
    IsQueryBoundP (liftCoins (P := P) oc) Reservoir.isProbe 0 := by
  induction oc using OracleComp.inductionOn with
  | pure a => simp [liftCoins]
  | query_bind n k ih =>
    change IsQueryBoundP
      ((liftM ((ObsModel P).query (.inl n)) : ObsComp P _) >>= fun u => liftCoins (k u))
      Reservoir.isProbe 0
    simpa [isQueryBoundP_query_bind_iff, Reservoir.isProbe] using ih

theorem liftGame_bound {α : Type} (oc : GameM P α) (st : OracleState P) :
    IsQueryBoundP ((liftGame oc).run st) Reservoir.isProbe 0 := liftCoins_bound _

theorem encodeGT_bound (x : Fq P) (st : OracleState P) :
    IsQueryBoundP ((encodeGT x).run st) Reservoir.isProbe 1 := by
  simp [encodeGT, StateT.run_lift, isQueryBoundP_map_iff, Reservoir.isProbe]

theorem decodeGT_bound (t : Label P) (st : OracleState P) :
    IsQueryBoundP ((decodeGT t).run st) Reservoir.isProbe 1 := by
  simp [decodeGT, StateT.run_lift, isQueryBoundP_map_iff, Reservoir.isProbe]

noncomputable def plain (σ : Fq P ↪ Label P) : QueryImpl (ObsModel P) ProbComp := by
  let probes : QueryImpl (Reservoir.probeModel (Fq P) (Label P)) ProbComp :=
    fun q => pure (Reservoir.observe q σ)
  exact QueryImpl.ofLift unifSpec ProbComp + probes

theorem decode_eq (σ : Fq P ↪ Label P) (t : Label P) :
    Reservoir.decode σ t = Algebra.decodeLabel σ t := rfl

theorem liftCoins_plain (σ : Fq P ↪ Label P) {α : Type} (oc : ProbComp α) :
    simulateQ (plain σ) (liftCoins oc) = oc := by
  unfold liftCoins
  rw [← QueryImpl.simulateQ_compose]
  have he : QueryImpl.compose (plain σ)
      (fun n => liftM ((ObsModel P).query (.inl n))) = QueryImpl.id' unifSpec := by
    funext n
    simp [QueryImpl.compose, plain, simulateQ_query]
  rw [he, simulateQ_id']

theorem liftGame_plain (σ : Fq P ↪ Label P) {α : Type} (oc : GameM P α) (st : OracleState P) :
    simulateQ (plain σ) ((liftGame oc).run st) = oc.run st := liftCoins_plain σ _

theorem encodeGT_plain (σ : Fq P ↪ Label P) (x : Fq P) (st : OracleState P) :
    simulateQ (plain σ) ((encodeGT x).run st) = pure (σ x, st) := by
  simp [encodeGT, StateT.run_lift, plain, simulateQ_query, Reservoir.observe]

theorem decodeGT_plain (σ : Fq P ↪ Label P) (t : Label P) (st : OracleState P) :
    simulateQ (plain σ) ((decodeGT t).run st) = pure (Algebra.decodeLabel σ t, st) := by
  simp [decodeGT, StateT.run_lift, plain, simulateQ_query, Reservoir.observe, decode_eq]

noncomputable def answer (src : LabelEncoding P) (issued : Finset (Label P)) :
    (qr : GQuery P) → ObsM P qr.Result
  | .lin .g₁ a b u v => pure (groupAnswer src issued (.lin .g₁ a b u v))
  | .lin .g₂ a b u v => pure (groupAnswer src issued (.lin .g₂ a b u v))
  | .lin .gₜ a b u v => do
    let x ← decodeGT u
    let y ← decodeGT v
    match x, y with
    | some x, some y => some <$> encodeGT (a*x + b*y)
    | _, _ => pure none
  | .pair u v => do
    match Algebra.decodeLabel (src .g₁) u, Algebra.decodeLabel (src .g₂) v with
    | some x, some y => some <$> encodeGT (x*y)
    | _, _ => pure none
  | .name v => do
    if v ∈ issued then
      let x ← decodeGT v
      match x with
      | none => pure none
      | some x =>
        let neg ← encodeGT (-x)
        pure (some s(v, neg))
    else pure none

theorem answer_plain (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (issued : Finset (Label P)) (qr : GQuery P) (st : OracleState P) :
    simulateQ (plain σ) ((answer src issued qr).run st) =
      pure (groupAnswer (withGT src σ) issued qr, st) := by
  classical
  cases qr with
  | lin s a b u v =>
    cases s
    · simp [answer, groupAnswer, withGT]
    · simp [answer, groupAnswer, withGT]
    · cases hx : Algebra.decodeLabel σ u <;> cases hy : Algebra.decodeLabel σ v <;>
        simp [answer, StateT.run_bind, StateT.run_map, simulateQ_bind,
          decodeGT_plain, encodeGT_plain, groupAnswer, withGT, hx, hy]
  | pair u v =>
    cases hx : Algebra.decodeLabel (src .g₁) u <;> cases hy : Algebra.decodeLabel (src .g₂) v <;>
      simp [answer, StateT.run_map,
        encodeGT_plain, groupAnswer, withGT, hx, hy]
  | name v =>
    by_cases hv : v ∈ issued
    · cases hx : Algebra.decodeLabel σ v with
      | none =>
        simp [answer, hv, StateT.run_bind, simulateQ_bind, decodeGT_plain,
          groupAnswer, withGT, hx]
      | some x =>
        have he := (Algebra.Label.RefCoupling.decodeLabel_eq_some_iff σ v x).mp hx
        simp [answer, hv, StateT.run_bind, simulateQ_bind, decodeGT_plain,
          encodeGT_plain, groupAnswer, withGT, hx, labelName, he]
    · simp [answer, hv, groupAnswer]

noncomputable def group (src : LabelEncoding P) : QueryImpl (groupModel P) (ObsM P) :=
  fun qr => do
    let r ← answer src (← get).issuedT qr
    match trEntry qr r with
    | some e => modify fun st =>
        { st with
          tr := st.tr ++ [e]
          issuedT := match e.issuedGT with
            | some l => insert l st.issuedT
            | none => st.issuedT }
    | none => pure ()
    liftGame (handOut qr r)

theorem group_plain (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (qr : GQuery P) (st : OracleState P) :
    simulateQ (plain σ) ((group src qr).run st) = (groupImpl (withGT src σ) qr).run st := by
  classical
  simp only [group, groupImpl, StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind]
  rw [answer_plain]
  simp only [pure_bind]
  split <;> simp_all [StateT.run_modify, StateT.run_bind, liftGame_plain]
  all_goals rfl

noncomputable def cacheTarget (target : ClassName P) (pad : Msg P) (st : OracleState P) : OracleState P :=
  { st with kdf := Function.update st.kdf target (some pad) }

@[simp] theorem cacheTarget_issuedT (target : ClassName P) (pad : Msg P) (st : OracleState P) :
    (cacheTarget target pad st).issuedT = st.issuedT := rfl

@[simp] theorem cacheTarget_names (target : ClassName P) (pad : Msg P) (st : OracleState P) :
    (cacheTarget target pad st).names = st.names := rfl

@[simp] theorem cacheTarget_tr (target : ClassName P) (pad : Msg P) (st : OracleState P) :
    (cacheTarget target pad st).tr = st.tr := rfl

@[simp] theorem cacheTarget_kdfLog (target : ClassName P) (pad : Msg P) (st : OracleState P) :
    (cacheTarget target pad st).kdfLog = st.kdfLog := rfl

theorem hfLazy_cacheTarget [NeZero P.q] (target : ClassName P) (pad : Msg P)
    (i : Seed P × FormIndex P) (st : OracleState P) :
    (hfLazy i).run (cacheTarget target pad st) =
      (fun r => (r.1, cacheTarget target pad r.2)) <$> (hfLazy i).run st := by
  classical
  cases hh : st.hf i <;>
    simp [hfLazy, cacheTarget, hh, StateT.run_bind, StateT.run_lift,
      StateT.run_modify, StateT.run_pure]

theorem kdfLazy_cacheTarget_off (target nm : ClassName P) (pad : Msg P)
    (hne : nm ≠ target) (st : OracleState P) :
    (kdfLazy nm).run (cacheTarget target pad st) =
      (fun r => (r.1, cacheTarget target pad r.2)) <$> (kdfLazy nm).run st := by
  classical
  cases hh : st.kdf nm <;>
    simp [kdfLazy, cacheTarget, Function.update_of_ne hne, hh, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, StateT.run_pure,
      Function.update_comm hne]

theorem handOut_cacheTarget (target : ClassName P) (pad : Msg P)
    (qr : GQuery P) (r : qr.Result) (st : OracleState P) :
    (handOut qr r).run (cacheTarget target pad st) =
      (fun z => (z.1, cacheTarget target pad z.2)) <$> (handOut qr r).run st := by
  classical
  cases qr with
  | lin s a b u v => simp [handOut, cacheTarget]
  | pair u v => simp [handOut, cacheTarget]
  | name v =>
    cases r with
    | none => simp [handOut, cacheTarget]
    | some nm =>
      simp only [handOut, nameRef, StateT.run_bind, StateT.run_map, StateT.run_get, pure_bind]
      cases hn : st.names.findIdx? (· == nm) <;>
        simp [cacheTarget, hn, StateT.run_set, StateT.run_pure]

theorem groupImpl_cacheTarget (target : ClassName P) (pad : Msg P)
    (σ : LabelEncoding P) (qr : GQuery P) (st : OracleState P) :
    (groupImpl σ qr).run (cacheTarget target pad st) =
      (fun r => (r.1, cacheTarget target pad r.2)) <$> (groupImpl σ qr).run st := by
  classical
  simp only [groupImpl, StateT.run_bind, StateT.run_get, pure_bind, cacheTarget_issuedT]
  cases he : trEntry qr (groupAnswer σ st.issuedT qr) with
  | none => simpa only [he, StateT.run_pure, pure_bind] using
      handOut_cacheTarget target pad qr (groupAnswer σ st.issuedT qr) st
  | some e =>
    exact handOut_cacheTarget target pad qr (groupAnswer σ st.issuedT qr)
      { st with tr := st.tr ++ [e], issuedT := match e.issuedGT with
          | some l => insert l st.issuedT
          | none => st.issuedT }

def targetPair (κ : Fq P) (x y : Option (Fq P)) : Prop :=
  (x = some κ ∧ y = some (-κ)) ∨ (x = some (-κ) ∧ y = some κ)

instance (κ : Fq P) (x y : Option (Fq P)) : Decidable (targetPair κ x y) := by
  unfold targetPair
  infer_instance

theorem targetPair_iff (σ : Fq P ↪ Label P) (κ : Fq P) (a b : Label P) :
    targetPair κ (Reservoir.decode σ a) (Reservoir.decode σ b) ↔
      s(a, b) = labelName σ κ := by
  simp only [targetPair, Reservoir.decode_some_iff, labelName, Sym2.eq_iff]
  tauto

theorem targetPair_out_iff (σ : Fq P ↪ Label P) (κ : Fq P) (nm : ClassName P) :
    targetPair κ (Algebra.decodeLabel σ nm.out.1) (Algebra.decodeLabel σ nm.out.2) ↔
      nm = labelName σ κ := by
  simpa only [decode_eq, Sym2.mk, nm.out_eq] using targetPair_iff σ κ nm.out.1 nm.out.2

noncomputable def resolvedKdf (κ : Fq P) (pad : Msg P) (nm : ClassName P) : ObsM P (Option (Msg P)) := do
  modify fun st => { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }
  let x ← decodeGT nm.out.1
  let y ← decodeGT nm.out.2
  if targetPair κ x y then pure (some pad) else liftGame (some <$> kdfLazy nm)

theorem resolvedKdf_plain (σ : Fq P ↪ Label P) (κ : Fq P) (pad : Msg P)
    (nm : ClassName P) (st : OracleState P) :
    (fun r => (r.1, cacheTarget (labelName σ κ) pad r.2)) <$>
        simulateQ (plain σ) ((resolvedKdf κ pad nm).run st) =
      ((do
        modify fun st : OracleState P => { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }
        some <$> kdfLazy nm) : GameM P _).run (cacheTarget (labelName σ κ) pad st) := by
  classical
  simp only [resolvedKdf, StateT.run_bind, StateT.run_modify, pure_bind, simulateQ_bind,
    decodeGT_plain, cacheTarget_tr, cacheTarget_kdfLog]
  by_cases ht : nm = labelName σ κ
  · simp [targetPair_out_iff, ht, kdfLazy, cacheTarget, StateT.run_map,
      StateT.run_bind, StateT.run_get, StateT.run_pure]
  · simp only [targetPair_out_iff, if_neg ht, liftGame_plain, StateT.run_map]
    simp only [Functor.map_map]
    let st' : OracleState P := { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }
    change (fun r : Msg P × OracleState P => (some r.1, cacheTarget (labelName σ κ) pad r.2)) <$>
        (kdfLazy nm).run st' =
      (fun r : Msg P × OracleState P => (some r.1, r.2)) <$>
        (kdfLazy nm).run (cacheTarget (labelName σ κ) pad st')
    rw [kdfLazy_cacheTarget_off (labelName σ κ) nm pad ht]
    simp only [Functor.map_map]

noncomputable def kdf (κ : Fq P) (pad : Msg P) (qk : KdfQuery P) : ObsM P (Option (Msg P)) := do
  let st ← get
  let nm? : Option (ClassName P) := match qk with
    | .ref k => st.names[k]?
    | .guess nm => some nm
  match nm? with
  | none => pure none
  | some nm => resolvedKdf κ pad nm

theorem kdf_plain (σ : Fq P ↪ Label P) (κ : Fq P) (pad : Msg P)
    (q : KdfQuery P) (st : OracleState P) :
    (fun r => (r.1, cacheTarget (labelName σ κ) pad r.2)) <$>
        simulateQ (plain σ) ((kdf κ pad q).run st) =
      (kdfImpl q).run (cacheTarget (labelName σ κ) pad st) := by
  classical
  cases q with
  | guess nm =>
    simpa [kdf, kdfImpl, StateT.run_bind, StateT.run_get] using resolvedKdf_plain σ κ pad nm st
  | ref k =>
    cases hn : st.names[k]? with
    | none => simp [kdf, kdfImpl, hn, cacheTarget, StateT.run_bind, StateT.run_get]
    | some nm =>
      simpa [kdf, kdfImpl, hn, StateT.run_bind, StateT.run_get] using resolvedKdf_plain σ κ pad nm st

noncomputable def handler [NeZero P.q] (src : LabelEncoding P) (κ : Fq P) (pad : Msg P) :
    QueryImpl (AdvModel P) (ObsM P) := by
  let coins : QueryImpl unifSpec (ObsM P) := fun n =>
    liftGame (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (GameM P)) n)
  let forms : QueryImpl (hfModel P) (ObsM P) := fun i => liftGame (hfLazy i)
  let keys : QueryImpl (kdfModel P) (ObsM P) := fun q => kdf κ pad q
  exact ((coins + group src) + forms) + keys

theorem handler_plain [NeZero P.q] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (pad : Msg P) (t : (AdvModel P).Domain) (st : OracleState P) :
    (fun r => (r.1, cacheTarget (labelName σ κ) pad r.2)) <$>
        simulateQ (plain σ) ((handler src κ pad t).run st) =
      (gameImpl (withGT src σ) t).run (cacheTarget (labelName σ κ) pad st) := by
  rcases t with (((n | qr) | i) | q)
  · simp [handler, gameImpl, liftGame_plain, QueryImpl.liftTarget,
      StateT.run_lift, cacheTarget, Functor.map_map]
  · simpa [handler, gameImpl, group_plain] using
      (groupImpl_cacheTarget (labelName σ κ) pad (withGT src σ) qr st).symm
  · simpa [handler, gameImpl, liftGame_plain] using
      (hfLazy_cacheTarget (labelName σ κ) pad i st).symm
  · simpa [handler, gameImpl] using kdf_plain σ κ pad q st

theorem simulate_handler_plain [NeZero P.q] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (pad : Msg P) {α : Type} (oa : OracleComp (AdvModel P) α) (st : OracleState P) :
    (fun r => (r.1, cacheTarget (labelName σ κ) pad r.2)) <$>
        simulateQ (plain σ) ((simulateQ (handler src κ pad) oa).run st) =
      (simulateQ (gameImpl (withGT src σ)) oa).run (cacheTarget (labelName σ κ) pad st) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact map_run_simulateQ_eq_of_query_map_eq
    ((plain σ).mapStateTBase (handler src κ pad)) (gameImpl (withGT src σ))
    (cacheTarget (labelName σ κ) pad) (fun t s => handler_plain src σ κ pad t s) oa st

noncomputable def initial [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (pp : PublicParams P)
    (forms : FormMatrix P) (c : Coins P) (hdr : Header P)
    (hf : Seed P × FormIndex P → Option (Rq P)) : ObsM P (EncOut P) := do
  let gen ← encodeGT 1
  let ct ← encodeGT (gtExp pp c)
  let pv := { pubView src pp (formVec forms) c with gT := [(none, gen), (some (), ct)] }
  set { OracleState.empty with hf := hf, issuedT := (pv.gT.map Prod.snd).toFinset }
  pure ⟨pv, hdr, forms, c⟩

noncomputable def program [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (pp : PublicParams P)
    (forms : FormMatrix P) (c : Coins P) (hdr : Header P) (pad : Msg P)
    (hf : Seed P × FormIndex P → Option (Rq P)) (A : Adversary P) (Q QH : ℕ) :
    ObsComp P ((EncOut P × Bool) × OracleState P) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  (do
    let e ← initial src pp forms c hdr hf
    let o ← simulateQ (handler src (kappa pp c) pad) ((cap Q QH A).run e.pv e.header)
    pure (e, o)).run OracleState.empty

end Praxis.Proofs.Names.Game
