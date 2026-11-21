import Praxis.Proofs.Reduction.Law.Forms
import Praxis.Proofs.Reduction.Law.Sampling
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Params
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Reduction

open OracleComp OracleSpec

variable {P : Params}

noncomputable def stateWith (seed : Seed P) (t : FormIndex P → Option (Rq P)) :
    OracleState P :=
  { OracleState.empty with hf := fun x => if x.1 = seed then t x.2 else none }

theorem stateWith_update (seed : Seed P) (t : FormIndex P → Option (Rq P))
    (i : FormIndex P) (v : Rq P) :
    {stateWith seed t with hf := Function.update (stateWith seed t).hf (seed, i) (some v)} =
      stateWith seed (Function.update t i (some v)) := by
  simp only [stateWith, OracleState.mk.injEq, and_true]
  funext ⟨s, j⟩
  by_cases hs : s = seed
  · subst s
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_apply, hj]
  · simp [Function.update_apply, hs]

noncomputable def readEntries [NeZero P.q] (seed : Seed P) (l : List (FormIndex P)) :
    GameM P (List (FormIndex P × Rq P)) :=
  l.mapM fun i => do
    let a ← hfLazy (seed, i)
    pure (i, a)

theorem readEntries_cached [NeZero P.q] (seed : Seed P) (B : FormMatrix P)
    (l : List (FormIndex P)) (st : OracleState P)
    (h : ∀ i ∈ l, st.hf (seed, i) = some (B i)) :
    (readEntries seed l).run st = pure (l.map (fun i => (i, B i)), st) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi := h i (by simp)
    have hl := ih (fun j hj => h j (by simp [hj]))
    simpa [readEntries, List.mapM_cons, hfLazy, StateT.run_bind, hi] using
      congrArg (fun oc => oc >>= fun z => pure ((i, B i) :: z.1, z.2)) hl

theorem readEntries_fresh [NeZero P.q] (seed : Seed P) (l : List (FormIndex P))
    (t : FormIndex P → Option (Rq P)) (hn : l.Nodup) (ht : ∀ i ∈ l, t i = none) :
    (readEntries seed l).run (stateWith seed t) = (do
      let z ← readFresh l t
      pure (z.1, stateWith seed z.2)) := by
  classical
  induction l generalizing t with
  | nil => simp [readEntries, readFresh]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.mp hn).1
    have hl : l.Nodup := (List.nodup_cons.mp hn).2
    have ht' : t i = none := ht i (by simp)
    simp only [readEntries, List.mapM_cons, hfLazy, StateT.run_bind, StateT.run_get,
      pure_bind, stateWith, if_true, ht', StateT.run_lift, StateT.run_modify,
      StateT.run_pure, bind_assoc, readFresh]
    congr 1
    funext v
    have htail : ∀ j ∈ l, Function.update t i (some v) j = none := by
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact ht j (by simp [hj])
    have h := ih (Function.update t i (some v)) hl htail
    rw [← stateWith_update] at h
    simp only [readEntries, stateWith, hfLazy, bind_assoc] at h
    rw [h]
    simp [bind_assoc]

theorem readEntries_empty_law [NeZero P.q] (seed : Seed P) :
    𝒮[(readEntries seed (formIndexList P)).run OracleState.empty] =
      𝒮[do let B ← $ᵗ (FormMatrix P)
           pure ((formIndexList P).map (fun i => (i, B i)),
             OracleState.empty.programHF seed B)] := by
  classical
  have he : stateWith seed (fun _ => none) = OracleState.empty := by
    simp [stateWith, OracleState.empty]
  conv_lhs => rw [← he, readEntries_fresh seed _ _ formIndexList_nodup (by simp)]
  rw [evalSPMF_bind, readFresh_law _ _ formIndexList_nodup, ← evalSPMF_bind]
  simp only [bind_assoc, pure_bind]
  apply evalSPMF_bind_congr
  intro B hB
  congr 1
  simp [stateWith, OracleState.programHF, OracleState.empty, formIndexList_complete]

noncomputable def freshPrefix [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) (m : Msg P) (seed : Seed P) (B : FormMatrix P)
    (c : {c : Coins P // ValidCoins pp.qap c}) (pad : Msg P) : EncOut P × OracleState P :=
  let pv := pubView σ pp (formVec B) c.1
  let st := OracleState.empty.programHF seed B
  (⟨pv, ⟨seed, m ^^^ pad⟩, B, c.1⟩,
    {st with
      kdf := Function.update st.kdf (labelName (σ .gₜ) (kappa pp c.1)) (some pad)
      issuedT := st.issuedT ∪ (pv.gT.map Prod.snd).toFinset})

theorem encAt_programmed [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (seed : Seed P) (B : FormMatrix P) :
    letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
    (encAt σ pp m seed).run (OracleState.empty.programHF seed B) = (do
      let c ← $ᵗ {c : Coins P // ValidCoins pp.qap c}
      let pad ← $ᵗ (Msg P)
      pure (freshPrefix σ pp m seed B c pad)) := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  have hr := readEntries_cached seed B (formIndexList P) (OracleState.empty.programHF seed B)
    (fun i _ => by simp [OracleState.programHF])
  unfold readEntries at hr
  unfold encAt
  simp only [StateT.run_bind]
  rw [hr, pure_bind, reconstruct_forms]
  simp [kdfLazy, OracleState.programHF, OracleState.empty, StateT.run_bind,
    StateT.run_lift, StateT.run_get, StateT.run_modify, StateT.run_pure, freshPrefix,
    bind_assoc]

theorem encAt_empty_law [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (seed : Seed P) :
    𝒮[(encAt σ pp m seed).run OracleState.empty] =
      𝒮[do let B ← $ᵗ (FormMatrix P)
           (encAt σ pp m seed).run (OracleState.empty.programHF seed B)] := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  unfold encAt
  simp only [StateT.run_bind]
  change 𝒮[(readEntries seed (formIndexList P)).run OracleState.empty >>= _] = _
  rw [evalSPMF_bind, readEntries_empty_law, ← evalSPMF_bind]
  simp only [bind_assoc, pure_bind]
  apply evalSPMF_bind_congr
  intro B hB
  have hr := readEntries_cached seed B (formIndexList P) (OracleState.empty.programHF seed B)
    (fun i _ => by simp [OracleState.programHF])
  unfold readEntries at hr
  rw [hr, pure_bind]

end Praxis.Proofs.Reduction
