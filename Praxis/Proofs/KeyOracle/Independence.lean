import Praxis.Games
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Keys
import Praxis.Params
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.KeyOracle

open OracleComp OracleSpec

def Clean {P : Params} (st : OracleState P) : Prop :=
  st.kdf = (fun _ => none) ∧ st.kdfLog = [] ∧ st.tr = []

theorem hf_clean {P : Params} [NeZero P.q] (i : Seed P × FormIndex P) (st : OracleState P)
    (hs : Clean st) (z : Rq P × OracleState P)
    (hz : z ∈ support ((hfLazy i).run st)) : Clean z.2 := by
  unfold hfLazy at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  next a h =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hs
  next h =>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨a, ha, he⟩ := hz
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨u, hu, he⟩ := he
    subst u
    subst z
    exact hs

theorem hf_list_clean {P : Params} [NeZero P.q] (seed : Seed P) (is : List (FormIndex P))
    (st : OracleState P) (hs : Clean st)
    (z : List (FormIndex P × Rq P) × OracleState P)
    (hz : z ∈ support ((is.mapM fun i => do
      let a ← hfLazy (seed, i)
      pure (i, a)).run st)) : Clean z.2 := by
  induction is generalizing st z with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hs
  | cons i is ih =>
    simp only [List.mapM_cons, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨a, ha, b, hb, hz⟩ := hz
    have hc : Clean a.2 := by
      simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at ha
      obtain ⟨v, hv, he⟩ := ha
      subst a
      exact hf_clean (seed, i) st hs v hv
    have hc' := ih a.2 hc b hb
    have he : z = (a.1 :: b.1, b.2) := by simpa using hz
    subst z
    exact hc'

variable {P : Params} [Fact (Nat.Prime P.q)]

local instance : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩

abbrev PrefixData (pp : PublicParams P) :=
  Seed P × FormMatrix P × {c : Coins P // ValidCoins pp.qap c}

noncomputable def encPrefix (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] : GameM P (PrefixData pp) :=
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  do
    let seed ← (StateT.lift ($ᵗ (Seed P)) : GameM P (Seed P))
    let entries ← (formIndexList P).mapM fun i => do
      let a ← hfLazy (seed, i)
      pure (i, a)
    let A : FormMatrix P := fun i =>
      ((entries.find? fun e => decide (e.1 = i)).map Prod.snd).getD 0
    let c ← (StateT.lift ($ᵗ {c : Coins P // ValidCoins pp.qap c}) : GameM P _)
    pure (seed, A, c)

theorem prefix_clean (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (z : PrefixData pp × OracleState P)
    (hz : z ∈ support ((encPrefix pp).run OracleState.empty)) : Clean z.2 := by
  simp only [encPrefix, StateT.run_bind, StateT.run_lift, bind_map_left, mem_support_bind_iff,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨seed, hseed, entries, hent, c, hc, he⟩ := hz
  obtain ⟨s, hs, rfl⟩ := hseed
  obtain ⟨coin, hcoin, rfl⟩ := hc
  subst z
  exact hf_list_clean s (formIndexList P) OracleState.empty ⟨rfl, rfl, rfl⟩ entries hent

noncomputable def finish (σ : LabelEncoding P) (pp : PublicParams P)
    (m : Msg P) (d : PrefixData pp) (st : OracleState P) (p : Msg P) :
    EncOut P × OracleState P :=
  let pv := pubView σ pp (formVec d.2.1) d.2.2.1
  (⟨pv, ⟨d.1, m ^^^ p⟩, d.2.1, d.2.2.1⟩,
    { st with kdf := Function.update st.kdf (labelName (σ .gₜ) (kappa pp d.2.2.1)) (some p)
              issuedT := st.issuedT ∪ (pv.gT.map Prod.snd).toFinset })

noncomputable def suffix (σ : LabelEncoding P) (pp : PublicParams P)
    (m : Msg P) (d : PrefixData pp) : GameM P (EncOut P) := do
  let pad ← kdfLazy (labelName (σ .gₜ) (kappa pp d.2.2.1))
  let pv := pubView σ pp (formVec d.2.1) d.2.2.1
  modify fun st => { st with issuedT := st.issuedT ∪ (pv.gT.map Prod.snd).toFinset }
  pure ⟨pv, ⟨d.1, m ^^^ pad⟩, d.2.1, d.2.2.1⟩

theorem enc_split (σ : LabelEncoding P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) :
    evalSPMF ((encGame σ pp m).run OracleState.empty) =
      evalSPMF (do
        let z ← (encPrefix pp).run OracleState.empty
        let p ← $ᵗ (Msg P)
        pure (finish σ pp m z.1 z.2 p)) := by
  have he : encGame σ pp m = (do
      let d ← encPrefix pp
      suffix σ pp m d) := by
    simp only [encGame, encAt, encPrefix, suffix, bind_assoc, pure_bind]
  rw [he, StateT.run_bind]
  apply evalSPMF_bind_congr
  intro z hz
  have hk := (prefix_clean pp z hz).1
  simp only [suffix, StateT.run_bind, kdfLazy, StateT.run_get, pure_bind, hk,
    StateT.run_lift, StateT.run_modify, StateT.run_pure, bind_map_left, finish]
  simp only [bind_assoc, pure_bind, hk]

theorem uniform_xor {α : Type} (m : Msg P) (k : Msg P → ProbComp α) :
    evalSPMF (($ᵗ (Msg P)) >>= fun c => k (c ^^^ m)) =
      evalSPMF (($ᵗ (Msg P)) >>= k) := by
  have hx : Function.Involutive (fun c : Msg P => c ^^^ m) := by
    intro c
    simp [BitVec.xor_assoc]
  apply evalSPMF_ext
  intro a
  exact probOutput_bind_bijective_uniform_cross (Msg P) _ hx.bijective k a

theorem enc_common_header (σ : LabelEncoding P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) :
    evalSPMF ((encGame σ pp m).run OracleState.empty) =
      evalSPMF (do
        let z ← (encPrefix pp).run OracleState.empty
        let c ← $ᵗ (Msg P)
        pure (finish σ pp m z.1 z.2 (c ^^^ m))) := by
  rw [enc_split σ pp m]
  apply evalSPMF_bind_congr
  intro z hz
  exact (uniform_xor m (fun p => pure (finish σ pp m z.1 z.2 p))).symm

end Praxis.Proofs.KeyOracle
