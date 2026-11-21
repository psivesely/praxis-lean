import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.KeyOracle.Independence
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Params
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init.Sampling

variable {P : Params}

def Clean (st : OracleState P) : Prop :=
  st.kdf = (fun _ => none) ∧ st.tr = [] ∧ st.kdfLog = [] ∧ st.issuedT = ∅ ∧ st.names = []

theorem hfLazy_clean [NeZero P.q] (i : Seed P × FormIndex P) (st : OracleState P)
    (h : Clean st) : ∀ z ∈ support ((hfLazy i).run st), Clean z.2 := by
  cases hh : st.hf i <;>
    simpa [hfLazy, StateT.run_bind, StateT.run_get, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, hh, Clean] using h

noncomputable def readEntries [NeZero P.q] (seed : Seed P)
    (l : List (FormIndex P)) : GameM P (List (FormIndex P × Rq P)) :=
  l.mapM fun i => do
    let a ← hfLazy (seed, i)
    pure (i, a)

theorem readEntries_clean [NeZero P.q] (seed : Seed P) (l : List (FormIndex P))
    (st : OracleState P) (h : Clean st) :
    ∀ z ∈ support ((readEntries seed l).run st), Clean z.2 := by
  induction l generalizing st with
  | nil => simpa [readEntries] using h
  | cons i l ih =>
    simp only [readEntries, List.mapM_cons, StateT.run_bind, StateT.run_pure]
    intro z hz
    obtain ⟨u, hu, hz⟩ := mem_support_bind_peel _ _ hz
    obtain ⟨v, hv, hz⟩ := mem_support_bind_peel _ _ hz
    obtain rfl := eq_of_mem_support_pure _ hz
    have hc : Clean u.2 := by
      change u ∈ support ((hfLazy (seed, i)).run st >>= fun w => pure ((i, w.1), w.2)) at hu
      obtain ⟨w, hw, hu⟩ := mem_support_bind_peel _ _ hu
      obtain rfl := eq_of_mem_support_pure _ hu
      exact hfLazy_clean (seed, i) st h w hw
    exact ih u.2 hc v hv

def matrixOf (entries : List (FormIndex P × Rq P)) : FormMatrix P := fun i =>
  ((entries.find? fun e => decide (e.1 = i)).map Prod.snd).getD 0

structure Prepared (pp : PublicParams P) where
  seed : Seed P
  forms : FormMatrix P
  coins : {c : Coins P // ValidCoins pp.qap c}
  pad : Msg P
  hf : Seed P × FormIndex P → Option (Rq P)

noncomputable def prepare [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] : ProbComp (Prepared pp) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  do
    let seed ← $ᵗ (Seed P)
    let es ← (readEntries seed (formIndexList P)).run OracleState.empty
    let c ← $ᵗ {c : Coins P // ValidCoins pp.qap c}
    let pad ← $ᵗ (Msg P)
    pure ⟨seed, matrixOf es.1, c, pad, es.2.hf⟩

def Prepared.header {pp : PublicParams P} (d : Prepared pp) (m : Msg P) : Header P :=
  ⟨d.seed, m ^^^ d.pad⟩

def initialState (pv : PubView P) (hf : Seed P × FormIndex P → Option (Rq P)) : OracleState P :=
  { OracleState.empty with hf := hf, issuedT := (pv.gT.map Prod.snd).toFinset }

def cacheTarget (target : ClassName P) (pad : Msg P) (st : OracleState P) : OracleState P :=
  { st with kdf := Function.update st.kdf target (some pad) }

noncomputable def fixedOut [Fact (Nat.Prime P.q)] (src : LabelEncoding P)
    (pp : PublicParams P) (forms : FormMatrix P) (c : Coins P) (hdr : Header P) : EncOut P :=
  ⟨pubView src pp (formVec forms) c, hdr, forms, c⟩

theorem encGame_prepared [Fact (Nat.Prime P.q)] (σ : LabelEncoding P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) :
    (encGame σ pp m).run OracleState.empty =
      (fun d : Prepared pp =>
        (fixedOut σ pp d.forms d.coins.1 (d.header m),
          cacheTarget (labelName (σ .gₜ) (kappa pp d.coins.1)) d.pad
            (initialState (pubView σ pp (formVec d.forms) d.coins.1) d.hf))) <$> prepare pp := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [encGame, encAt, prepare, StateT.run_bind, StateT.run_lift, map_bind,
    bind_assoc, pure_bind]
  apply bind_congr
  intro seed
  change ((readEntries seed (formIndexList P)).run OracleState.empty >>= _) = _
  apply bind_congr_of_forall_mem_support
  intro es hes
  have hc := readEntries_clean seed (formIndexList P) OracleState.empty
    (by simp [Clean, OracleState.empty]) es hes
  rcases es with ⟨entries, st⟩
  rcases st with ⟨hf, kdf, tr, kl, issued, names⟩
  rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
  apply bind_congr
  intro c
  simp [kdfLazy, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_modify,
    StateT.run_pure, matrixOf, fixedOut, Prepared.header, cacheTarget, initialState,
    OracleState.empty]
  rfl

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init.Sampling
