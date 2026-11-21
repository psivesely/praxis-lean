import Praxis.Proofs.NamesProbability
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Cap
import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesInitial
import Praxis.Proofs.NamesReservoir
import Praxis.Params
import Praxis.Setting
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Names.Game

open OracleComp OracleSpec

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

theorem initial_plain [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (pp : PublicParams P) (forms : FormMatrix P) (c : Coins P) (hdr : Header P)
    (hf : Seed P × FormIndex P → Option (Rq P)) (st : OracleState P) :
    simulateQ (plain σ) ((initial src pp forms c hdr hf).run st) =
      pure (fixedOut (withGT src σ) pp forms c hdr,
        initialState (pubView (withGT src σ) pp (formVec forms) c) hf) := by
  rw [← run_plain (kappa pp c) (-kappa pp c) σ _ .fresh, initial_tracked]
  rfl

theorem program_plain [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (pp : PublicParams P) (forms : FormMatrix P) (c : Coins P) (hdr : Header P) (pad : Msg P)
    (hf : Seed P × FormIndex P → Option (Rq P)) (A : Adversary P) (Q QH : ℕ) :
    restoredWorld src σ (kappa pp c) pad <$>
        simulateQ (plain σ) (program src pp forms c hdr pad hf A Q QH) =
      (fun z => (⟨withGT src σ, fixedOut (withGT src σ) pp forms c hdr, z.1, z.2⟩ : WorldOut P)) <$>
        (simulateQ (gameImpl (withGT src σ))
          ((cap Q QH A).run (pubView (withGT src σ) pp (formVec forms) c) hdr)).run
          (cacheTarget (labelName σ (kappa pp c)) pad
            (initialState (pubView (withGT src σ) pp (formVec forms) c) hf)) := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [program, StateT.run_bind, simulateQ_bind, initial_plain, pure_bind,
    StateT.run_pure, simulateQ_pure, bind_pure_comp]
  rw [← simulate_handler_plain src σ (kappa pp c) pad]
  simp [map_bind, restoredWorld, fixedOut, Functor.map_map]

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

end Praxis.Proofs.Names.Game
