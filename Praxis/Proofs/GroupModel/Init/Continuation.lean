import Praxis.Proofs.GroupModel.Init.World
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

theorem encAt_event_bound {P : Params} [Fact (Nat.Prime P.q)] [NeZero P.q]
    (σ : LabelEncoding P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (seed : Seed P) (st : OracleState P)
    (E : FormMatrix P → Coins P → Prop) (ε : ENNReal)
    (hb : ∀ F, letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
      Pr[fun c => E F c.1 | $ᵗ {c : Coins P // ValidCoins pp.qap c}] ≤ ε) :
    Pr[fun z => E z.1.forms z.1.coins | (encAt σ pp m seed).run st] ≤ ε := by
  classical
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  unfold encAt
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, Function.comp_def]
  apply probEvent_bind_le_of_forall_le
  intro entries he
  apply le_trans (probEvent_bind_le_probEvent (p := fun c => E
    (fun i => ((entries.1.find? fun e => decide (e.1 = i)).map Prod.snd).getD 0) c.1) ?_)
    (hb _)
  intro c hc hn
  apply probEvent_eq_zero
  intro z hz h
  simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_modify,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨pad, hp, rfl⟩ := hz
  exact hn h

theorem encGame_event_bound {P : Params} [Fact (Nat.Prime P.q)] [NeZero P.q]
    (σ : LabelEncoding P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (st : OracleState P)
    (E : FormMatrix P → Coins P → Prop) (ε : ENNReal)
    (hb : ∀ F, letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
      Pr[fun c => E F c.1 | $ᵗ {c : Coins P // ValidCoins pp.qap c}] ≤ ε) :
    Pr[fun z => E z.1.forms z.1.coins | (encGame σ pp m).run st] ≤ ε := by
  unfold encGame
  simp only [StateT.run_bind, StateT.run_lift]
  apply probEvent_bind_le_of_forall_le
  intro seed hs
  exact encAt_event_bound σ pp m seed.1 seed.2 E ε hb

theorem worldRun_event_bound {P : Params} [Fact (Nat.Prime P.q)] [NeZero P.q]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (A : Adversary P)
    (E : FormMatrix P → Coins P → Prop) (ε : ENNReal)
    (hb : ∀ F, letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
      Pr[fun c => E F c.1 | $ᵗ {c : Coins P // ValidCoins pp.qap c}] ≤ ε) :
    Pr[fun w => E w.out.forms w.out.coins | worldRun pp m A] ≤ ε := by
  classical
  unfold worldRun
  apply probEvent_bind_le_of_forall_le
  intro σ hσ
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  unfold runWith
  simp only [StateT.run_bind]
  apply le_trans (probEvent_bind_le_probEvent
    (p := fun z => E z.1.forms z.1.coins) ?_) (encGame_event_bound σ pp m _ E ε hb)
  intro z hz hn
  apply probEvent_eq_zero
  intro out hout he
  simp only [mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hout
  obtain ⟨a, ha, rfl⟩ := hout
  exact hn he

end Praxis.Proofs.GroupModel
