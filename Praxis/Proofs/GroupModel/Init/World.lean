import Praxis.Proofs.GroupModel.Init.Collision
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

theorem encAt_view {P : Params} [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (seed : Seed P) (st : OracleState P) (z : EncOut P × OracleState P)
    (hz : z ∈ support ((encAt σ pp m seed).run st)) :
    z.1.pv = pubView σ pp (formVec z.1.forms) z.1.coins := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  unfold encAt at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hz⟩ := hz
  simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hb
  obtain ⟨x, _, rfl⟩ := hb
  simp only [StateT.run_modify, support_pure, Set.mem_singleton_iff] at hd
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hd
  subst hz
  rfl

theorem encGame_view {P : Params} [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (z : EncOut P × OracleState P)
    (hz : z ∈ support ((encGame σ pp m).run OracleState.empty)) :
    z.1.pv = pubView σ pp (formVec z.1.forms) z.1.coins := by
  unfold encGame at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, _, hz⟩ := hz
  exact encAt_view σ pp m a.1 a.2 z hz

theorem worldRun_view {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) (A : Adversary P)
    (w : WorldOut P) (hw : w ∈ support (worldRun pp m A)) :
    w.out.pv = pubView w.enc pp (formsOfRun w) w.out.coins := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  unfold worldRun at hw
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨σ, _, r, hr, rfl⟩ := hw
  unfold runWith at hr
  simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨es, hes, z, hz, rfl⟩ := hr
  exact encGame_view σ pp m es hes

theorem worldRun_init_event_bound {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) (A : Adversary P)
    (E : WorldOut P → Prop)
    (hE : ∀ w, w.out.pv = pubView w.enc pp (formsOfRun w) w.out.coins →
      firstMark pp w = some .init → E w) :
    Pr[fun w => firstMark pp w = some .init | worldRun pp m A] ≤
      Pr[E | worldRun pp m A] := by
  apply probEvent_mono
  intro w hw hmark
  exact hE w (worldRun_view pp m A w hw) hmark

end Praxis.Proofs.GroupModel
