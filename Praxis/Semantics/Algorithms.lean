import Praxis.Params
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.ZMod.Basic
import Praxis.Published
import Praxis.Games
import Praxis.Domain
import Praxis.Enc
import Praxis.Keys

namespace Praxis.Semantics

open Praxis Praxis.Algebra OracleComp OracleSpec

theorem countedRun_forget {P : Params} [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (A : Adversary P) (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) :
    (fun z => ((z.1.1, z.1.2.1), z.2)) <$> countedRun σ A pp m =
      runWith σ A (encGame σ pp m) OracleState.empty := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  have key : (fun z : EncOut P × Bool × QueryCount CallKind => (z.1, z.2.1)) <$>
      (do
        let e ← encGame σ pp m
        let oc ← (simulateQ ((gameImpl σ).withCost callCost) (A.run e.pv e.header)).run
        pure (e, oc) : GameM P _) =
      (do
        let e ← encGame σ pp m
        let o ← simulateQ (gameImpl σ) (A.run e.pv e.header)
        pure (e, o)) := by
    simp only [map_bind, map_pure]
    congr 1
    funext e
    rw [← QueryImpl.fst_map_run_withCost (gameImpl σ) callCost (A.run e.pv e.header),
      bind_map_left]
  unfold countedRun runWith
  rw [← key, StateT.run_map]

end Praxis.Semantics
