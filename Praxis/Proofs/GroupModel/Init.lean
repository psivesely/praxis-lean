import Praxis.Proofs.View.NoKey
import Praxis.Proofs.Degree
import Praxis.Proofs.GroupModel.Init.Assemble
import Praxis.Domain
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Relation

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

theorem gg_init (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S) (Q QH : ℕ)
    (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => firstMark (ppOf ch S) f.w = some .init |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (ledgerInit : ℝ) := by
  exact initial_world_bound ch S hS m A

end Praxis.Proofs.GroupModel
