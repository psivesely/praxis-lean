import Praxis.Proofs.NamesBound
import Praxis.Domain
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Relation

namespace Praxis.Proofs.Names

open OracleComp OracleSpec

theorem gg_name (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S) (Q QH : ℕ)
    (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => firstMark (ppOf ch S) f.w = some .guessName |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (ledgerName : ℝ) := by
  exact gg_name_bound ch S Q QH A hA m

end Praxis.Proofs.Names
