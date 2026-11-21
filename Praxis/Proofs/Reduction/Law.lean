import Praxis.Proofs.Reduction.Complete
import Praxis.Proofs.Reduction.Law.Joint
import Praxis.Domain
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Relation
import Praxis.Scheme

namespace Praxis.Proofs.Reduction

open OracleComp OracleSpec

theorem red_law (ch : AdmissibleChoice P0) (S : Relation P0) (A : Adversary P0) (m : Msg P0) :
    (scheme ch).succ S m A =
      (Pr[fun f => RmWins main_d_ne_zero (ppOf ch S) m f |
        worldFull (ppOf ch S) m A extF]).toReal := by
  exact success_law main_d_ne_zero (ppOf ch S) m A extF

end Praxis.Proofs.Reduction
