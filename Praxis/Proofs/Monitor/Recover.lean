import Praxis.Proofs.Monitor.Recover.Assembly
import Praxis.Proofs.Monitor.Recover.Normal
import Praxis.Constants
import Praxis.Domain
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.QAP.Valid
import Praxis.Relation

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

theorem recovery_span (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (Q QH : ℕ) (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => ∃ D ι, GoodMark (ppOf ch S) f.w D ι ∧
        gradSpan (ppOf ch S) (recAssign f.w0 f.w1) D (markSector D) ≠ jointSpace (markStack D) |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (Constants.eps_f : ℝ) := by
  apply recovery_span_of_normal ch S hS A m
  intro w D ι hgood ω hc
  obtain ⟨k, hk, hd, hcmp⟩ := hgood
  exact recovery_normal (ppOf ch S) S (Praxis.Proofs.QAP.domainMap_valid ch S)
    (formsOfRun w) (realR w) D ι hcmp.1 ω hc (markSector D)

end Praxis.Proofs.Monitor
