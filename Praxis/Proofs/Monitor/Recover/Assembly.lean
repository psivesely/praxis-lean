import Praxis.Proofs.Monitor.Recover.Finish
import Praxis.Proofs.Monitor.Recover.ProbeGrid
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Differences
import Praxis.Proofs.Monitor.Recover.ProbeBound
import Praxis.Proofs.Monitor.Recover.Sampling
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

theorem recovery_span_of_normal (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : Adversary P0) (m : Msg P0)
    (hnormal : ∀ (w : WorldOut P0) (D : ExprT P0) (ι : Fq P0),
      GoodMark (ppOf ch S) w D ι → ∀ ω : Assign P0,
      ValidCoins (ppOf ch S).qap ω.coins →
      rGrad (ppOf ch S) ω D (markSector D) = sectorScale ω.coins (markSector D) •
        ∑ cl : Cell P0, gamma ω.coins cl •
          ((exprStack D (markSector D) cl).transpose.mulVec ω.coins.1)) :
    (Pr[fun f => ∃ D ι, GoodMark (ppOf ch S) f.w D ι ∧
      gradSpan (ppOf ch S) (recAssign f.w0 f.w1) D (markSector D) ≠ jointSpace (markStack D) |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (Constants.eps_f : ℝ) := by
  classical
  letI : Nonempty {c : Coins P0 // ValidCoins (ppOf ch S).qap c} := ppOf_coins ch S
  have hP : P0.Valid := by constructor <;> decide
  have hKD : P0.K1 + 1 ≤ P0.D := by decide
  have hDq : P0.D < P0.q := by decide
  have heps : 0 ≤ (Constants.eps_f : ℝ) := by norm_num [Constants.eps_f]
  have hden : 0 ≤ (Constants.q : ℝ) - Constants.D := by
    norm_num [Constants.q, Constants.D]
  let ε : ℝ := ((P0.n + 3 : ℕ) : ℝ) / ((Constants.q : ℝ) - Constants.D)
  have hε : 0 ≤ ε := div_nonneg (by positivity) hden
  apply worldFull_recovery_bound (ppOf ch S) m A extF _ heps
  intro w D ι hg
  have hp := Praxis.Proofs.Differences.good_mark_passing ch S hS w D ι hg
  have hsym : ∀ cl, (exprStack D (markSector D) cl).IsSymm := hp.2.2.1
  have hrank : Module.finrank (Fq P0) (jointSpace (exprStack D (markSector D))) ≤ 3 := by
    change Module.finrank (Fq P0) (jointSpace (markStack D)) ≤ dimMax
    exact hp.2.2.2
  have hbound := sampleGradients_bound_of_roots (ppOf ch S) D (markSector D) ε hε
    hsym (hnormal w D ι hg) hrank
  have hdraw := hbound (fun φ hφ => by
    simpa [ε, P0, Params.main] using
      recoveryPolynomial_root_bound (ppOf ch S) hP hKD hDq (exprStack D (markSector D)) φ hφ)
  calc
    _ ≤ 3 * ε := by simpa [markStack] using hdraw
    _ = 3 * ((P0.n + 3 : ℕ) : ℝ) / ((Constants.q : ℝ) - Constants.D) := by simp [ε]; ring
    _ ≤ _ := recovery_degree_le_eps

end Praxis.Proofs.Monitor
