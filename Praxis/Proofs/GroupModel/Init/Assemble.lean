import Praxis.Proofs.GroupModel.Init.Collision
import Praxis.Proofs.GroupModel.Init.Average
import Praxis.Proofs.GroupModel.Init.Continuation
import Praxis.Proofs.GroupModel.Init.Arithmetic
import Praxis.Proofs.Coupling.Half
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Init.PairUnion
import Praxis.Proofs.GroupModel.Init.World
import Praxis.Relation

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

private def InitialCollision (pp : PublicParams P0) (F : FormMatrix P0) (c : Coins P0) : Prop :=
  G1InitialCollision pp c ∨ G2InitialCollision pp (formVec F) c ∨
    GTInitialCollision pp (formVec F) c

private noncomputable def initialAllowance : ENNReal :=
  ((Nat.choose Constants.L1 2 + Nat.choose Constants.L2 2 + 1 : ℕ) : ENNReal) *
    ENNReal.ofReal (Constants.eps_f : ℝ)

private theorem three_event_bound {C : Type} (law : ProbComp C)
    (E1 E2 E3 : C → Prop) (b1 b2 b3 : ENNReal)
    (h1 : Pr[E1 | law] ≤ b1) (h2 : Pr[E2 | law] ≤ b2) (h3 : Pr[E3 | law] ≤ b3) :
    Pr[fun c => E1 c ∨ E2 c ∨ E3 c | law] ≤ b1 + (b2 + b3) := by
  exact (probEvent_or_le law E1 (fun c => E2 c ∨ E3 c)).trans
    (add_le_add h1 ((probEvent_or_le law E2 E3).trans (add_le_add h2 h3)))

private theorem allowance_add (a b : ℕ) (eps : ENNReal) :
    (a : ENNReal) * eps + ((b : ENNReal) * eps + eps) =
      ((a + b + 1 : ℕ) : ENNReal) * eps := by
  push_cast
  ring

private theorem initial_collision_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (F : FormMatrix P0) :
    Pr[fun c => InitialCollision (ppOf ch S) F c.1 | coinLaw (ppOf ch S)] ≤
      initialAllowance := by
  have h1 := g1_initial_collision_bound ch S hS F
  have h2 := g2_initial_collision_of_pairs ch S F (g2_initial_pair_bound ch S hS F)
  have ht := gt_initial_collision_bound ch S hS F
  exact (three_event_bound (coinLaw (ppOf ch S)) _ _ _ _ _ _ h1 h2 ht).trans_eq
    (allowance_add (Nat.choose Constants.L1 2) (Nat.choose Constants.L2 2)
      (ENNReal.ofReal (Constants.eps_f : ℝ)))

private theorem initial_mark_le_collision (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0) (A : Adversary P0) :
    Pr[fun w => firstMark pp w = some .init | worldRun pp m A] ≤
      Pr[fun w => InitialCollision pp w.out.forms w.out.coins | worldRun pp m A] := by
  apply worldRun_init_event_bound pp m A
  intro w hpv hmark
  exact firstMark_init_collision pp w hpv hmark

private theorem initial_world_collision_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (m : Msg P0) (A : Adversary P0) :
    Pr[fun w => InitialCollision (ppOf ch S) w.out.forms w.out.coins |
      worldRun (ppOf ch S) m A] ≤ initialAllowance := by
  exact worldRun_event_bound (ppOf ch S) m A (InitialCollision (ppOf ch S))
    initialAllowance (initial_collision_bound ch S hS)

private theorem initial_run_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (m : Msg P0) (A : Adversary P0) :
    Pr[fun w => firstMark (ppOf ch S) w = some .init | worldRun (ppOf ch S) m A] ≤
      initialAllowance :=
  (initial_mark_le_collision (ppOf ch S) m A).trans
    (initial_world_collision_bound ch S hS m A)

private theorem allowance_ne_top (n : ℕ) (eps : ℝ) :
    (n : ENNReal) * ENNReal.ofReal eps ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

private theorem allowance_toReal (a b : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    (((a + b + 1 : ℕ) : ENNReal) * ENNReal.ofReal eps).toReal =
      ((a : ℝ) + (b : ℝ) + 1) * eps := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal heps]
  simp only [Nat.cast_add, Nat.cast_one]

private theorem initialAllowance_real_le : initialAllowance.toReal ≤ (ledgerInit : ℝ) := by
  have hn : 0 ≤ (Constants.eps_f : ℝ) := by
    exact_mod_cast (show 0 ≤ Constants.eps_f by norm_num [Constants.eps_f])
  exact (allowance_toReal (Nat.choose Constants.L1 2) (Nat.choose Constants.L2 2)
    (Constants.eps_f : ℝ) hn).le.trans initial_ledger_bound

private theorem initial_run_real_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (m : Msg P0) (A : Adversary P0) :
    (Pr[fun w => firstMark (ppOf ch S) w = some .init |
      worldRun (ppOf ch S) m A]).toReal ≤ (ledgerInit : ℝ) := by
  have ht : initialAllowance ≠ ⊤ := allowance_ne_top _ _
  exact (ENNReal.toReal_mono ht (initial_run_bound ch S hS m A)).trans
    initialAllowance_real_le

theorem initial_world_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (m : Msg P0) (A : Adversary P0) :
    (Pr[fun f => firstMark (ppOf ch S) f.w = some .init |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (ledgerInit : ℝ) := by
  have he := Coupling.full_world_marginal (ppOf ch S) m A extF
    (fun w => firstMark (ppOf ch S) w = some .init)
  rw [he]
  exact initial_run_real_bound ch S hS m A

end Praxis.Proofs.GroupModel
