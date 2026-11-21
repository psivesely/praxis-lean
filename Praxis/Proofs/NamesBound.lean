import Praxis.Proofs.NamesPreparation
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Cap
import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesInitial
import Praxis.Proofs.NamesMonitor
import Praxis.Proofs.NamesProbability
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Names

open OracleComp OracleSpec

open scoped ENNReal

variable {P : Params}

theorem worldRun_cap_eq [Fact (Nat.Prime P.q)] [Nonempty (Fq P ↪ Label P)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (A : Adversary P) (Q QH : ℕ) (hA : InClass A Q QH) :
    worldRun pp m (cap Q QH A) = worldRun pp m A := by
  unfold worldRun
  apply bind_congr
  intro σ
  rw [runWith_cap_eq σ A pp m Q QH]
  intro z hz k
  cases k
  · exact hA.group σ pp m z hz
  · exact hA.hf σ pp m z hz
  · exact hA.kdf σ pp m z hz

namespace Game

theorem world_prepared [Fact (Nat.Prime P.q)] (src : LabelEncoding P)
    (σ : Fq P ↪ Label P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P)
    (A : Adversary P) (Q QH : ℕ) :
    (fun r => (⟨withGT src σ, r.1.1, r.1.2, r.2⟩ : WorldOut P)) <$>
        runWith (withGT src σ) (cap Q QH A) (encGame (withGT src σ) pp m) OracleState.empty =
      prepare pp >>= fun d =>
        restoredWorld src σ (kappa pp d.coins.1) d.pad <$>
          simulateQ (plain σ)
            (program src pp d.forms d.coins.1 (d.header m) d.pad d.hf A Q QH) := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [runWith, StateT.run_bind, StateT.run_pure]
  rw [encGame_prepared]
  simp only [bind_map_left, map_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro d
  rw [program_plain]
  simp [fixedOut, withGT]

def sources (σ1 σ2 : Fq P ↪ Label P) : LabelEncoding P
  | .g₁ => σ1
  | .g₂ => σ2
  | .gₜ => σ1

end Game

set_option maxRecDepth 2000 in
theorem capped_probability (ch : AdmissibleChoice P0) (S : Relation P0)
    (m : Msg P0) (A : Adversary P0) (Q QH : ℕ)
    (hQ : Q < Constants.T) (hH : QH ≤ Constants.T) :
    Pr[fun w => firstMark (ppOf ch S) w = some .guessName |
      worldRun (ppOf ch S) m (cap Q QH A)] ≤
      (observerBudget Q QH : ℝ≥0∞)^2 * (Constants.N_free : ℝ≥0∞)⁻¹^2 := by
  classical
  simp only [worldRun, sampleEncoding, bind_assoc, pure_bind]
  apply probEvent_bind_le_of_forall_le
  intro σ1 _
  apply probEvent_bind_le_of_forall_le
  intro σ2 _
  simp only [bind_pure_comp]
  change Pr[fun w => firstMark (ppOf ch S) w = some .guessName |
    ($ᵗ (Fq P0 ↪ Label P0)) >>= fun σ =>
      (fun r => (⟨Game.withGT (Game.sources σ1 σ2) σ, r.1.1, r.1.2, r.2⟩ : WorldOut P0)) <$>
        runWith (Game.withGT (Game.sources σ1 σ2) σ) (cap Q QH A)
          (encGame (Game.withGT (Game.sources σ1 σ2) σ) (ppOf ch S) m) OracleState.empty] ≤ _
  simp_rw [Game.world_prepared]
  rw [probEvent_bind_bind_swap]
  apply probEvent_bind_le_of_forall_le
  intro d _
  exact Game.program_probability (Game.sources σ1 σ2) (ppOf ch S) d.forms d.coins.1
    (kappa_ne_neg ch S d.coins.1 d.coins.2) (d.header m) d.pad d.hf A Q QH Constants.N_free
    (by norm_num [Constants.N_free]) (observerBudget_reserve Q QH hQ hH)

theorem gg_name_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (Q QH : ℕ) (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => firstMark (ppOf ch S) f.w = some .guessName |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (ledgerName : ℝ) := by
  rw [worldFull_event (ppOf ch S) m A extF (fun w => firstMark (ppOf ch S) w = some .guessName),
    ← worldRun_cap_eq (ppOf ch S) m A Q QH hA]
  exact (ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top, Constants.N_free])
    (capped_probability ch S m A Q QH hA.Q_lt hA.QH_le)).trans
      (observerBudget_ledger Q QH hA.Q_lt hA.QH_le)

end Praxis.Proofs.Names
