import Praxis.Scheme
import Praxis.Ledger
import Praxis.Proofs.Assembly.Correctness
import Praxis.Proofs.Assembly.Extraction
import Praxis.Proofs.Basic
import Praxis.Constants
import Praxis.Domain
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Coupling.Half
import Praxis.Proofs.Decryption.Correct
import Praxis.Proofs.Differences
import Praxis.Proofs.GroupModel.Cmp
import Praxis.Proofs.GroupModel.Init
import Praxis.Proofs.Injectivity.Inj
import Praxis.Proofs.Injectivity.Sound
import Praxis.Proofs.IndexSelection.Total
import Praxis.Proofs.Ledger.Delta
import Praxis.Proofs.Ledger.Split
import Praxis.Proofs.Monitor.Recover
import Praxis.Proofs.Monitor.Stop
import Praxis.Proofs.MonitorBounds
import Praxis.Proofs.Names
import Praxis.Proofs.Reduction.Complete
import Praxis.Proofs.Reduction.Law
import Praxis.Proofs.Reduction.Sound
import Praxis.Proofs.Query.Marked
import Praxis.Proofs.Unit.WKey
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open OracleComp OracleSpec

open Praxis.Algebra (Vec)

namespace Scheme

variable (sch : Scheme)

def Correctness : Prop :=
  ∀ S : Relation sch.params, InShape sch.params S →
  ∀ x : Vec (Fq sch.params) sch.params.N, IsWitness S x →
  ∀ m : Msg sch.params,
    (Pr[fun out => out ≠ some m | sch.decExp S m x]).toReal ≤ 2 / (sch.params.q : ℝ)

def Extraction : Prop :=
  ∀ S : Relation sch.params, InShape sch.params S →
  ∀ (Q QH : ℕ) (A : Adversary sch.params), InClass A Q QH →
  ∀ m0 m1 : Msg sch.params,

    (∀ input ∈ support (sch.extractInputs S m0 m1 A),
      WithinUnits (sch.extractor (sparseOf S) input.1 input.2)
          (simBudget Q * (Constants.running_time_extractor_per_w +
              Constants.running_time_extractor_per_w_per_S * size S) +
            Constants.running_time_extractor_setup) ∧
        SmallSamples (sch.extractor (sparseOf S) input.1 input.2)) ∧

    ((Pr[= true | sch.extractExp S m0 m1 A]).toReal ≤
        1 / 2 + 1 / 2 * ((ledgerE (simBudget Q) : ℝ) + sch.succ S m0 A + sch.succ S m1 A) ∧
      (ledgerE (simBudget Q) : ℝ) ≤
        min (((Q : ℝ) + 1) / (Constants.T : ℝ)) (1 - (Constants.ledger_delta : ℝ))) ∧

    ∀ (pub : PubView sch.params) (tr : List (TrOp sch.params)) (x : Vec (Fq sch.params) sch.params.N),
      some x ∈ support (runUnits (sch.extractor (sparseOf S) pub tr)) → IsWitness S x

end Scheme

theorem correctness (ch : AdmissibleChoice Params.main) : (scheme ch).Correctness :=
  Praxis.Proofs.Assembly.correctness_of_lemmas ch
    @Praxis.Proofs.Unit.wkey_vanish
    @Praxis.Proofs.Decryption.decref_correct

theorem extraction (ch : AdmissibleChoice Params.main) : (scheme ch).Extraction :=
  Praxis.Proofs.Assembly.extraction_of_lemmas ch
    @Praxis.Proofs.IndexSelection.jset_total
    @Praxis.Proofs.Coupling.couple_half
    @Praxis.Proofs.Query.target_marked
    @Praxis.Proofs.GroupModel.gg_init
    @Praxis.Proofs.GroupModel.gg_cmp
    @Praxis.Proofs.Names.gg_name
    @Praxis.Proofs.Differences.good_mark_passing
    @Praxis.Proofs.Monitor.monitor_at_mark
    @Praxis.Proofs.Monitor.recovery_span
    @Praxis.Proofs.Reduction.red_complete
    @Praxis.Proofs.Reduction.red_sound
    @Praxis.Proofs.Reduction.red_law
    @Praxis.Proofs.Injectivity.jse_inj
    @Praxis.Proofs.Ledger.ledger_split
    @Praxis.Proofs.MonitorBounds.monfit
    @Praxis.Proofs.Ledger.ledger_min
    @Praxis.Proofs.Injectivity.jse_sound

end Praxis
