import Praxis.Proofs.Monitor.Stop.Main
import Praxis.Proofs.Monitor.Stop.Roots
import Praxis.Constants
import Praxis.Enc
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Stop.Coins
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Proofs.Monitor.Stop.Numerator
import Praxis.Proofs.Monitor.Stop.Sampling
import Praxis.Params
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

open Classical

theorem main_root_bound (pp : PublicParams P0) [SampleableType (AssignSample pp)]
    [Nonempty (ValidCoin pp)] (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N)
    (D : ExprT P0) (ι : Fq P0)
    (hA : ∀ j, (pp.qap.A j).natDegree < P0.D) (hB : ∀ j, (pp.qap.B j).natDegree < P0.D)
    (hL : pp.qap.Lrho.natDegree < P0.D)
    (hZc : ∀ c, (pp.qap.zCell c).natDegree ≤ P0.D) (hZ0 : pp.qap.Z0.natDegree ≤ P0.N + 2)
    (h : ¬ ∀ ω, ValidCoins pp.qap ω.coins → valT pp v ω D = ι * kappa pp ω.coins) :
    Pr[fun z : AssignSample pp =>
        valT pp v (sampleToAssign z) D = ι * kappa pp (sampleToAssign z).coins |
      $ᵗ (AssignSample pp)] ≤
      (Constants.eps_f_numerator : ENNReal) / ((P0.q - P0.D : ℕ) : ENNReal) := by
  have hne := comparisonPoly_ne_zero pp v D ι h
  have hm : 0 < P0.q - P0.D := by
    norm_num [P0, Params.main, Constants.q, Constants.D]
  have hroot := assign_root_prob pp (P0.q - P0.D) hm (main_scalarSet_card_lower pp.qap)
    (comparisonPoly pp v D ι) hne
  refine le_trans (probEvent_mono ?_) (hroot.trans ?_)
  · intro z _ hz
    show MvPolynomial.eval (assignmentCoords (sampleToAssign z)) (comparisonPoly pp v D ι) = 0
    rw [eval_comparisonPoly pp v (sampleToAssign z) z.1.2 D ι, hz, sub_self, mul_zero]
  · exact ENNReal.div_le_div_right
      (by exact_mod_cast main_comparison_degree pp v D ι hA hB hL hZc hZ0) _

end Praxis.Proofs.Monitor
