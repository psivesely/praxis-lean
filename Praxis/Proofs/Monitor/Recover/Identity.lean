import Praxis.Proofs.View.SZ
import Praxis.Constants
import Praxis.Enc
import Praxis.Proofs.Basic
import Praxis.Proofs.View.SZ.Bound
import Praxis.Proofs.View.SZ.Degree
import Praxis.Proofs.View.SZ.Eval
import Praxis.Proofs.View.SZ.Grid
import Praxis.Proofs.View.SZ.Model
import Praxis.Proofs.View.SZ.PolyDegree
import Praxis.Params
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Scheme
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

open Praxis.Proofs.View Praxis.Proofs.View.SZ

theorem recovery_polynomial_zero (pp : PublicParams P0) (S : Relation P0)
    (hD : ValidQAP pp.qap S) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0)
    (h : IdentityAtR pp v r D ι) : differenceP pp v r D ι = 0 := by
  classical
  letI := main_validCoins_nonempty pp.qap
  by_contra hp
  have hd := differenceP_degree_of_e2 pp S hD v r D ι (e2P_degree pp S hD v r)
  have hb := coinLaw_root_bound pp _ hp (P0.q - Constants.D)
    Constants.view_degree_total (by decide) hd
    (sampleSet_card_lower pp.qap Constants.D
      (by rw [SZ.qapIndex_card]; decide) (by decide) (by decide))
  have he : (letI := SampleableType.ofFintype {c : Coins P0 // ValidCoins pp.qap c}
      Pr[fun c => MvPolynomial.eval (coinVar c.1) (differenceP pp v r D ι) = 0 |
        $ᵗ {c : Coins P0 // ValidCoins pp.qap c}]) = 1 := by
    apply probEvent_eq_one
    refine ⟨by simp, ?_⟩
    intro c _
    rw [eval_differenceP pp c.1 v r D ι c.2, h c.1 c.2, sub_self, mul_zero]
  rw [he, ENNReal.toReal_one] at hb
  have hlt : (Constants.view_degree_total : ℝ) / (P0.q - Constants.D : ℕ) < 1 := by
    norm_num [Constants.view_degree_total, Constants.view_degree_d1,
      Constants.view_degree_d2, Constants.D, Constants.q, P0, Params.main,
      Constants.E1, Constants.n, Constants.K1]
  exact (not_le_of_gt hlt) hb

end Praxis.Proofs.Monitor
