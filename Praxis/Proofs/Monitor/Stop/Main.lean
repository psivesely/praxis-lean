import Praxis.Proofs.Monitor.Stop.RightDegree
import Praxis.Proofs.Monitor.Stop.NumDegree
import Praxis.Constants
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Stop.Degree
import Praxis.Proofs.Monitor.Stop.LeftDegree
import Praxis.Proofs.Monitor.Stop.Numerator
import Praxis.Params
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open MvPolynomial

noncomputable section

theorem main_leg_lt (l : Leg P0) : legExp l < P0.n := by
  obtain ⟨kind, k⟩ := l
  have hk : k.val < 12 := by
    have := k.2
    simpa [P0, Params.main, Constants.K2] using this
  cases kind <;> simp only [legExp, LegKind.base] <;>
    simp only [P0, Params.main, Constants.K1, Constants.n] <;> omega

theorem main_cell_lt (c : Cell P0) : cellExp c < P0.n := by
  obtain ⟨k1, kind, k⟩ := c
  have hk : k.val < 12 := by
    have := k.2
    simpa [P0, Params.main, Constants.K2] using this
  have hk1 : k1.val < 192 := by
    have := k1.2
    simpa [P0, Params.main, Constants.K1] using this
  cases kind <;> simp only [cellExp, legExp, LegKind.base] <;>
    simp only [P0, Params.main, Constants.K1, Constants.n] <;> omega

theorem main_comparison_degree (pp : PublicParams P0) (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N)
    (D : ExprT P0) (ι : Fq P0)
    (hA : ∀ j, (pp.qap.A j).natDegree < P0.D) (hB : ∀ j, (pp.qap.B j).natDegree < P0.D)
    (hL : pp.qap.Lrho.natDegree < P0.D)
    (hZc : ∀ c, (pp.qap.zCell c).natDegree ≤ P0.D) (hZ0 : pp.qap.Z0.natDegree ≤ P0.N + 2) :
    (comparisonPoly pp v D ι).totalDegree ≤ Constants.eps_f_numerator := by
  have hnum : P0.D + 2 * P0.K1 + (P0.D + P0.E1 * (P0.Mq - 1) + P0.n + 7) ≤
      Constants.eps_f_numerator := by
    norm_num [P0, Params.main, Constants.D, Constants.K1, Constants.E1, Constants.M_q,
      Constants.n, Constants.eps_f_numerator]
  refine le_trans ?_ hnum
  apply degree_comparisonPoly_of_leaf_bounds pp v D ι (P0.D + 2 * P0.K1)
    (P0.D + P0.E1 * (P0.Mq - 1) + P0.n + 7) (P0.D + 7)
  · intro a
    apply degree_leftPoly_le pp hA
    · norm_num [P0, Params.main, Constants.D]
    · norm_num [P0, Params.main, Constants.D, Constants.K1, Constants.E1]
    · norm_num [P0, Params.main, Constants.D, Constants.K1, Constants.U, Constants.E1p]
  · intro b
    apply degree_rightPoly_le pp v
    · norm_num [P0, Params.main, Constants.D]
    · norm_num [P0, Params.main, Constants.D, Constants.n]
    · exact main_leg_lt
    · exact main_cell_lt
    · exact hA
    · exact hB
    · exact hZc
    · exact hZ0
    · norm_num [P0, Params.main, Constants.D, Constants.N, Constants.U, Constants.E1p,
        Constants.W_r, Constants.E1, Constants.M_q]
  · exact degree_keyPoly pp hL
  · norm_num [P0, Params.main, Constants.D, Constants.K1, Constants.E1, Constants.M_q,
      Constants.n]

end

end Praxis.Proofs.Monitor
