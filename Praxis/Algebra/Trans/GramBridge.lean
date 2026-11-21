import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.TrimAnalysis.GridTrim

open scoped BigOperators

namespace Praxis.Algebra.Trans

theorem gridSigma_sq {ι : Type*} (G : ι → ℕ) (i : ι) :
    ((G i : ℝ) / Real.sqrt 12) ^ 2 = (G i : ℝ) ^ 2 / 12 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]

theorem weightedGram_gridSigma {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (G : ι → ℕ) (B : Matrix ι (Fin d) ℝ) :
    weightedGram B (fun i => (G i : ℝ) / Real.sqrt 12) = Analysis.gridCovariance G B := by
  ext j k
  simp only [weightedGram, Analysis.gridCovariance, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    gridSigma_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Praxis.Algebra.Trans
