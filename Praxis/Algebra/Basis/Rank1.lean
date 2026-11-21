import Praxis.Algebra.Basis.Definitions
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

namespace Praxis.Algebra.Basis

open Praxis.Algebra.Inverse.Definitions

open scoped BigOperators

theorem height_rank1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι (Fin 1) ℤ) : height B = maxAbs (fun i => B i 0) := by
  unfold height Algebra.VectorInverse.largestMinor maxAbs Combinatorics.UnequalChain.maxNorm
  apply le_antisymm
  · apply Finset.sup_le
    intro r _
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply, id_eq] using
      (Finset.le_sup (f := fun i => (B i 0).natAbs) (Finset.mem_univ (r 0)))
  · apply Finset.sup_le
    intro i _
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply, id_eq] using
      (Finset.le_sup (f := fun r : Fin 1 → ι => (B.submatrix r id).det.natAbs)
        (Finset.mem_univ (fun _ => i)))

theorem rank1_basis_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : IntLat ι 1) :
    (∏ j, (maxAbs (L.basis j : ι → ℤ) : ℝ)) = (J 1 : ℝ) * (L.H : ℝ) := by
  rw [Fin.prod_univ_one]
  have hH : L.H = maxAbs (L.basis 0 : ι → ℤ) := height_rank1 L.matrix
  simp [J, hH]

theorem controlledBasis_rank1 : ControlledBasis 1 := by
  intro ι _ _ L _ _
  exact ⟨L.basis, (rank1_basis_product L).le⟩

end Praxis.Algebra.Basis
