import Praxis.Proofs.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Rank1

open Praxis.Algebra (Vec)

private theorem moment_scaled {F : Type*} [Field F] {N : ℕ} (g : Algebra.Gate F N)
    (x : Vec F N) (c : F) :
    Algebra.MomentGate g (c • Matrix.vecMulVec x x) =
      c * ((∑ j, Algebra.dot (g.left j) x * Algebra.dot (g.right j) x) -
        x 0 * Algebra.dot g.linear x) := by
  simp only [Algebra.MomentGate, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Algebra.dot, mul_sub, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro k _
    ring

theorem honest_cell_passes (S : Relation P0) (x : Vec (Fq P0) P0.N) (hx : IsWitness S x)
    (c : Fq P0) : Passes S (c • Matrix.vecMulVec x x) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  · intro i
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, hx.1, one_mul]
    rcases hx.2.1 i with hi | hi <;> simp [hi]
  · intro t
    rw [moment_scaled, sub_eq_zero.mpr (hx.2.2 t), mul_zero]

end Praxis.Proofs.Rank1
