import Praxis.Proofs.Sampling.Locus
import Praxis.Bounds.Rank
import Praxis.Algebra.RankMass.Pushforward
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler
import Praxis.Algebra.Definitions.Stack

namespace Praxis.Proofs.Sampling.RowSpan

open Praxis.Bounds.Rank

theorem jointSpace_le (W : Praxis.Stack Praxis.Params.main) (hsym : ∀ c, (W c).IsSymm) :
    Praxis.Proofs.jointSpace W ≤ Algebra.stackSpace (stackAsBase W) := by
  unfold Praxis.Proofs.jointSpace
  apply iSup_le
  intro c
  rintro y ⟨u, rfl⟩
  have hrow : ∀ j, (W c j) ∈ Algebra.stackSpace (stackAsBase W) := by
    intro j
    apply Submodule.subset_span
    refine ⟨(cellEquiv _ c, j), ?_⟩
    funext i
    simp [Algebra.stackRows, stackAsBase, cellEquiv]
  have : (W c).mulVecLin u = ∑ j, u j • W c j := by
    funext i
    have h : ∀ j, W c i j = W c j i := fun j => by
      have := congrFun (congrFun (hsym c).eq j) i
      simpa [Matrix.transpose_apply] using this
    simp [Matrix.mulVec, dotProduct, h, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hrow j)

theorem row_heavy_aux (W : Praxis.Stack Praxis.Params.main) (hsym : ∀ c, (W c).IsSymm)
    (v : Algebra.Vec (Praxis.Fq Praxis.Params.main) Praxis.Params.main.N)
    (hv : v ∈ Praxis.Proofs.jointSpace W) :
    Praxis.gp W ≤ Algebra.maxAtom (fun s : Praxis.SearchSample Praxis.Params.main => Algebra.dot v (Praxis.rField s)) := by
  rw [gp_eq_stackMass]
  exact Algebra.RankMass.maxAtom_readout_le_scalar
    (fun w : Praxis.SearchSample Praxis.Params.main => (Praxis.rField w : Algebra.Vec _ _))
    (Algebra.stackRows (stackAsBase W)) v (jointSpace_le W hsym hv)

end Praxis.Proofs.Sampling.RowSpan
