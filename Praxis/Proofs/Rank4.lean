import Praxis.Proofs.Basic
import Praxis.Bounds.Rank
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Stack

namespace Praxis.Proofs.Rank4

theorem rank_four (W : Stack P0) (hr : lightRank ≤ Algebra.stackRank (Praxis.Bounds.Rank.stackAsBase W)) :
    Light W :=
  Praxis.Bounds.Rank.rank_four_bound W hr

theorem finrank_jointSpace (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) :
    Module.finrank (Fq P0) (jointSpace W) = Algebra.stackRank (Praxis.Bounds.Rank.stackAsBase W) ∧
      (Heavy W → Module.finrank (Fq P0) (jointSpace W) ≤ dimMax) := by
  classical
  have hspace : jointSpace W = Algebra.stackSpace (Praxis.Bounds.Rank.stackAsBase W) := by
    apply le_antisymm
    · unfold jointSpace
      apply iSup_le
      intro c
      rw [Matrix.range_mulVecLin]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      refine ⟨(Praxis.Bounds.Rank.cellEquiv P0 c, i), ?_⟩
      funext j
      change W ((Praxis.Bounds.Rank.cellEquiv P0).symm (Praxis.Bounds.Rank.cellEquiv P0 c)) i j = W c j i
      rw [Equiv.symm_apply_apply]
      exact (hsym c).apply j i
    · unfold Algebra.stackSpace
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨c, i⟩, rfl⟩
      let c' := (Praxis.Bounds.Rank.cellEquiv P0).symm c
      have hcol : Algebra.stackRows (Praxis.Bounds.Rank.stackAsBase W) (c, i) = (W c').col i := by
        funext j
        exact (hsym c').apply j i
      rw [hcol]
      apply (le_iSup (fun c => LinearMap.range (W c).mulVecLin) c')
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨i, rfl⟩
  have hrank : Module.finrank (Fq P0) (jointSpace W) =
      Algebra.stackRank (Praxis.Bounds.Rank.stackAsBase W) := by
    rw [hspace, Algebra.stackRank]
  refine ⟨hrank, ?_⟩
  intro hh
  rw [hrank]
  by_contra h
  have hr : lightRank ≤ Algebra.stackRank (Praxis.Bounds.Rank.stackAsBase W) := by
    dsimp [lightRank, dimMax] at *
    omega
  exact hh (rank_four W hr)

end Praxis.Proofs.Rank4
