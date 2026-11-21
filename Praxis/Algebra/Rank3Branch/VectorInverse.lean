import Praxis.Algebra.Rank3Branch.RankThreeBranch

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.RankThree

open Finset Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

theorem tail_ne_zero {p N : ℕ} [Fact p.Prime]
    {z : Fin (N + 1) → ZMod p} (hz : z ≠ 0) (hz0 : z 0 = 0) :
    (fun i : Fin N => z i.succ) ≠ 0 := by
  intro h
  apply hz
  funext i
  refine Fin.cases hz0 (fun j => ?_) i
  exact congrFun h j

end Praxis.Algebra.RankThree
