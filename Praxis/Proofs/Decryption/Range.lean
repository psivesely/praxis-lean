import Praxis.Proofs.Basic
import Praxis.Proofs.Decryption.Range.Bound
import Praxis.Params
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler

namespace Praxis.Proofs.Decryption

open Praxis.Algebra (Vec dot)

theorem decref_range (x : Vec (Fq P0) P0.N) (hx0 : x 0 = 1)
    (hb : ∀ j : Fin P0.N, x j.succ = 0 ∨ x j.succ = 1) (w : SearchSample P0) :
    |rOf (toInt x) (rInt w) - cX (toInt x)| ≤ (P0.tBound : ℤ) ∧
      dot x (rField w) = ((rOf (toInt x) (rInt w) : ℤ) : Fq P0) := by
  refine ⟨?_, ?_⟩
  · exact Bound.range_general P0 (by decide) (by decide) (by decide) (by decide) x hx0 hb w
  · unfold dot rOf
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [toInt, rField, rInt, Algebra.centeredF]

end Praxis.Proofs.Decryption
