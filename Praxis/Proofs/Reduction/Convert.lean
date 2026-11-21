import Praxis.Proofs.Basic
import Praxis.Algebra.Definitions.Forms
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Stmt.Short

namespace Praxis.Proofs.Reduction

open Praxis.Algebra (Vec)

theorem convert_sound (v : Vec (Fq P0) P0.N) (z : Vec ℤ P0.N) (h : convertLIFT v = some z) :
    Algebra.castVec (p := P0.q) z ≠ 0 ∧ (∃ a : Fq P0, a ≠ 0 ∧ ∀ i, (z i : Fq P0) = a * v i) ∧
      ∀ i, |z i| ≤ (P0.eta : ℤ) := by
  change Algebra.Short.bruteForce P0.q P0.eta v = some z at h
  unfold Algebra.Short.bruteForce at h
  have hv : Algebra.Short.VerifiedMultiple P0.q P0.eta v z := by
    simpa using List.find?_some h
  exact hv

end Praxis.Proofs.Reduction
