import Praxis.Proofs.Classification.Moore
import Praxis.Proofs.ZeroCoordinate
import Praxis.Proofs.Rank1
import Praxis.Proofs.Ties.Origin
import Praxis.Proofs.Classification.BooleanCore
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Classification

open Praxis.Algebra (Vec)

theorem classification_boolean (A : FormMatrix P0) (W : Stack P0) (hsym : ∀ c, (W c).IsSymm)
    (hbool : ∀ c (j : Fin P0.N), W c j.succ j.succ = W c 0 j.succ) (hties : Ties (formVec A) W)
    (hdim : Module.finrank (Fq P0) (jointSpace W) ≤ dimMax)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin (formVec A)) = ⊥) :
    ∃ (xs : Finset (Vec (Fq P0) P0.N)) (ρ : Vec (Fq P0) P0.N → Fq P0),
      (∀ x ∈ xs, x ∈ jointSpace W ∧ x 0 = 1 ∧ ∀ j : Fin P0.N, x j.succ = 0 ∨ x j.succ = 1) ∧
      W = ∑ x ∈ xs, ρ x • honestStack (formVec A) x := by
  exact boolean_core (formVec A) W hsym hbool hties hdim hinj

end Praxis.Proofs.Classification
