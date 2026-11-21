import Praxis.Proofs.Classification.Gates
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Bool
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Classification

open Praxis.Algebra (Vec)

theorem classification (A : FormMatrix P0) (S : Relation P0) (hS : InShape P0 S) (W : Stack P0)
    (hW : PassingStack S (formVec A) W)
    (hdim : Module.finrank (Fq P0) (jointSpace W) ≤ dimMax)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin (formVec A)) = ⊥) :
    ∃ (xs : Finset (Vec (Fq P0) P0.N)) (ρ : Vec (Fq P0) P0.N → Fq P0),
      (∀ x ∈ xs, x ∈ jointSpace W ∧ IsWitness S x) ∧
      W = ∑ x ∈ xs, ρ x • honestStack (formVec A) x := by
  obtain ⟨xs, ρ, hxs, hsum⟩ := classification_boolean A W
    (fun c => (hW.1 c).1) (fun c => (hW.1 c).2.1) hW.2 hdim hinj
  exact classification_gates A S hS W xs ρ hxs hsum (fun c => (hW.1 c).2.2) hdim hinj

end Praxis.Proofs.Classification
