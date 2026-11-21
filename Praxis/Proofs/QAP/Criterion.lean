import Praxis.Proofs.QAP.Criterion.Helpers
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.QAP

open Praxis.Algebra (Mat)

theorem qap_criterion (S : Relation P0) (hS : InShape P0 S) (Dm : QAPData P0)
    (hD : ValidQAP Dm S) (W : Mat (Fq P0) P0.N) (hW : W.IsSymm) :
    Passes S W ↔ QAPCriterion Dm W := by
  constructor
  · rintro ⟨_, hb, hg⟩
    exact criterion_forward (by decide +kernel) (by decide +kernel) hS hD W hb hg
  · intro hc
    obtain ⟨hb, hg⟩ := criterion_backward hS hD W hc
    exact ⟨hW, hb, hg⟩

end Praxis.Proofs.QAP
