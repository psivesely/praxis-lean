import Praxis.Proofs.View.ForwardPassing
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.QAP.Criterion
import Praxis.Proofs.View.ForwardAlgebra
import Praxis.Proofs.View.ForwardCells
import Praxis.Proofs.View.ForwardEvaluation
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Proofs.View.ForwardLines
import Praxis.Proofs.View.ForwardMain
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat)

lemma forward_analysis (pp : PublicParams P0) (S : Relation P0) (hS : InShape P0 S)
    (hD : ValidQAP pp.qap S) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0) (h : IdentityAtR pp v r D ι) (σ : Sector) :
    (∀ cl, Passes S (aC (expandTot D) σ cl)) ∧
    (∀ cl, Matrix.mulVec (aC (expandTot D) σ cl) r = -sC (expandTot D) σ cl) ∧
    (∀ cl, IsKeyCell cl → aC (expandTot D) σ cl 0 0 = (if σ = .plain then ι else -D.2)) ∧
    (∀ c, ValidCoins pp.qap c → maskTerm v (expandTot D) σ c = 0) := by
  have hm := mainValue_identity pp v r D ι h σ
  have hd := matrix_coeffs_equal pp S hD v r (expandTot D) σ (if σ = .plain then ι else -D.2) hm
  have hs := split_cell_mask pp v r (expandTot D) σ (if σ = .plain then ι else -D.2) (by decide) hd hm
  have hcell := cell_evaluations pp r (expandTot D) σ (if σ = .plain then ι else -D.2)
    (fun c hc => (hs c hc).1)
  have hcrit := fun (W : Mat (Fq P0) P0.N) (hW : W.IsSymm) => QAP.qap_criterion S hS pp.qap hD W hW
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cl
    exact (cells_pass pp S hD hcrit qapIndex_card (by decide) (by decide) (by decide) (by decide) r (expandTot D) σ _ hcell cl).1
  · intro cl
    exact (cell_symm_search pp S hD qapIndex_card (by decide) (by decide) r (expandTot D) σ _ hcell cl).2
  · intro cl
    exact (cells_pass pp S hD hcrit qapIndex_card (by decide) (by decide) (by decide) (by decide) r (expandTot D) σ _ hcell cl).2
  · intro c hc
    exact (hs c hc).2

end Praxis.Proofs.View
