import Praxis.Proofs.Sampling.Locus
import Praxis.Proofs.Sampling.Row.Span
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler

namespace Praxis.Proofs.Sampling

open Praxis.Algebra (Vec dot)

theorem row_heavy (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) (v : Vec (Fq P0) P0.N)
    (hv : v ∈ jointSpace W) :
    gp W ≤ Algebra.maxAtom (fun s : SearchSample P0 => dot v (rField s)) := by
  exact RowSpan.row_heavy_aux W hsym v hv

end Praxis.Proofs.Sampling
