import Praxis.Proofs.Ties.OriginAux
import Praxis.KummerIrr
import Praxis.Dec
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Ties

open Praxis.Algebra (Vec dot)

theorem mask_origin (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (c : Coins P0)
    (hε : coin c .eps ≠ 0) :
    ∑ cl : Cell P0, piAt c cl.1.val * dot c.1 ((W cl).mulVec (legMask v c cl.2)) =
      coin c .pi * ∑ i : Fin (P0.N + 1), c.1 i *
        ((∑ s : TieIdx, cTie c s *
            ∑ t ∈ Finset.range (2 * P0.n - 1), coin c .u ^ t * tiePoly v W s t i) +
          ∑ g : CrossIdx, crossVal c g *
            ∑ t ∈ Finset.range (2 * P0.n - 1), coin c .u ^ t * crossPoly v W g t i) := by
  exact mask_origin_gen v W c (by rw [P0_n]; norm_num) beta_pow_m
    uCell_exp_lt (fun cl h => (vCell_exp cl h).1) hε

end Praxis.Proofs.Ties
