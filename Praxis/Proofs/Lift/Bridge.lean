import Praxis.Proofs.Basic
import Praxis.Lift.Parameters
import Praxis.Algebra.RankMass.ZeroCoord
import Praxis.Algebra.Inverse.SchemeModel
import Praxis.Params
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler
import Praxis.Algebra.Inverse.Definitions

namespace Praxis.Proofs.Lift

open Praxis.Algebra (Vec dot)

theorem lift_bridge (v : Vec (Fq P0) P0.N) (hv0 : v 0 = 0) :
    Algebra.maxAtom (fun s : SearchSample P0 => dot v (rField s)) =
      Algebra.Inverse.Definitions.mass (fun _ : Fin P0.N => P0.g)
        (Algebra.Inverse.Definitions.scalar (fun _ : Fin P0.N => P0.g) (fun i => v i.succ)) := by
  change Algebra.scalarMass P0.g (widths P0) v = _
  rw [Algebra.RankMass.scalarMass_eq_productMass_of_zero (by decide) v hv0]
  exact Algebra.productMass_eq_vitMass (widths P0) (fun i => v i.succ)

end Praxis.Proofs.Lift
