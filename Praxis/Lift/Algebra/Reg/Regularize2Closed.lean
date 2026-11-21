import Praxis.Lift.Algebra.Trans.ChartTransitions
import Praxis.Lift.Algebra.Reg.Regularize2Assemble
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Closed2

open Praxis.Algebra Praxis.Algebra.Reg

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

theorem regularize2 (P : VITParameters) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ℕ) (L : IntLat ι 2) : Regularize2 P G L :=
  Algebra.Reg.Assemble2.regularize2 P (Algebra.Trans.ChartTransitions.transition32_compat P) G L

end Algebra.Reg.Closed2

end Praxis.Lift
