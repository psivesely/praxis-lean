import Praxis.Algebra.Trans.Definitions
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

open Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

namespace Praxis.Lift

namespace Algebra.Trans

open Praxis.Algebra.Trans hiding Transition32 Transition21 Transition31

def Transition32 (P : VITParameters) : Prop :=
  PlanarCount → SectionCount3 → Algebra.Trim.TrimForIntLat →
  ∀ n (T : TransitionInput n 3 2), TransitionData 3 2 P.toVITData T →
    T.density * T.newHeight ≤ P.D * P.g * T.oldHeight * T.oldMass

def Transition21 (P : VITParameters) : Prop :=
  PlanarCount → SectionCount3 → Algebra.Trim.TrimForIntLat →
  ∀ n (T : TransitionInput n 2 1), TransitionData 2 1 P.toVITData T →
    T.density * T.newHeight ≤ P.D * P.g * T.oldHeight * T.oldMass

def Transition31 (P : VITParameters) : Prop :=
  PlanarCount → SectionCount3 → Algebra.Trim.TrimForIntLat →
  ∀ n (T : TransitionInput n 3 1), TransitionData 3 1 P.toVITData T →
    T.density * T.newHeight ≤ P.E * (P.g : ℝ)^2 * T.oldHeight * T.oldMass

end Algebra.Trans

end Praxis.Lift
