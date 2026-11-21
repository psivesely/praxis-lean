import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Lift.Algebra.Reg.Return2
import Praxis.Lift.Algebra.Trans.Definitions
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Transition2

open Praxis.Algebra Praxis.Algebra.Reg

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

theorem newHeight_eq {n r q : ℕ} (T : Algebra.Trans.TransitionInput n r q)
    (L : IntLat (Fin (n + 1)) q) (hnew : T.normal = L.matrix) :
    T.newHeight = L.H := by
  show height T.normal = height L.matrix
  rw [hnew]

theorem oldHeight_eq {n r q : ℕ} (T : Algebra.Trans.TransitionInput n r q)
    (L : IntLat (Fin n) r) (hold : T.old = L.matrix) :
    T.oldHeight = L.H := by
  show height T.old = height L.matrix
  rw [hold]

theorem oldMass_eq {n r q : ℕ} (T : Algebra.Trans.TransitionInput n r q)
    (L : IntLat (Fin n) r) (hold : T.old = L.matrix) :
    T.oldMass = L.mZ T.oldGrids := by
  show mass T.oldGrids (imageZ T.oldGrids T.old) =
    mass T.oldGrids (imageZ T.oldGrids L.matrix)
  rw [hold]

theorem transition32_raw (P : VITParameters)
    (hT : Algebra.Trans.Transition32 P) (hPlanar : Algebra.Point.PlanarCount)
    (hSection : Algebra.Point.SectionCount3) (hTrim : Algebra.Trim.TrimForIntLat)
    {n : ℕ} (T : Algebra.Trans.TransitionInput n 3 2)
    (hData : Algebra.Trans.TransitionData 3 2 P.toVITData T)
    (L3 : IntLat (Fin n) 3) (L2 : IntLat (Fin (n + 1)) 2)
    (hold : T.old = L3.matrix) (hnew : T.normal = L2.matrix) :
    T.density * (L2.H : ℝ) ≤
      P.D * (P.g : ℝ) * (L3.H : ℝ) * L3.mZ T.oldGrids := by
  have h := hT hPlanar hSection hTrim n T hData
  rw [newHeight_eq T L2 hnew, oldHeight_eq T L3 hold, oldMass_eq T L3 hold] at h
  exact h

end Algebra.Reg.Transition2

end Praxis.Lift
