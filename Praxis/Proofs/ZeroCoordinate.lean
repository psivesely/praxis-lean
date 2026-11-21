import Praxis.Proofs.Basic
import Praxis.Forms
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.ZeroCoordinate

open Praxis.Algebra (Vec)

theorem kernel_zero_coordinate (A : FormMatrix P0) (z : Vec (Fq P0) P0.N) (hz : zLin (formVec A) z = 0) :
    z 0 = 0 := by
  have h := congrFun hz (⟨0, by decide⟩ : Fin P0.n)
  have hd : P0.d = 0 ∨ 0 < P0.d := Nat.eq_zero_or_pos _
  simpa [hd, zLin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, formVec, phi,
    Pi.single_apply] using h

end Praxis.Proofs.ZeroCoordinate
