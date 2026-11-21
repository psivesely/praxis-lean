import Praxis.Proofs.Basic
import Praxis.Packing.Coefficients
import Praxis.Proofs.Pack.Kernel.Main
import Praxis.Forms
import Praxis.Proofs.Pack.Kernel.Ring
import Praxis.Params
import Praxis.Reduction
import Praxis.Scheme
import Praxis.Setting
import Praxis.Algebra.Definitions.Forms
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Pack

open Praxis.Algebra (Vec dot)

theorem packCore_eq (w : Vec ℤ P0.N) : packCore (P := P0) w = Praxis.Packing.packCoeffs w := by
  rfl

theorem pack_kernel (F : FormMatrix P0) (w : Vec ℤ P0.N) (hw0 : w 0 = 0)
    (hker : ∀ e : Fin P0.n, P0.d ≤ e.val → dot (formVec F e) (Algebra.castVec w) = 0) :
    Algebra.moduleMul (msisRing P0 main_d_ne_zero) (chalOf main_d_ne_zero F) (packCore w) = 0 := by
  funext ρ
  rw [moduleMul_chalOf main_d_ne_zero]
  have hn : P0.n = P0.d * (P0.rows + 1) := by decide +kernel
  have h := slot_sum_zero hn F w hw0 hker ρ
  have hslot : ∀ j, slotPoly (Algebra.castVec (p := P0.q) w) j =
      fun t => ((packCore (P := P0) w j t : ℤ) : Fq P0) := by
    intro j
    funext t
    rw [Praxis.Packing.slot_coefficients]
    rfl
  simp only [hslot] at h
  rw [h, toRing_zero]
  rfl

end Praxis.Proofs.Pack
