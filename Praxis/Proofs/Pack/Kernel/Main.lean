import Praxis.Proofs.Pack.Kernel.Lin
import Praxis.Proofs.Pack.Kernel.Ring
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Forms
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Pack

open Praxis.Algebra (Vec dot)

section Main

variable {P : Params} [Fact (1 < P.q)] (hd : P.d ≠ 0)

theorem moduleMul_chalOf (F : FormMatrix P) (v : Algebra.CoeffVec P.d P.cols) (ρ : Fin P.rows) :
    Algebra.moduleMul (msisRing P hd) (chalOf hd F) v ρ =
      toRing hd (∑ j : Fin P.cols, rqMul (F (ρ, some j)) (fun t => ((v j t : ℤ) : Fq P))) := by
  unfold Algebra.moduleMul
  rw [toRing_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toRing_mul, embed_eq]
  congr 1
  unfold chalOf
  rw [coords_symm_eq]
  congr 1

theorem slot_sum_zero (hn : P.n = P.d * (P.rows + 1)) (F : FormMatrix P) (w : Vec ℤ P.N)
    (hw0 : w 0 = 0)
    (hker : ∀ e : Fin P.n, P.d ≤ e.val → dot (formVec F e) (Algebra.castVec w) = 0)
    (ρ : Fin P.rows) :
    ∑ j : Fin P.cols, rqMul (F (ρ, some j)) (slotPoly (Algebra.castVec (p := P.q) w) j) = 0 := by
  funext i
  have hdpos : 0 < P.d := Fin.pos i
  have hlt : (ρ.val + 1) * P.d + i.val < P.n := by
    rw [hn]
    have : ρ.val + 1 < P.rows + 1 := by omega
    have h2 := i.isLt
    nlinarith [Nat.mul_le_mul_right P.d (show ρ.val + 2 ≤ P.rows + 1 by omega)]
  have h := hker ⟨(ρ.val + 1) * P.d + i.val, hlt⟩ (by
    show P.d ≤ (ρ.val + 1) * P.d + i.val
    nlinarith)
  rw [← phi_eq_dot] at h
  have hdiv : ((ρ.val + 1) * P.d + i.val) / P.d = ρ.val + 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hdpos, Nat.div_eq_of_lt i.isLt, zero_add]
  have hmod : ((ρ.val + 1) * P.d + i.val) % P.d = i.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  have hx0 : (Algebra.castVec (p := P.q) w) 0 = 0 := by simp [Algebra.castVec, hw0]
  unfold phi at h
  simp only [hdiv, hmod, Nat.add_sub_cancel, hx0, zero_mul, zero_add, Nat.succ_ne_zero,
    if_false, ρ.isLt, dif_pos] at h
  simp only [rqCoeff, i.isLt, dif_pos] at h
  rw [Finset.sum_apply]
  exact h

end Main

end Praxis.Proofs.Pack
