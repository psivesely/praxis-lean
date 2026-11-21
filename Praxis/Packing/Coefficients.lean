import Praxis.Forms
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Forms
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Probability.Distributions.Uniform
import Praxis.Constants
import Praxis.Params
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Packing

open Praxis.Constants

def packCoeffs (w : Algebra.Vec ℤ N) : Algebra.CoeffVec ring_degree module_columns :=
  fun c t => if h : c.val * ring_degree + t.val < N then w (Fin.succ ⟨_, h⟩) else 0

theorem slot_coefficients (P : Praxis.Params) (w : Algebra.Vec ℤ P.N)
    (c : Fin P.cols) (t : Fin P.d) :
    Praxis.slotPoly (P := P) (Algebra.castVec (p := P.q) w) c t =
      ((if h : c.val * P.d + t.val < P.N then w (Fin.succ ⟨_, h⟩) else 0 : ℤ) : ZMod P.q) := by
  unfold Praxis.slotPoly Algebra.castVec
  by_cases h : c.val * P.d + t.val < P.N
  · have h' : 1 + P.d * c.val + t.val < P.N + 1 := by rw [Nat.mul_comm P.d]; omega
    simp only [dif_pos h', dif_pos h]
    apply congrArg (fun z : ℤ => (z : ZMod P.q))
    apply congrArg w
    apply Fin.ext
    simp only [Fin.val_succ]
    rw [Nat.mul_comm P.d]
    omega
  · have h' : ¬ 1 + P.d * c.val + t.val < P.N + 1 := by rw [Nat.mul_comm P.d]; omega
    simp only [dif_neg h', dif_neg h, Int.cast_zero]

private def chunk (i : Fin N) : Fin module_columns :=
  ⟨i.val / ring_degree, by
    have hi := i.isLt
    norm_num [N, ring_degree, module_columns] at hi ⊢
    omega⟩

private def offset (i : Fin N) : Fin ring_degree :=
  ⟨i.val % ring_degree, Nat.mod_lt _ (by norm_num [ring_degree])⟩

private theorem pack_column (w : Algebra.Vec ℤ N) (i : Fin N) :
    packCoeffs w (chunk i) (offset i) = w i.succ := by
  have hi : (chunk i).val * ring_degree + (offset i).val = i.val := by
    simpa [chunk, offset, Nat.mul_comm] using Nat.div_add_mod i.val ring_degree
  simp [packCoeffs, hi, i.isLt]

theorem pack_nonzero (w : Algebra.Vec ℤ N) (h0 : w 0 = 0) :
    Algebra.castVec (p := q) w ≠ 0 ↔ Algebra.NonzeroModP q (packCoeffs w) := by
  constructor
  · intro hw
    by_contra hpack
    apply hw
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Algebra.castVec, h0]
    · have hj : ((packCoeffs w (chunk j) (offset j) : ℤ) : ZMod q) = 0 := by
        by_contra hj
        exact hpack ⟨chunk j, offset j, hj⟩
      simpa only [pack_column, Algebra.castVec, Pi.zero_apply] using hj
  · rintro ⟨c, t, hct⟩ hw
    unfold packCoeffs at hct
    split at hct
    · exact hct (congrFun hw _)
    · exact hct (by simp)

end Praxis.Packing
