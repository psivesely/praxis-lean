import Praxis.Algebra.Conversion.ConversionStatement
import Praxis.Algebra.Conversion.ConversionAlgebra

open Matrix

namespace HeavyStack

theorem exists_centered_lift {p n : ℕ} [NeZero p]
    (z : Fin n → ZMod p) (hz : z ≠ 0) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ (∀ i, (w i : ZMod p) = z i) ∧
      ∀ i, |(w i : ℝ)| ≤ (p : ℝ) / 2 := by
  let w : Fin n → ℤ := fun i => (z i).valMinAbs
  have hwcast (i : Fin n) : (w i : ZMod p) = z i := ZMod.coe_valMinAbs _
  refine ⟨w, ?_, hwcast, ?_⟩
  · intro h
    apply hz
    funext i
    rw [← hwcast i, h]
    simp
  · intro i
    have hl : -(p : ℝ) < (w i : ℝ) * 2 := by
      exact_mod_cast (z i).valMinAbs_mem_Ioc.1
    have hu : (w i : ℝ) * 2 ≤ (p : ℝ) := by
      exact_mod_cast (z i).valMinAbs_mem_Ioc.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem reduction_ne_zero_of_short {p n : ℕ} (w : Fin n → ℤ)
    (hw : w ≠ 0) (hshort : ∀ i, |(w i : ℝ)| < (p : ℝ)) :
    (fun i => (w i : ZMod p)) ≠ 0 := by
  intro hzero
  apply hw
  funext i
  have hdiv : (p : ℤ) ∣ w i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    exact congrFun hzero i
  have habs : |w i| < (p : ℤ) := by exact_mod_cast hshort i
  exact Int.eq_zero_of_abs_lt_dvd hdiv habs

theorem scalar_ne_zero_of_short_congruence {p n : ℕ}
    (w : Fin n → ℤ) (hw : w ≠ 0)
    (hshort : ∀ i, |(w i : ℝ)| < (p : ℝ))
    (z : Fin n → ZMod p) (a : ZMod p)
    (hcong : ∀ i, (w i : ZMod p) = a * z i) : a ≠ 0 := by
  intro ha
  apply reduction_ne_zero_of_short w hw hshort
  funext i
  simp [hcong i, ha]

end HeavyStack
