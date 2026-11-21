import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

open Matrix MeasureTheory Module

namespace HeavyStack

def l1 {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, |x i|

def l1Ball (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) := {x | l1 x ≤ R}

theorem l1_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ l1 x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_l1 {d : ℕ} (x : Fin d → ℝ) (i : Fin d) : |x i| ≤ l1 x := by
  unfold l1
  exact Finset.single_le_sum (f := fun j : Fin d => |x j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem l1Ball_convex (d : ℕ) (R : ℝ) : Convex ℝ (l1Ball d R) := by
  intro x hx y hy a b ha hb hab
  change (∑ i, |a * x i + b * y i|) ≤ R
  calc
    _ ≤ ∑ i, (a * |x i| + b * |y i|) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ |a * x i| + |b * y i| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * l1 x + b * l1 y := by
      simp [l1, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * R + b * R :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul, hab, one_mul]

theorem l1Ball_compact (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (l1Ball d R) := by
  have hc : Continuous (fun x : Fin d → ℝ => l1 x) := by unfold l1; fun_prop
  have hclosed : IsClosed (l1Ball d R) := isClosed_le hc continuous_const
  apply (isCompact_closedBall (0 : Fin d → ℝ) R).of_isClosed_subset hclosed
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  intro i
  simpa only [Real.norm_eq_abs] using (abs_le_l1 x i).trans hx

theorem volume_l1Ball {d : ℕ} (hd : 0 < d) (R : ℝ) :
    volume (l1Ball d R) = ENNReal.ofReal R ^ d *
      ENNReal.ofReal ((2 : ℝ) ^ d / (Nat.factorial d : ℝ)) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  have h := MeasureTheory.volume_sum_rpow_le (Fin d) (p := 1) (by norm_num) R
  simp only [one_div_one, div_one, Real.rpow_one, Fintype.card_fin] at h
  rw [show (1 : ℝ) + 1 = 2 by norm_num, hg, Real.Gamma_nat_eq_factorial, mul_one] at h
  exact h

theorem exists_int_combination_l1_le {d : ℕ} (hd : 0 < d)
    (b : Basis (Fin d) ℝ (Fin d → ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hbound : (Nat.factorial d : ℝ) * |(Matrix.of b).det| ≤ R ^ d) :
    ∃ t : Fin d → ℤ,
      (∑ j, (t j : ℝ) • b j) ≠ 0 ∧ l1 (∑ j, (t j : ℝ) • b j) ≤ R := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    (b.restrictScalars ℤ).repr.injective.countable
  have hreal : |(Matrix.of b).det| * (2 : ℝ) ^ d ≤
      R ^ d * ((2 : ℝ) ^ d / (Nat.factorial d : ℝ)) := by
    calc
      _ = ((Nat.factorial d : ℝ) * |(Matrix.of b).det|) *
          ((2 : ℝ) ^ d / (Nat.factorial d : ℝ)) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (by positivity)
  have hmeasure : volume (ZSpan.fundamentalDomain b) *
      2 ^ finrank ℝ (Fin d → ℝ) ≤ volume (l1Ball d R) := by
    calc
      _ = ENNReal.ofReal (|(Matrix.of b).det| * (2 : ℝ) ^ d) := by
        rw [ZSpan.volume_fundamentalDomain]
        simp only [finrank_fintype_fun_eq_card, Fintype.card_fin]
        rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (by positivity)]
        norm_num
      _ ≤ ENNReal.ofReal (R ^ d * ((2 : ℝ) ^ d / (Nat.factorial d : ℝ))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [volume_l1Ball hd R, ENNReal.ofReal_mul (pow_nonneg hR d),
          ENNReal.ofReal_pow hR]
  obtain ⟨x, hx0, hx⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (ZSpan.isAddFundamentalDomain' b volume)
      (fun x hx => by simpa [l1Ball, l1] using hx)
      (l1Ball_convex d R) (l1Ball_compact d hR) hmeasure
  have hint := (b.mem_span_iff_repr_mem ℤ (x : Fin d → ℝ)).mp x.property
  choose t ht using hint
  have ht' (i : Fin d) : (t i : ℝ) = b.repr (x : Fin d → ℝ) i := ht i
  have hsum : (∑ j, (t j : ℝ) • b j) = (x : Fin d → ℝ) := by
    simpa only [ht'] using b.sum_repr (x : Fin d → ℝ)
  refine ⟨t, ?_, ?_⟩
  · rw [hsum]
    exact fun h => hx0 (Subtype.ext h)
  · rw [hsum]
    exact hx

theorem exists_int_mulVec_l1_le {d : ℕ} (hd : 0 < d)
    (C : Matrix (Fin d) (Fin d) ℤ) (hC : C.det ≠ 0)
    {R : ℝ} (hR : 0 ≤ R)
    (hbound : (Nat.factorial d : ℝ) * |(C.det : ℝ)| ≤ R ^ d) :
    ∃ t : Fin d → ℤ, C *ᵥ t ≠ 0 ∧ l1 (fun i => ((C *ᵥ t) i : ℝ)) ≤ R := by
  classical
  let A : Matrix (Fin d) (Fin d) ℝ := C.map fun x => (x : ℝ)
  have hA : A.det ≠ 0 := by
    rw [show A.det = (C.det : ℝ) from (Int.cast_det C).symm]
    exact_mod_cast hC
  let e := Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin d)) A (isUnit_iff_ne_zero.mpr hA)
  let b := (Pi.basisFun ℝ (Fin d)).map e
  have hb (j i : Fin d) : b j i = A i j := by
    simp [b, e, Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Pi.basisFun_apply, Pi.single_apply, mul_ite]
  have hbdet : |(Matrix.of b).det| = |(C.det : ℝ)| := by
    have heq : Matrix.of b = Aᵀ := by ext i j; exact hb i j
    rw [heq, Matrix.det_transpose]
    exact congrArg abs (Int.cast_det C).symm
  obtain ⟨t, ht0, ht⟩ := exists_int_combination_l1_le hd b hR (hbdet ▸ hbound)
  have hsum : (∑ j, (t j : ℝ) • b j) = fun i => ((C *ᵥ t) i : ℝ) := by
    ext i
    simp [Finset.sum_apply, hb, A, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨t, ?_, ?_⟩
  · intro h
    apply ht0
    rw [hsum, h]
    ext i
    exact Int.cast_zero
  · rwa [hsum] at ht

end HeavyStack
