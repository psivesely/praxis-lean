import Praxis.Algebra.Point.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Combination

noncomputable section

open MeasureTheory Set

open scoped BigOperators ENNReal

namespace Praxis.Algebra.Point

private theorem abs_measurable : Measurable (fun x : ℝ => |x|) := by
  simpa only [Real.norm_eq_abs] using
    (continuous_norm.measurable : Measurable (fun x : ℝ => ‖x‖))

private theorem map_abs_volume :
    (volume : Measure ℝ).map (fun x => |x|) =
      (2 : ℝ≥0∞) • volume.restrict (Ici (0 : ℝ)) := by
  rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
  ext s hs
  rw [Measure.map_apply abs_measurable hs, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply hs]
  have heq : (fun x : ℝ => |x|) ⁻¹' s =ᵐ[volume]
      ((s ∩ Ioi 0) ∪ (fun x : ℝ => -x) ⁻¹' (s ∩ Ioi 0) : Set ℝ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
    apply propext
    change (|x| ∈ s) ↔ ((x ∈ s ∧ 0 < x) ∨ (-x ∈ s ∧ 0 < -x))
    rcases lt_or_gt_of_ne hx with hx | hx
    · simp [abs_of_neg hx, not_lt_of_ge hx.le, neg_pos.mpr hx]
    · simp [abs_of_pos hx, hx, not_lt_of_ge (neg_nonpos.mpr hx.le)]
  rw [measure_congr heq, measure_union]
  · rw [Measure.measure_preimage_neg, two_mul]
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hp : 0 < x := Set.mem_Ioi.mp hx.2
    have hn : 0 < -x := Set.mem_Ioi.mp hy.2
    exact (not_lt_of_ge hp.le) (neg_pos.mp hn)
  · exact (hs.inter measurableSet_Ioi).preimage measurable_neg

private theorem map_abs_volume_pi (e : ℕ) :
    (volume : Measure (Fin e → ℝ)).map (fun x i => |x i|) =
      (2 : ℝ≥0∞)^e • volume.restrict (Set.univ.pi fun _ => Ici (0 : ℝ)) := by
  have : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℝ).restrict (Ici 0)) := by
    rw [two_smul ℝ≥0∞]
    infer_instance
  have : SigmaFinite ((volume : Measure ℝ).map (fun x => |x|)) := by
    rw [map_abs_volume]
    infer_instance
  change (Measure.pi fun _ : Fin e => (volume : Measure ℝ)).map _ = _
  rw [Measure.pi_map_pi (fun _ => abs_measurable.aemeasurable)]
  simp_rw [map_abs_volume]
  change (Measure.pi fun _ : Fin e => (2 : ℝ≥0∞) •
    (volume : Measure ℝ).restrict (Ici 0)) = (2 : ℝ≥0∞)^e •
      (Measure.pi fun _ : Fin e => (volume : Measure ℝ)).restrict
        (Set.univ.pi fun _ => Ici (0 : ℝ))
  rw [Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.pi_pi, Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem standardSimplex_hull (e : ℕ) :
    convexHull ℝ (simplexPoints (standardVertices e) : Set (E e)) =
      {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  classical
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [standardVertices]
      · simp [standardVertices, EuclideanSpace.basisFun_apply,
          PiLp.single_apply]
        intro i
        split_ifs <;> norm_num
    · intro x hx y hy a b ha hb hab
      constructor
      · intro i
        change 0 ≤ a * x i + b * y i
        exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
      · change (∑ i, (a * x i + b * y i)) ≤ 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        nlinarith [mul_le_mul_of_nonneg_left hx.2 ha,
          mul_le_mul_of_nonneg_left hy.2 hb]
  · intro x hx
    let w : Fin (e + 1) → ℝ := Fin.cases (1 - ∑ i, x i) (fun i => x i)
    apply mem_convexHull_of_exists_fintype w (standardVertices e)
    · intro i
      exact Fin.cases (sub_nonneg.mpr hx.2) (fun j => hx.1 j) i
    · simp [w, Fin.sum_univ_succ]
    · intro i
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    · simp only [Fin.sum_univ_succ, w, standardVertices, Fin.cases_zero,
        Fin.cases_succ, smul_zero, zero_add]
      exact (EuclideanSpace.basisFun (Fin e) ℝ).sum_repr x

private theorem volume_positive_simplex (e : ℕ) :
    volume {x : Fin e → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} =
      ENNReal.ofReal (1 / (e.factorial : ℝ)) := by
  classical
  let S : Set (Fin e → ℝ) := {x | ∑ i, x i ≤ 1}
  have hS : MeasurableSet S := by
    apply measurableSet_le
    · exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
    · exact measurable_const
  have hfold := congrArg (fun μ : Measure (Fin e → ℝ) => μ S) (map_abs_volume_pi e)
  rw [Measure.map_apply (by fun_prop) hS, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply hS] at hfold
  have hsect : S ∩ Set.univ.pi (fun _ : Fin e => Ici (0 : ℝ)) =
      {x : Fin e → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
    ext x
    simp only [S, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ_pi,
      Set.mem_Ici]
    exact and_comm
  rw [hsect] at hfold
  have hballClosed : volume {x : Fin e → ℝ | ∑ i, |x i| ≤ 1} =
      ENNReal.ofReal ((2 : ℝ)^e / (e.factorial : ℝ)) := by
    cases e with
    | zero => simp [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
    | succ n =>
      have hgamma : Real.Gamma (2 : ℝ) = 1 := by
        simp
      simpa only [Fintype.card_fin, div_one, Real.rpow_one,
        one_add_one_eq_two, hgamma, mul_one, Real.Gamma_nat_eq_factorial,
        ENNReal.ofReal_one, one_pow, one_mul] using
        (volume_sum_rpow_le (Fin (n + 1)) (p := 1) (by norm_num) 1)
  have hscaled : (2 : ℝ≥0∞)^e *
      volume {x : Fin e → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} =
      (2 : ℝ≥0∞)^e * ENNReal.ofReal (1 / (e.factorial : ℝ)) := by
    rw [← hfold]
    change volume {x : Fin e → ℝ | ∑ i, |x i| ≤ 1} = _
    rw [hballClosed]
    calc
      ENNReal.ofReal ((2 : ℝ)^e / (e.factorial : ℝ)) =
          ENNReal.ofReal ((2 : ℝ)^e * (1 / (e.factorial : ℝ))) := by
            congr 1
            ring
      _ = ENNReal.ofReal ((2 : ℝ)^e) *
          ENNReal.ofReal (1 / (e.factorial : ℝ)) :=
        ENNReal.ofReal_mul (by positivity)
      _ = _ := by simp
  exact (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞)^e)
    (by positivity) (by finiteness)).mp hscaled

theorem stdSimplexVolume : StdSimplexVolume := by
  intro e
  rw [volHull, standardSimplex_hull]
  have hvolume : volume {x : E e | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} =
      volume {x : Fin e → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
    have hm : MeasurableSet {x : Fin e → ℝ |
        (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
      have hn : MeasurableSet {x : Fin e → ℝ | ∀ i, (0 : ℝ) ≤ x i} := by
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter (fun i =>
          measurableSet_le measurable_const (measurable_pi_apply i))
      exact hn.inter (measurableSet_le
        (by fun_prop : Measurable (fun x : Fin e → ℝ => ∑ i, x i)) measurable_const)
    exact ((PiLp.volume_preserving_ofLp (Fin e)).measure_preimage
      hm.nullMeasurableSet)
  rw [hvolume, volume_positive_simplex, ENNReal.toReal_ofReal (by positivity)]

end Praxis.Algebra.Point
