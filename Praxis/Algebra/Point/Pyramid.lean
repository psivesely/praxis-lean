import Praxis.Algebra.Point.Definitions
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Module MeasureTheory Set

open scoped ENNReal

namespace Praxis.Algebra.Point

section Slices

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem pyramid_height (f : V →ₗ[ℝ] ℝ) (a v b : V) (α β : ℝ)
    (hv : f (v - a) = 1) (hb : f (b - a) = 0) (hab : α + β = 1) :
    f (α • v + β • b - a) = α := by
  have h : α • v + β • b - a = α • (v - a) + β • (b - a) := by
    linear_combination (norm := module) hab • a
  rw [h, map_add, map_smul, map_smul, hv, hb]
  simp

theorem pyramid_slice (S : Set V) (hS : S.Nonempty) (a v : V)
    (f : V →ₗ[ℝ] ℝ) (hv : f (v - a) = 1)
    (hbase : ∀ b ∈ S, f (b - a) = 0) (t : ℝ) :
    convexHull ℝ (insert v S) ∩ {x | f (x - a) = t} =
      if t ∈ Icc (0 : ℝ) 1 then
        (fun b => t • v + (1 - t) • b) '' convexHull ℝ S else ∅ := by
  have hbase' : ∀ b ∈ convexHull ℝ S, f (b - a) = 0 := by
    have hc : Convex ℝ {b : V | f (b - a) = 0} := by
      intro x hx y hy α β hα hβ hab
      change f (α • x + β • y - a) = 0
      have heq : α • x + β • y - a = α • (x - a) + β • (y - a) := by
        linear_combination (norm := module) hab • a
      rw [heq, map_add, map_smul, map_smul, hx, hy]
      simp
    exact convexHull_min hbase hc
  rw [convexHull_insert hS]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxt⟩
    obtain ⟨z, hz, b, hb, α, β, hα, hβ, hab, rfl⟩ := mem_convexJoin.mp hx
    have hzv : z = v := mem_singleton_iff.mp hz
    subst z
    have hαt : α = t := by
      rw [pyramid_height f a v b α β hv (hbase' b hb) hab] at hxt
      exact hxt
    have hβt : β = 1 - t := by linarith
    have ht : t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp only [if_pos ht]
    exact ⟨b, hb, by rw [hαt, hβt]⟩
  · intro hx
    split_ifs at hx with ht
    · obtain ⟨b, hb, rfl⟩ := hx
      constructor
      · exact mem_convexJoin.mpr ⟨v, mem_singleton v, b, hb,
          t, 1 - t, ht.1, sub_nonneg.mpr ht.2, by ring, rfl⟩
      · exact pyramid_height f a v b t (1 - t) hv (hbase' b hb) (by ring)
    · exact hx.elim

end Slices

theorem sectionVolume_eq_hausdorff {e : ℕ} (C : Set (E e)) (a : E e)
    (H : Submodule ℝ (E e)) (hC : C ⊆ affineFlat a H) :
    sectionVolume C a H = (Measure.euclideanHausdorffMeasure (finrank ℝ H) C).toReal := by
  let g : H → E e := fun w => a + (w : E e)
  have hg : Isometry g := by
    intro x y
    simpa only [g, edist_add_left] using isometry_subtype_coe.edist_eq x y
  have hrange : Set.range g = affineFlat a H := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      simp [g, affineFlat]
    · intro hx
      exact ⟨⟨x - a, hx⟩, by simp [g]⟩
  have hm := hg.euclideanHausdorffMeasure_preimage
    (d := finrank ℝ H) C
  rw [hrange, Set.inter_eq_left.mpr hC,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at hm
  exact congrArg ENNReal.toReal hm

theorem pyramid_weight_integral (d : ℕ) :
    ∫⁻ t : ℝ, (Icc (0 : ℝ) 1).indicator
      (fun t => ENNReal.ofReal ((1 - t) ^ d)) t =
        ENNReal.ofReal (1 / (d + 1 : ℝ)) := by
  rw [lintegral_indicator measurableSet_Icc]
  have hi : IntegrableOn (fun t : ℝ => (1 - t) ^ d) (Icc (0 : ℝ) 1) :=
    (by fun_prop : Continuous (fun t : ℝ => (1 - t) ^ d)).continuousOn.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ d) 1]
    simp [integral_pow]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_nonneg (sub_nonneg.mpr ht.2) d

theorem pyramid_normal {e : ℕ} (he : 1 ≤ e) (H : Submodule ℝ (E e))
    (hH : finrank ℝ H = e - 1) (a v : E e) (hv : v ∉ affineFlat a H) :
    ∃ n : E e, n ≠ 0 ∧ H = (ℝ ∙ n)ᗮ ∧ v - a - n ∈ H ∧
      ‖n‖ = Metric.infDist v (affineFlat a H) := by
  let p := H.starProjection (v - a)
  let n := v - a - p
  have hp : p ∈ H := H.starProjection_apply_mem _
  have hn : n ∈ Hᗮ := H.sub_starProjection_mem_orthogonal _
  have hn0 : n ≠ 0 := by
    intro h
    have hpa : v - a = p := sub_eq_zero.mp h
    exact hv (show v - a ∈ H by rw [hpa]; exact hp)
  have hrank : finrank ℝ Hᗮ = 1 := by
    have hh := H.finrank_add_finrank_orthogonal
    rw [hH, finrank_euclideanSpace_fin] at hh
    omega
  have hspan : ℝ ∙ n = Hᗮ :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem n Hᗮ).mpr hn)
      (by rw [finrank_span_singleton hn0, hrank])
  have horth : H = (ℝ ∙ n)ᗮ := by rw [hspan, H.orthogonal_orthogonal]
  refine ⟨n, hn0, horth, ?_, ?_⟩
  · simpa [n] using hp
  · have hnonempty : (affineFlat a H).Nonempty := ⟨a, by simp [affineFlat]⟩
    apply le_antisymm
    · apply (Metric.le_infDist hnonempty).mpr
      intro y hy
      have hyH : y - a ∈ H := hy
      have heq : v - y = (v - a) - (y - a) := by abel
      have hproj : Hᗮ.starProjection (v - y) = n := by
        rw [heq, map_sub, H.starProjection_orthogonal_apply_eq_zero hyH,
          sub_zero, H.starProjection_orthogonal_val]
      simpa only [hproj, dist_eq_norm] using Hᗮ.norm_starProjection_apply_le (v - y)
    · have hpoint : a + p ∈ affineFlat a H := by simpa [affineFlat] using hp
      have hd := Metric.infDist_le_dist_of_mem hpoint (x := v)
      simpa [dist_eq_norm, n, sub_add_eq_sub_sub] using hd

theorem pyramid_height_coordinate {e : ℕ} (H : Submodule ℝ (E e))
    (n : E e) (hn : n ≠ 0) (hH : H = (ℝ ∙ n)ᗮ) :
    ∃ f : E e →ₗ[ℝ] ℝ, f n = 1 ∧ ∀ x, f x = 0 ↔ x ∈ H := by
  let f : E e →ₗ[ℝ] ℝ := (‖n‖ ^ 2)⁻¹ • (innerSL ℝ n).toLinearMap
  have hn2 : ‖n‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hn)
  refine ⟨f, ?_, ?_⟩
  · simp [f, hn2]
  · intro x
    simp [f, hH, Submodule.mem_orthogonal_singleton_iff_inner_right, hn2]

theorem pyramid_flat_eq_level {e : ℕ} (H : Submodule ℝ (E e))
    (a n : E e) (f : E e →ₗ[ℝ] ℝ) (hn : f n = 1)
    (hker : ∀ x, f x = 0 ↔ x ∈ H) (t : ℝ) :
    (AffineSubspace.mk' (t • n + a) H : Set (E e)) = {x | f (x - a) = t} := by
  ext x
  change x - (t • n + a) ∈ H ↔ f (x - a) = t
  rw [← hker]
  have hx : x - (t • n + a) = (x - a) - t • n := by abel
  rw [hx, map_sub, map_smul, hn]
  simp only [smul_eq_mul, mul_one, sub_eq_zero]

theorem pyramid_slice_measure {e : ℕ} (S : Set (E e)) (hS : S.Nonempty)
    (a v : E e) (f : E e →ₗ[ℝ] ℝ) (hv : f (v - a) = 1)
    (hbase : ∀ b ∈ S, f (b - a) = 0) (d : ℕ) (t : ℝ) (ht : t ≠ 1) :
    Measure.euclideanHausdorffMeasure d
      (convexHull ℝ (insert v S) ∩ {x | f (x - a) = t}) =
        (Icc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal ((1 - t) ^ d) *
          Measure.euclideanHausdorffMeasure d (convexHull ℝ S)) t := by
  rw [pyramid_slice S hS a v f hv hbase t]
  by_cases htI : t ∈ Icc (0 : ℝ) 1
  · rw [if_pos htI, Set.indicator_of_mem htI]
    have hhom : (fun b : E e => t • v + (1 - t) • b) =
        AffineMap.homothety v (1 - t) := by
      funext b
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [hhom, euclideanHausdorffMeasure_homothety_image d v (sub_ne_zero.mpr (Ne.symm ht))]
    have hscale : (↑(‖1 - t‖₊ ^ d) : ℝ≥0∞) = ENNReal.ofReal ((1 - t) ^ d) := by
      rw [ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_of_nonneg (sub_nonneg.mpr htI.2),
        ENNReal.ofReal_pow (sub_nonneg.mpr htI.2)]
    simpa only [ENNReal.smul_def, smul_eq_mul] using
      congrArg (fun z : ℝ≥0∞ => z * Measure.euclideanHausdorffMeasure d (convexHull ℝ S)) hscale
  · simp [htI]

theorem pyramid_measure {e : ℕ} (S : Set (E e)) (hS : S.Nonempty)
    (a v n : E e) (hn : n ≠ 0) (H : Submodule ℝ (E e))
    (hH : H = (ℝ ∙ n)ᗮ) (f : E e →ₗ[ℝ] ℝ) (hfn : f n = 1)
    (hker : ∀ x, f x = 0 ↔ x ∈ H) (hv : f (v - a) = 1)
    (hbase : ∀ b ∈ S, f (b - a) = 0)
    (hmeas : MeasurableSet (convexHull ℝ (insert v S))) :
    volume (convexHull ℝ (insert v S)) =
      ‖n‖ₑ * (ENNReal.ofReal (1 / ((e - 1 : ℕ) + 1 : ℕ)) *
        Measure.euclideanHausdorffMeasure (e - 1) (convexHull ℝ S)) := by
  have hslicing := EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral a hn hmeas
  rw [finrank_euclideanSpace_fin, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at hslicing
  simp only [vadd_eq_add] at hslicing
  rw [hslicing]
  congr 1
  have hslice : (fun t : ℝ => Measure.euclideanHausdorffMeasure (e - 1)
      (convexHull ℝ (insert v S) ∩ AffineSubspace.mk' (t • n + a) (ℝ ∙ n)ᗮ)) =ᵐ[volume]
      (Icc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal ((1 - t) ^ (e - 1)) *
        Measure.euclideanHausdorffMeasure (e - 1) (convexHull ℝ S)) := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 1] with t ht
    rw [← hH, pyramid_flat_eq_level H a n f hfn hker]
    exact pyramid_slice_measure S hS a v f hv hbase (e - 1) t ht
  rw [lintegral_congr_ae hslice]
  have hind : (Icc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal ((1 - t) ^ (e - 1)) *
      Measure.euclideanHausdorffMeasure (e - 1) (convexHull ℝ S)) =
      fun t => (Icc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal ((1 - t) ^ (e - 1))) t *
        Measure.euclideanHausdorffMeasure (e - 1) (convexHull ℝ S) := by
    ext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1 <;> simp [ht]
  rw [hind, lintegral_mul_const _ (Measurable.indicator (by fun_prop) measurableSet_Icc),
    pyramid_weight_integral]
  simp only [Nat.cast_add, Nat.cast_one]

theorem pyramidVolume : PyramidVolume := by
  classical
  intro e he H a v B hH hB _hspan hflat hv
  obtain ⟨n, hn, horth, hres, hheight⟩ := pyramid_normal he H hH a v hv
  obtain ⟨f, hfn, hker⟩ := pyramid_height_coordinate H n hn horth
  have hfv : f (v - a) = 1 := by
    have hh := (hker (v - a - n)).mpr hres
    rw [map_sub, hfn] at hh
    linarith
  have hbase : ∀ b ∈ (B : Set (E e)), f (b - a) = 0 := by
    intro b hb
    exact (hker (b - a)).mpr (hflat b hb)
  have hc : convexHull ℝ (B : Set (E e)) ⊆ affineFlat a H := by
    apply convexHull_min hflat
    exact (AffineSubspace.mk' a H).convex
  have hmeas : MeasurableSet (convexHull ℝ (insert v (B : Set (E e)))) :=
    ((B.finite_toSet.insert v).isCompact_convexHull ℝ).measurableSet
  have hm := pyramid_measure (B : Set (E e)) hB a v n hn H horth f hfn hker hfv hbase hmeas
  rw [Nat.sub_add_cancel he] at hm
  rw [sectionVolume_eq_hausdorff _ a H hc, hH]
  unfold volHull
  rw [Finset.coe_insert, hm, ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg e))]
  rw [← hheight]
  simp only [enorm, ENNReal.coe_toReal, coe_nnnorm]
  ring

end Praxis.Algebra.Point
