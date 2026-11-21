import Praxis.Algebra.Point.Definitions
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

noncomputable section

open Module MeasureTheory

open scoped Pointwise

namespace Praxis.Algebra.Point

namespace Dim4

theorem section_card_lower {e : ℕ} (T : Finset (E e)) (he : 0 < e)
    (hspan : spanDim T = e) : e + 1 ≤ T.card := by
  classical
  have hne : T.Nonempty := by
    by_contra h
    have hzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst T
    unfold spanDim at hspan
    rw [Finset.coe_empty, vectorSpan_empty, finrank_bot] at hspan
    omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hne))
  have hdim := finrank_vectorSpan_image_finset_le ℝ (id : E e → E e) T hm
  have hid : T.image (id : E e → E e) = T := Finset.image_id (s := T)
  rw [hid] at hdim
  change spanDim T ≤ m at hdim
  rw [hspan] at hdim
  omega

theorem hull_count4 (hcount : SimplexCount 4) (L : FullLat 4) (b : E 4)
    (T : Finset (E 4)) (hcoset : InCoset L b T) (hspan : spanDim T = 4) :
    (T.card : ℝ) ≤ 120 * volHull T / L.det := by
  have hc := hcount (by decide) (by decide) L b T hcoset hspan
  have hcard : (5 : ℝ) ≤ T.card := by
    exact_mod_cast section_card_lower T (by decide) hspan
  norm_num [Nat.factorial] at hc
  have hratio : 1 ≤ 24 * volHull T / L.det := by linarith
  have heq : 120 * volHull T / L.det = 5 * (24 * volHull T / L.det) := by ring
  rw [heq]
  linarith

theorem isCompact_differenceBody {n : ℕ} {C : Set (E n)} (hC : IsCompact C) :
    IsCompact (differenceBody C) := by
  have hset : differenceBody C = (fun p : E n × E n => p.1 - p.2) '' (C ×ˢ C) := by
    ext z
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  rw [hset]
  exact (hC.prod hC).image (continuous_fst.sub continuous_snd)

theorem central_section_measure_ne_top {n : ℕ} (W : Submodule ℝ (E n))
    {C : Set (E n)} (hC : IsCompact C) :
    volume {w : W | (w : E n) ∈ C} ≠ ⊤ := by
  have hc : IsCompact {w : W | (w : E n) ∈ C} :=
    W.closed_of_finiteDimensional.isProperMap_subtypeVal.isCompact_preimage hC
  exact hc.measure_lt_top.ne

theorem volHull_le_difference_section {n e : ℕ} (W : Submodule ℝ (E n))
    (chart : W ≃ₗᵢ[ℝ] E e) (a : E n) (C : Set (E n)) (S : Finset W)
    (hC : IsCompact C) (hconv : Convex ℝ C)
    (hcontained : ∀ x ∈ S, a + (x : E n) ∈ C) (hne : S.Nonempty) :
    volHull (S.image chart) ≤ sectionVolume (differenceBody C) 0 W := by
  classical
  let H : Set W := convexHull ℝ (S : Set W)
  have hH : ∀ x ∈ H, a + (x : E n) ∈ C := by
    let f : W →ᵃ[ℝ] E n := AffineMap.const ℝ W a + W.subtype.toAffineMap
    have hf : Convex ℝ (f ⁻¹' C) := hconv.affine_preimage f
    exact convexHull_min hcontained hf
  obtain ⟨s, hs⟩ := hne
  have hsub : (fun w : W => w + s) ⁻¹' H ⊆
      {w : W | (w : E n) ∈ differenceBody C} := by
    intro w hw
    refine ⟨a + ((w + s : W) : E n), hH (w + s) hw,
      a + (s : E n), hcontained s hs, ?_⟩
    simp only [Submodule.coe_add]
    abel
  have hmeasure : volume H ≤ volume {w : W | (w : E n) ∈ differenceBody C} := by
    rw [← measure_preimage_add_right volume s H]
    exact measure_mono hsub
  have hchart : chart ⁻¹' convexHull ℝ (S.image chart : Set (E e)) = H := by
    rw [Finset.coe_image]
    change chart ⁻¹' convexHull ℝ (chart.toLinearEquiv.toLinearMap '' (S : Set W)) = H
    rw [← chart.toLinearEquiv.toLinearMap.image_convexHull]
    exact Set.preimage_image_eq _ chart.injective
  have hvol : volume H = volume (convexHull ℝ (S.image chart : Set (E e))) := by
    rw [← hchart]
    exact chart.measurePreserving.measure_preimage_emb chart.toHomeomorph.measurableEmbedding _
  unfold volHull sectionVolume
  simp only [zero_add]
  rw [← hvol]
  exact ENNReal.toReal_mono
    (central_section_measure_ne_top W (isCompact_differenceBody hC)) hmeasure

theorem differenceBody_eq_two_smul {n : ℕ} {C : Set (E n)} (hconv : Convex ℝ C)
    (hsym : CentrallySymmetric C) : differenceBody C = (2 : ℝ) • C := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y) ∈ C :=
      hconv hx ((hsym y).mp hy) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y), hm, ?_⟩
    module
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, -x, (hsym x).mp hx, ?_⟩
    module

theorem symmetric_difference_section_volume {n e : ℕ} (W : Submodule ℝ (E n))
    (chart : W ≃ₗᵢ[ℝ] E e) (C : Set (E n)) (hconv : Convex ℝ C)
    (hsym : CentrallySymmetric C) :
    sectionVolume (differenceBody C) 0 W = (2 : ℝ)^e * sectionVolume C 0 W := by
  have hdim : finrank ℝ W = e := by
    simpa using chart.toLinearEquiv.finrank_eq
  have hset : {w : W | (w : E n) ∈ differenceBody C} =
      (2 : ℝ) • {w : W | (w : E n) ∈ C} := by
    rw [differenceBody_eq_two_smul hconv hsym]
    ext w
    constructor
    · rintro ⟨x, hx, heq⟩
      have hxW : x ∈ W := by
        have hmem : (2 : ℝ) • x ∈ W := by
          change (2 : ℝ) • x = (w : E n) at heq
          rw [heq]
          exact w.property
        simpa using W.smul_mem (1 / 2 : ℝ) hmem
      refine ⟨⟨x, hxW⟩, hx, ?_⟩
      exact Subtype.ext heq
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : E n), hx, rfl⟩
  unfold sectionVolume
  simp only [zero_add]
  rw [hset, volume.addHaar_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hdim,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2^e)]

end Dim4

open Praxis.Algebra.Point.Dim4 in

theorem sectionCount4 (hcount : SimplexCount 4) (_hlower : SimplexVolumeLower) :
    SectionCount4 := by
  intro n _hn W chart L a b C S hC hconv hcontained hcoset hspan
  have hneT : (S.image chart).Nonempty := by
    have hc := section_card_lower (S.image chart) (by decide : 0 < 4) hspan
    exact Finset.card_pos.mp (by omega)
  have hne : S.Nonempty := Finset.image_nonempty.mp hneT
  have hvol := volHull_le_difference_section W chart a C S hC hconv hcontained hne
  have hd : 0 < L.det := ZLattice.covolume_pos L.carrier (volume : Measure (E 4))
  have hcountT := hull_count4 hcount L b (S.image chart) hcoset hspan
  have hcard : (S.image chart).card = S.card := Finset.card_image_of_injective S chart.injective
  rw [hcard] at hcountT
  have hbound : (S.card : ℝ) ≤ 972 * sectionVolume (differenceBody C) 0 W / L.det := by
    apply hcountT.trans
    apply (div_le_div_iff_of_pos_right hd).mpr
    have hvnonneg : 0 ≤ sectionVolume (differenceBody C) 0 W := ENNReal.toReal_nonneg
    nlinarith
  refine ⟨hbound, ?_⟩
  intro hsym
  have hscale := symmetric_difference_section_volume W chart C hconv hsym
  exact ⟨hscale, by simpa only [Nat.cast_ofNat, hscale, mul_assoc] using hbound⟩

end Praxis.Algebra.Point
