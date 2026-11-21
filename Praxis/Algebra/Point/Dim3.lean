import Praxis.Algebra.Point.Definitions
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section

open Module MeasureTheory

open scoped Pointwise

namespace Praxis.Algebra.Point

theorem exists_full_simplex {e : ℕ} (he : 0 < e) (S : Finset (E e))
    (hS : spanDim S = e) :
    ∃ v : Fin (e + 1) → E e, (∀ i, v i ∈ S) ∧ AffineIndependent ℝ v := by
  classical
  obtain ⟨t, ht, hspan, hi⟩ := exists_affineIndependent ℝ (E e) (S : Set (E e))
  have hdim : Module.finrank ℝ (vectorSpan ℝ t) = e := by
    rw [← direction_affineSpan, hspan, direction_affineSpan]
    exact hS
  have htne : t.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, vectorSpan_empty] at hdim
    simp only [finrank_bot] at hdim
    omega
  let : Nonempty t := htne.to_subtype
  let : Fintype t := (S.finite_toSet.subset ht).fintype
  have hcard : Fintype.card t = e + 1 := by
    have hc := hi.finrank_vectorSpan_add_one
    rw [Subtype.range_coe, hdim] at hc
    exact hc.symm
  let f := Fintype.equivFinOfCardEq hcard
  exact ⟨fun i => (f.symm i : E e), fun i => ht (f.symm i).property,
    hi.comp_embedding f.symm.toEmbedding⟩

theorem count_le_twentyfour (hcount : SimplexCount 3) (hlower : SimplexVolumeLower)
    (L : FullLat 3) (b : E 3) (T : Finset (E 3))
    (hcoset : InCoset L b T) (hdim : spanDim T = 3) :
    (T.card : ℝ) ≤ 24 * volHull T / L.det := by
  obtain ⟨v, hv, hi⟩ := exists_full_simplex (by decide : 0 < 3) T hdim
  have hsub : (simplexPoints v : Set (E 3)) ⊆ (T : Set (E 3)) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hv i
  have hvol : volHull (simplexPoints v) ≤ volHull T :=
    measureReal_mono (convexHull_mono hsub)
      (T.finite_toSet.isCompact_convexHull ℝ).measure_ne_top
  have hlo := hlower 3 L b v (fun i => hcoset _ (hv i)) hi
  have hc := hcount (by decide) (by decide) L b T hcoset hdim
  have hdet : 0 < L.det := ZLattice.covolume_pos L.carrier volume
  norm_num at hlo hc
  have hr : 1 ≤ 6 * volHull T / L.det := by
    apply (le_div_iff₀ hdet).mpr
    linarith
  calc
    (T.card : ℝ) ≤ 6 * volHull T / L.det + 3 := hc
    _ ≤ 4 * (6 * volHull T / L.det) := by linarith
    _ = 24 * volHull T / L.det := by ring

theorem isCompact_differenceBody {n : ℕ} {C : Set (E n)} (hC : IsCompact C) :
    IsCompact (differenceBody C) := by
  have heq : differenceBody C =
      (fun p : E n × E n => p.1 - p.2) '' (C ×ˢ C) := by
    ext z
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  rw [heq]
  exact (hC.prod hC).image (by fun_prop)

theorem volHull_le_difference_section {n e : ℕ}
    (W : Submodule ℝ (E n)) (chart : W ≃ₗᵢ[ℝ] E e)
    (a : E n) (C : Set (E n)) (S : Finset W)
    (hcompact : IsCompact C) (hconvex : Convex ℝ C) (hne : S.Nonempty)
    (hcontained : ∀ x ∈ S, a + (x : E n) ∈ C) :
    volHull (S.image chart) ≤ sectionVolume (differenceBody C) 0 W := by
  classical
  obtain ⟨p, hp⟩ := hne
  let D : Set W := {w | (w : E n) ∈ differenceBody C}
  have hDc : IsCompact D :=
    (W.isClosedEmbedding_subtype W.closed_of_finiteDimensional).isCompact_preimage
      (isCompact_differenceBody hcompact)
  let f : E e →ᵃ[ℝ] E n := AffineMap.const ℝ (E e) a +
    (W.subtype.comp chart.symm.toLinearEquiv.toLinearMap).toAffineMap
  have hHull : convexHull ℝ (S.image chart : Set (E e)) ⊆ f ⁻¹' C := by
    apply convexHull_min _ (hconvex.affine_preimage f)
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    simpa [f] using hcontained w hw
  have hsub : (fun x : E e => x - chart p) ''
      convexHull ℝ (S.image chart : Set (E e)) ⊆ chart.symm ⁻¹' D := by
    rintro _ ⟨x, hx, rfl⟩
    change (chart.symm (x - chart p) : E n) ∈ differenceBody C
    refine ⟨a + (chart.symm x : E n), hHull hx,
      a + (p : E n), hcontained p hp, ?_⟩
    simp only [map_sub, LinearIsometryEquiv.symm_apply_apply, Submodule.coe_sub]
    abel
  have hmeasure := measure_mono hsub (μ := (volume : Measure (E e)))
  rw [chart.symm.measurePreserving.measure_preimage_emb
    chart.symm.toHomeomorph.measurableEmbedding D] at hmeasure
  have htranslate (K : Set (E e)) : (fun x : E e => x - chart p) '' K =
      (fun x => x + chart p) ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + chart p, hx, add_sub_cancel_right x (chart p)⟩
  rw [htranslate, measure_preimage_add_right] at hmeasure
  simpa [volHull, sectionVolume, D] using ENNReal.toReal_mono hDc.measure_ne_top hmeasure

theorem differenceBody_eq_two_smul {n : ℕ} {C : Set (E n)}
    (hconvex : Convex ℝ C) (hsym : CentrallySymmetric C) :
    differenceBody C = (2 : ℝ) • C := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    have hm := hconvex hx ((hsym y).mp hy)
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
    refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y), hm, ?_⟩
    simp [smul_add, smul_smul, sub_eq_add_neg]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, -x, (hsym x).mp hx, ?_⟩
    simp [two_smul]

theorem difference_section_volume {n e : ℕ}
    (W : Submodule ℝ (E n)) (chart : W ≃ₗᵢ[ℝ] E e)
    (C : Set (E n)) (hconvex : Convex ℝ C) (hsym : CentrallySymmetric C) :
    sectionVolume (differenceBody C) 0 W = (2 : ℝ)^e * sectionVolume C 0 W := by
  have hdim : Module.finrank ℝ W = e := by
    simpa using chart.toLinearEquiv.finrank_eq
  have heq : {w : W | (0 : E n) + (w : E n) ∈ differenceBody C} =
      (2 : ℝ) • {w : W | (0 : E n) + (w : E n) ∈ C} := by
    rw [differenceBody_eq_two_smul hconvex hsym]
    ext w
    simp only [zero_add, Set.mem_ofPred_eq, Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      refine ⟨(1 / 2 : ℝ) • w, ?_, ?_⟩
      · change ((1 / 2 : ℝ) • (w : E n)) ∈ C
        rw [← hxeq, smul_smul]
        simpa using hx
      · simp [smul_smul]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : E n), hx, rfl⟩
  unfold sectionVolume
  rw [heq, Measure.addHaar_smul_of_nonneg volume (by norm_num : 0 ≤ (2 : ℝ)),
    hdim, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem sectionCount3 (hcount : SimplexCount 3) (hlower : SimplexVolumeLower) :
    SectionCount3 := by
  classical
  intro n _ W chart L a b C S hcompact hconvex hcontained hcoset hdim
  have hne : S.Nonempty := by
    obtain ⟨v, hv, _⟩ := exists_full_simplex (by decide : 0 < 3) (S.image chart) hdim
    obtain ⟨p, hp, _⟩ := Finset.mem_image.mp (hv 0)
    exact ⟨p, hp⟩
  have hc := count_le_twentyfour hcount hlower L b (S.image chart) hcoset hdim
  rw [Finset.card_image_of_injective _ chart.injective] at hc
  have hv := volHull_le_difference_section W chart a C S hcompact hconvex hne hcontained
  have hdet : 0 < L.det := ZLattice.covolume_pos L.carrier volume
  have hvolume : 0 ≤ sectionVolume (differenceBody C) 0 W := ENNReal.toReal_nonneg
  have hbound : (S.card : ℝ) ≤ 81 * sectionVolume (differenceBody C) 0 W / L.det := by
    apply hc.trans
    apply (div_le_div_iff_of_pos_right hdet).mpr
    linarith
  refine ⟨hbound, ?_⟩
  intro hsym
  have heq := difference_section_volume W chart C hconvex hsym
  refine ⟨heq, ?_⟩
  rw [heq] at hbound
  simpa only [mul_assoc, Nat.cast_ofNat] using hbound

end Praxis.Algebra.Point
