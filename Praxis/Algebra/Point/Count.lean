import Praxis.Algebra.Point.Definitions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section

open Module MeasureTheory

namespace Praxis.Algebra.Point

theorem isExposed_insert_of_not_mem_affineSpan {e : ℕ} {B : Finset (E e)}
    {v w : E e} (hB : B.Nonempty) (hv : v ∉ affineSpan ℝ (B : Set (E e)))
    (hw : IsExposed B w) : IsExposed (insert v B) w := by
  classical
  obtain ⟨a, ha⟩ := hB
  obtain ⟨hwB, f, hf⟩ := hw
  have haA : a ∈ affineSpan ℝ (B : Set (E e)) := mem_affineSpan ℝ ha
  have hvW : v - a ∉ vectorSpan ℝ (B : Set (E e)) := by
    simpa only [← direction_affineSpan, ← vsub_eq_sub,
      AffineSubspace.vsub_right_mem_direction_iff_mem haA] using hv
  obtain ⟨g, hgv, hg⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvW inferInstance
  have hgB : ∀ b ∈ B, g b = g a := by
    intro b hb
    have hmem := Submodule.mem_map_of_mem (f := g) (vsub_mem_vectorSpan ℝ hb ha)
    rw [hg, Submodule.mem_bot] at hmem
    simpa only [vsub_eq_sub, map_sub, sub_eq_zero] using hmem
  have hne : g v - g a ≠ 0 := by simpa only [map_sub] using hgv
  let c : ℝ := (f v - f w + 1) / (g v - g a)
  have hc : c * (g v - g a) = f v - f w + 1 := div_mul_cancel₀ _ hne
  refine ⟨Finset.mem_insert_of_mem hwB, f - c • g, ?_⟩
  intro b hb hbw
  simp only [Finset.mem_insert] at hb
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rcases hb with rfl | hb
  · have hgw := hgB w hwB
    rw [hgw]
    nlinarith
  · have hgb := hgB b hb
    have hgw := hgB w hwB
    have hfb := hf b hb hbw
    rw [hgb, hgw]
    linarith only [hfb]

theorem exists_exposed_erase_affineSpan_eq (hexposed : ExposedPoint)
    {e : ℕ} (S : Finset (E e)) (hcard : spanDim S + 1 < S.card) :
    ∃ v, IsExposed S v ∧
      affineSpan ℝ (S.erase v : Set (E e)) = affineSpan ℝ (S : Set (E e)) := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hexposed e S hS
    have herase : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv.1
    have hinsert : insert v (S.erase v) = S := Finset.insert_erase hv.1
    by_cases hvA : v ∈ affineSpan ℝ (S.erase v : Set (E e))
    · refine ⟨v, hv, ?_⟩
      have h := affineSpan_insert_eq_affineSpan ℝ hvA
      simpa only [← Finset.coe_insert, hinsert] using h.symm
    · have hB : (S.erase v).Nonempty := Finset.card_pos.mp (by omega)
      have hltA : affineSpan ℝ (S.erase v : Set (E e)) <
          affineSpan ℝ (S : Set (E e)) := by
        refine lt_of_le_of_ne (affineSpan_mono ℝ (Finset.coe_subset.mpr
          (Finset.erase_subset _ _))) ?_
        intro heq
        exact hvA (heq.symm ▸ mem_affineSpan ℝ hv.1)
      have hltD : spanDim (S.erase v) < spanDim S := by
        have h := AffineSubspace.direction_lt_of_nonempty hltA (hB.to_set.affineSpan ℝ)
        rw [direction_affineSpan, direction_affineSpan] at h
        exact Submodule.finrank_lt_finrank_of_lt h
      obtain ⟨w, hw, hwA⟩ := ih (S.erase v).card (by omega) (S.erase v)
        (by omega) rfl
      have hwv : w ≠ v := (Finset.mem_erase.mp hw.1).1
      have hSw : S.erase w = insert v ((S.erase v).erase w) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hxw, hxS⟩
          by_cases hxv : x = v
          · exact Or.inl hxv
          · exact Or.inr ⟨hxw, hxv, hxS⟩
        · rintro (rfl | ⟨hxw, hxv, hxS⟩)
          · exact ⟨Ne.symm hwv, hv.1⟩
          · exact ⟨hxw, hxS⟩
      refine ⟨w, ?_, ?_⟩
      · rw [← hinsert]
        exact isExposed_insert_of_not_mem_affineSpan hB hvA hw
      · rw [hSw, Finset.coe_insert, ← affineSpan_insert_affineSpan, hwA,
          affineSpan_insert_affineSpan, ← Finset.coe_insert, hinsert]

theorem dimension_add_one_le_card {e : ℕ} (S : Finset (E e)) (hS : S.Nonempty) :
    spanDim S + 1 ≤ S.card := by
  classical
  have hpos : 1 ≤ S.card := Finset.one_le_card.mpr hS
  have hd := finrank_vectorSpan_image_finset_le ℝ id S
    (Nat.sub_add_cancel hpos).symm
  rw [Finset.image_id] at hd
  unfold spanDim
  omega

theorem simplex_count_of_card_eq (hlower : SimplexVolumeLower) {e : ℕ}
    (L : FullLat e) (a : E e) (S : Finset (E e)) (hcoset : InCoset L a S)
    (hspan : spanDim S = e) (hcard : S.card = e + 1) :
    (S.card : ℝ) ≤ (e.factorial : ℝ) * volHull S / L.det + (e : ℝ) := by
  classical
  let q : S ≃ Fin (e + 1) := Finset.equivFinOfCardEq hcard
  let v : Fin (e + 1) → E e := fun i => (q.symm i : E e)
  have hpoints : simplexPoints v = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact (q.symm i).property
    · intro hx
      exact Finset.mem_image.mpr ⟨q ⟨x, hx⟩, Finset.mem_univ _, by simp [v]⟩
  have hrange : Set.range v = (S : Set (E e)) := by
    rw [← hpoints]
    simp only [simplexPoints, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hind : AffineIndependent ℝ v := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ v
      (by simp : Fintype.card (Fin (e + 1)) = e + 1)).mpr
    rw [hrange]
    exact hspan
  have hvol := hlower e L a v (fun i => hcoset _ (q.symm i).property) hind
  rw [hpoints] at hvol
  have hdet : 0 < L.det := ZLattice.covolume_pos L.carrier volume
  have hfact : 0 < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
  have hone : (1 : ℝ) ≤ (e.factorial : ℝ) * volHull S / L.det := by
    apply (le_div_iff₀ hdet).mpr
    have h := (div_le_iff₀ hfact).mp hvol
    nlinarith
  rw [hcard, Nat.cast_add, Nat.cast_one]
  linarith only [hone]

theorem simplexCount (hgain : VertexRemovalGain) (_hpyramid : PyramidVolume)
    (_hspacing : LayerSpacing) (hlower : SimplexVolumeLower) (hexposed : ExposedPoint)
    (_hzero : CountDim0) (_hone : CountDim1) (e : ℕ) : SimplexCount e := by
  classical
  intro he _he4 L a S hcoset hspan
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    rw [← hn]
    have hS : S.Nonempty := by
      by_contra h
      have hempty := Finset.not_nonempty_iff_eq_empty.mp h
      rw [hempty] at hspan
      unfold spanDim at hspan
      rw [Finset.coe_empty, vectorSpan_empty, finrank_bot] at hspan
      omega
    have hcard := dimension_add_one_le_card S hS
    rw [hspan] at hcard
    by_cases hterminal : S.card = e + 1
    · exact simplex_count_of_card_eq hlower L a S hcoset hspan hterminal
    · obtain ⟨v, hv, hvA⟩ := exists_exposed_erase_affineSpan_eq hexposed S
        (by omega)
      have hspanB : spanDim (S.erase v) = e := by
        unfold spanDim
        rw [← direction_affineSpan, hvA, direction_affineSpan]
        exact hspan
      have hcosetB : InCoset L a (S.erase v) :=
        fun x hx => hcoset x (Finset.mem_of_mem_erase hx)
      have herase := Finset.card_erase_of_mem hv.1
      have hcountB := ih (S.erase v).card (by omega) (S.erase v) hcosetB hspanB rfl
      have hvol := hgain e he L a S v hcoset hv hspanB
      have hdet : 0 < L.det := ZLattice.covolume_pos L.carrier volume
      have hfact : 0 < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
      have hstep : (e.factorial : ℝ) * volHull (S.erase v) / L.det + 1 ≤
          (e.factorial : ℝ) * volHull S / L.det := by
        have hscaled := mul_le_mul_of_nonneg_left hvol hfact.le
        have hcancel : (e.factorial : ℝ) * (L.det / (e.factorial : ℝ)) = L.det :=
          mul_div_cancel₀ _ (ne_of_gt hfact)
        rw [mul_add, hcancel] at hscaled
        have h := div_le_div_of_nonneg_right hscaled hdet.le
        simpa only [add_div, div_self (ne_of_gt hdet)] using h
      have hcardR : (S.card : ℝ) = ((S.erase v).card : ℝ) + 1 := by
        have hnat : S.card = (S.erase v).card + 1 := by omega
        exact_mod_cast hnat
      rw [hcardR]
      linarith only [hcountB, hstep]

end Praxis.Algebra.Point
