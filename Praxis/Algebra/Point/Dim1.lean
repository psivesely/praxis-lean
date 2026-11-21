import Praxis.Algebra.Point.Definitions
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

noncomputable section

open MeasureTheory Module

open scoped Pointwise

namespace Praxis.Algebra.Point

theorem integer_card_le_hull_length (T : Finset ℤ) (hT : T.Nonempty) :
    (T.card : ℝ) ≤ (volume (convexHull ℝ ((fun z : ℤ => (z : ℝ)) '' (T : Set ℤ)))).toReal + 1 := by
  let m := T.min' hT
  let M := T.max' hT
  have hm : m ∈ T := T.min'_mem hT
  have hM : M ∈ T := T.max'_mem hT
  have hle : m ≤ M := T.min'_le M hM
  have hsub : T ⊆ Finset.Icc m M := by
    intro z hz
    exact Finset.mem_Icc.mpr ⟨T.min'_le z hz, T.le_max' z hz⟩
  have hcard : (T.card : ℝ) ≤ (M : ℝ) + 1 - m := by
    have hc := Finset.card_le_card hsub
    have hi := Int.card_Icc_of_le m M (by omega)
    have hi' : ((Finset.Icc m M).card : ℝ) = (M : ℝ) + 1 - m := by exact_mod_cast hi
    exact (Nat.cast_le.mpr hc).trans_eq hi'
  have hh : convexHull ℝ ((fun z : ℤ => (z : ℝ)) '' (T : Set ℤ)) =
      Set.Icc (m : ℝ) (M : ℝ) := by
    apply Set.Subset.antisymm
    · apply convexHull_min _ (convex_Icc _ _)
      rintro _ ⟨z, hz, rfl⟩
      change (m : ℝ) ≤ (z : ℝ) ∧ (z : ℝ) ≤ (M : ℝ)
      exact ⟨Int.cast_le.mpr (T.min'_le z hz), Int.cast_le.mpr (T.le_max' z hz)⟩
    · rw [← segment_eq_Icc (by exact_mod_cast hle : (m : ℝ) ≤ M)]
      exact segment_subset_convexHull ⟨m, hm, rfl⟩ ⟨M, hM, rfl⟩
  rw [hh, Real.volume_Icc, ENNReal.toReal_ofReal (by exact_mod_cast sub_nonneg.mpr hle)]
  linarith

end Praxis.Algebra.Point

namespace Praxis.Algebra.Point

theorem countDim1 : CountDim1 := by
  classical
  intro L a S hcos hdim
  let : Module.Free ℤ L.carrier := ZLattice.module_free ℝ L.carrier
  let : Module.Finite ℤ L.carrier := ZLattice.module_finite ℝ L.carrier
  have hrank : Module.finrank ℤ L.carrier = 1 := by
    rw [ZLattice.rank ℝ L.carrier]
    exact finrank_euclideanSpace_fin
  let b : Basis (Fin 1) ℤ L.carrier :=
    (Module.finBasis ℤ L.carrier).reindex (finCongr hrank)
  let f : E 1 ≃ₗ[ℝ] (Fin 1 → ℝ) := (b.ofZLatticeBasis ℝ).equivFun
  let e : (Fin 1 → ℝ) ≃ₗ[ℝ] ℝ := LinearEquiv.funUnique (Fin 1) ℝ ℝ
  let p : E 1 ≃ᵃ[ℝ] ℝ :=
    (AffineEquiv.constVAdd ℝ (E 1) (-a)).trans (f.trans e).toAffineEquiv
  have hp (x : E 1) : p x = f (x - a) 0 := by
    simp [p, e, LinearEquiv.funUnique_apply, sub_eq_add_neg, add_comm]
  let T : Finset ℤ := S.image (fun x => ⌊p x⌋)
  have hint (x : E 1) (hx : x ∈ S) : (⌊p x⌋ : ℝ) = p x := by
    have hcoord : p x = (b.repr ⟨x - a, hcos x hx⟩ 0 : ℝ) := by
      rw [hp]
      exact b.ofZLatticeBasis_repr_apply ℝ L.carrier ⟨x - a, hcos x hx⟩ 0
    rw [hcoord, Int.floor_intCast]
  have himage : (fun z : ℤ => (z : ℝ)) '' (T : Set ℤ) = p '' (S : Set (E 1)) := by
    simp only [T, Finset.coe_image, Set.image_image]
    apply Set.image_congr
    intro x hx
    exact hint x hx
  have hcard : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    apply p.injective
    rw [← hint x hx, ← hint y hy]
    exact congrArg (fun z : ℤ => (z : ℝ)) hxy
  have hS : S.Nonempty := by
    by_contra hs
    have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst S
    unfold spanDim at hdim
    rw [Finset.coe_empty, vectorSpan_empty] at hdim
    simp at hdim
  have hT : T.Nonempty := hS.image _
  have hcount := integer_card_le_hull_length T hT
  have hhull := p.toAffineMap.image_convexHull (S : Set (E 1))
  change p '' convexHull ℝ (S : Set (E 1)) = convexHull ℝ (p '' (S : Set (E 1))) at hhull
  rw [hcard, himage, ← hhull] at hcount
  have hvolume : volume (p '' convexHull ℝ (S : Set (E 1))) =
      volume (convexHull ℝ (S : Set (E 1))) / ENNReal.ofReal L.det := by
    let A : Set (E 1) := -a +ᵥ convexHull ℝ (S : Set (E 1))
    have hA : IsCompact A :=
      (S.finite_toSet.isCompact_convexHull ℝ).vadd (-a)
    have hfA : IsCompact (f '' A) := hA.image f.toLinearMap.continuous_of_finiteDimensional
    have hevol : volume (e '' (f '' A)) = volume (f '' A) := by
      change volume ((MeasurableEquiv.funUnique (Fin 1) ℝ) '' (f '' A)) = _
      rw [MeasurableEquiv.image_eq_preimage_symm]
      exact ((volume_preserving_funUnique (Fin 1) ℝ).symm _).measure_preimage
        hfA.measurableSet.nullMeasurableSet
    have hnorm := ZLattice.volume_image_eq_volume_div_covolume' L.carrier b
      hA.measurableSet.nullMeasurableSet
    have hpimage : p '' convexHull ℝ (S : Set (E 1)) = e '' (f '' A) := by
      rw [show A = (fun x : E 1 => -a +ᵥ x) '' convexHull ℝ (S : Set (E 1)) from
        Set.image_vadd.symm, Set.image_image, Set.image_image]
      rfl
    rw [hpimage, hevol, hnorm]
    change volume (-a +ᵥ convexHull ℝ (S : Set (E 1))) / _ = _
    rw [measure_vadd]
    rfl
  have hdet : 0 ≤ L.det := by
    unfold FullLat.det
    exact (ZLattice.covolume_pos L.carrier volume).le
  rw [hvolume, ENNReal.toReal_div, ENNReal.toReal_ofReal hdet] at hcount
  exact hcount

end Praxis.Algebra.Point
