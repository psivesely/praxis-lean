import Praxis.Algebra.Point.Definitions
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Module MeasureTheory MeasureTheory.Measure

namespace Praxis.Algebra.Point

namespace VertexGain

section Supporting

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem exists_feasible (S : Finset V) (hS : S.Nonempty)
    (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ g : V →ₗ[ℝ] ℝ, ∀ x ∈ S, 1 ≤ g x := by
  obtain ⟨x, hx, hmin⟩ := S.exists_min_image f hS
  refine ⟨(f x)⁻¹ • f, fun y hy => ?_⟩
  change 1 ≤ (f x)⁻¹ * f y
  rw [inv_mul_eq_div, le_div_iff₀ (hf x hx)]
  simpa using hmin y hy

theorem increase_tight (S : Finset V) (f g : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ S, 1 ≤ f x)
    (hzero : ∀ x ∈ S, f x = 1 → g x = 0)
    (hneg : ∃ x ∈ S, g x < 0) :
    ∃ k : V →ₗ[ℝ] ℝ, (∀ x ∈ S, 1 ≤ k x) ∧
      S.filter (fun x => f x = 1) ⊂ S.filter (fun x => k x = 1) := by
  classical
  let N := S.filter (fun x => g x < 0)
  have hN : N.Nonempty := by
    obtain ⟨x, hx, hgx⟩ := hneg
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hgx⟩⟩
  obtain ⟨z, hz, hmin⟩ := N.exists_min_image (fun x => (f x - 1) / (-g x)) hN
  have hzS := (Finset.mem_filter.mp hz).1
  have hgz : 0 < -g z := neg_pos.mpr (Finset.mem_filter.mp hz).2
  let t := (f z - 1) / (-g z)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hf z hzS)) hgz.le
  let k := f + t • g
  have hk : ∀ x ∈ S, 1 ≤ k x := by
    intro x hx
    change 1 ≤ f x + t * g x
    by_cases hgx : g x < 0
    · have hb := hmin x (Finset.mem_filter.mpr ⟨hx, hgx⟩)
      change t ≤ (f x - 1) / (-g x) at hb
      have hb' := (le_div_iff₀ (neg_pos.mpr hgx)).mp hb
      nlinarith
    · have hp : 0 ≤ t * g x := mul_nonneg ht (le_of_not_gt hgx)
      linarith [hf x hx]
  have hkeep : ∀ x ∈ S, f x = 1 → k x = 1 := by
    intro x hx hfx
    change f x + t * g x = 1
    rw [hfx, hzero x hx hfx, mul_zero, add_zero]
  have hkz : k z = 1 := by
    change f z + ((f z - 1) / (-g z)) * g z = 1
    field_simp [ne_of_lt (Finset.mem_filter.mp hz).2]
    ring
  refine ⟨k, hk, Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩⟩
  · intro x hx
    obtain ⟨hxS, hfx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxS, hkeep x hxS hfx⟩
  · intro heq
    have hzT : z ∈ S.filter (fun x => f x = 1) :=
      heq.symm ▸ Finset.mem_filter.mpr ⟨hzS, hkz⟩
    have hfz : f z = 1 := (Finset.mem_filter.mp hzT).2
    have := hzero z hzS hfz
    linarith

theorem exists_spanning_tight (S : Finset V) (hS : S.Nonempty)
    (hspan : Submodule.span ℝ (S : Set V) = ⊤)
    (f₀ : V →ₗ[ℝ] ℝ) (hpos : ∀ x ∈ S, 0 < f₀ x) :
    ∃ f : V →ₗ[ℝ] ℝ, (∀ x ∈ S, 1 ≤ f x) ∧
      Submodule.span ℝ ((S.filter (fun x => f x = 1)) : Set V) = ⊤ := by
  classical
  let A := S.powerset.filter (fun T =>
    ∃ f : V →ₗ[ℝ] ℝ, (∀ x ∈ S, 1 ≤ f x) ∧ T = S.filter (fun x => f x = 1))
  have hA : A.Nonempty := by
    obtain ⟨f, hf⟩ := exists_feasible S hS f₀ hpos
    refine ⟨S.filter (fun x => f x = 1), Finset.mem_filter.mpr ⟨?_, f, hf, rfl⟩⟩
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  obtain ⟨T, hT, hmax⟩ := A.exists_max_image Finset.card hA
  obtain ⟨f, hf, rfl⟩ := (Finset.mem_filter.mp hT).2
  refine ⟨f, hf, ?_⟩
  by_contra hproper
  obtain ⟨g, hg, hker⟩ :=
    (Submodule.span ℝ ((S.filter (fun x => f x = 1)) : Set V)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hproper)
  have hex : ∃ x ∈ S, g x ≠ 0 := by
    by_contra! h
    have hle : Submodule.span ℝ (S : Set V) ≤ LinearMap.ker g :=
      Submodule.span_le.mpr h
    rw [hspan] at hle
    apply hg
    ext x
    exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ V))
  have hzero : ∀ x ∈ S, f x = 1 → g x = 0 := by
    intro x hx hfx
    exact hker (Submodule.subset_span (Finset.mem_filter.mpr ⟨hx, hfx⟩))
  have hstep : ∃ k : V →ₗ[ℝ] ℝ, (∀ x ∈ S, 1 ≤ k x) ∧
      S.filter (fun x => f x = 1) ⊂ S.filter (fun x => k x = 1) := by
    obtain ⟨x, hx, hgx⟩ := hex
    obtain hgx | hgx := lt_or_gt_of_ne hgx
    · exact increase_tight S f g hf hzero ⟨x, hx, hgx⟩
    · exact increase_tight S f (-g) hf (by simpa using hzero) ⟨x, hx, by simpa⟩
  obtain ⟨k, hk, hstrict⟩ := hstep
  have hkA : S.filter (fun x => k x = 1) ∈ A := by
    refine Finset.mem_filter.mpr ⟨?_, k, hk, rfl⟩
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  exact (not_lt_of_ge (hmax _ hkA)) (Finset.card_lt_card hstrict)

end Supporting

theorem span_sub_eq_top {e : ℕ} (S : Finset (E e)) (v : E e)
    (hS : spanDim S = e) :
    Submodule.span ℝ ((S.image (fun x => x - v)) : Set (E e)) = ⊤ := by
  classical
  have hfull : vectorSpan ℝ (S : Set (E e)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa [spanDim] using hS)
  apply top_unique
  rw [← hfull, vectorSpan_def]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hx' : x - v ∈ Submodule.span ℝ ((S.image (fun x => x - v)) : Set (E e)) :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hy' : y - v ∈ Submodule.span ℝ ((S.image (fun x => x - v)) : Set (E e)) :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  convert Submodule.sub_mem _ hx' hy' using 1
  simp [vsub_eq_sub]

theorem exists_visible_simplex {e : ℕ} (he : 1 ≤ e)
    (S : Finset (E e)) (v : E e) (hv : IsExposed S v)
    (hspan : spanDim (S.erase v) = e) :
    ∃ (p : Fin (e + 1) → E e) (f : E e →ₗ[ℝ] ℝ),
      p 0 = v ∧ AffineIndependent ℝ p ∧
      (∀ i : Fin e, p i.succ ∈ S.erase v ∧ f (p i.succ) = f v + 1) ∧
      (∀ w ∈ S.erase v, f v + 1 ≤ f w) := by
  classical
  have hne : (S.erase v).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty] at hspan
    dsimp only [spanDim] at hspan
    rw [Finset.coe_empty, vectorSpan_empty, finrank_bot] at hspan
    omega
  obtain ⟨f₀, hf₀⟩ := hv.2
  let T := (S.erase v).image (fun x => x - v)
  have hpos : ∀ x ∈ T, 0 < (-f₀) x := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    have hw' := Finset.mem_erase.mp hw
    have hlt := hf₀ w hw'.2 hw'.1
    simp only [LinearMap.neg_apply, map_sub]
    linarith
  obtain ⟨f, hf, htight⟩ := exists_spanning_tight T (hne.image _)
    (span_sub_eq_top (S.erase v) v hspan) (-f₀) hpos
  let b₀ := Basis.ofSpan htight.ge
  let b : Basis (Fin e) ℝ (E e) :=
    b₀.reindex (b₀.indexEquiv (EuclideanSpace.basisFun (Fin e) ℝ).toBasis)
  have hb : ∀ i, b i ∈ T ∧ f (b i) = 1 := by
    intro i
    simp only [b, Basis.reindex_apply]
    exact Finset.mem_filter.mp (Basis.ofSpan_subset htight.ge
      (Set.mem_range.mpr ⟨(b₀.indexEquiv
        (EuclideanSpace.basisFun (Fin e) ℝ).toBasis).symm i, rfl⟩))
  let p : Fin (e + 1) → E e := Fin.cases v (fun i => b i + v)
  have hp0 : p 0 = v := rfl
  have hps : ∀ i : Fin e, p i.succ ∈ S.erase v ∧ f (p i.succ) = f v + 1 := by
    intro i
    obtain ⟨w, hw, hwb⟩ := Finset.mem_image.mp (hb i).1
    have heq : p i.succ = w := by simp [p, ← hwb]
    refine ⟨heq.symm ▸ hw, ?_⟩
    change f (b i + v) = f v + 1
    rw [map_add, (hb i).2, add_comm]
  have hptop : vectorSpan ℝ (Set.range p) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hi := vsub_mem_vectorSpan ℝ (Set.mem_range_self i.succ : p i.succ ∈ Set.range p)
      (Set.mem_range_self (0 : Fin (e + 1)) : p 0 ∈ Set.range p)
    simpa [p, vsub_eq_sub] using hi
  have hpind : AffineIndependent ℝ p := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ p
      (by simp : Fintype.card (Fin (e + 1)) = e + 1)).mpr
    rw [hptop]
    simp
  refine ⟨p, f, hp0, hpind, hps, ?_⟩
  intro w hw
  have h := hf (w - v) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  rw [map_sub] at h
  linarith

theorem volHull_add_le_of_separated {e : ℕ} (S T U : Finset (E e))
    (hSU : S ⊆ U) (hTU : T ⊆ U) (f : E e →ₗ[ℝ] ℝ) (c : ℝ)
    (b v : E e) (hb : f b = c) (hv : f v ≠ c)
    (hS : ∀ x ∈ S, c ≤ f x) (hT : ∀ x ∈ T, f x ≤ c) :
    volHull S + volHull T ≤ volHull U := by
  let H : AffineSubspace ℝ (E e) := AffineSubspace.mk' b (LinearMap.ker f)
  have hH : H ≠ ⊤ := by
    intro heq
    have hmem : v ∈ H := heq.symm ▸ (show v ∈ (⊤ : AffineSubspace ℝ (E e)) by trivial)
    change f (v - b) = 0 at hmem
    rw [map_sub, hb, sub_eq_zero] at hmem
    exact hv hmem
  have hleft : convexHull ℝ (S : Set (E e)) ⊆ {x | c ≤ f x} :=
    convexHull_min hS (convex_halfSpace_ge f.isLinear c)
  have hright : convexHull ℝ (T : Set (E e)) ⊆ {x | f x ≤ c} :=
    convexHull_min hT (convex_halfSpace_le f.isLinear c)
  have hnull : volume (convexHull ℝ (S : Set (E e)) ∩
      convexHull ℝ (T : Set (E e))) = 0 := by
    refine measure_mono_null (t := (H : Set (E e))) ?_
      (addHaar_affineSubspace volume H hH)
    intro x hx
    change f (x - b) = 0
    rw [map_sub, hb, sub_eq_zero]
    exact le_antisymm (hright hx.2) (hleft hx.1)
  have hfiniteS : volume (convexHull ℝ (S : Set (E e))) ≠ ⊤ :=
    (S.finite_toSet.isCompact_convexHull ℝ).measure_lt_top.ne
  have hfiniteT : volume (convexHull ℝ (T : Set (E e))) ≠ ⊤ :=
    (T.finite_toSet.isCompact_convexHull ℝ).measure_lt_top.ne
  have hfiniteU : volume (convexHull ℝ (U : Set (E e))) ≠ ⊤ :=
    (U.finite_toSet.isCompact_convexHull ℝ).measure_lt_top.ne
  have hsum : volume (convexHull ℝ (S : Set (E e))) +
      volume (convexHull ℝ (T : Set (E e))) ≤
      volume (convexHull ℝ (U : Set (E e))) := by
    rw [← measure_union₀ ((convex_convexHull ℝ (T : Set (E e))).nullMeasurableSet
      (μ := volume)) hnull]
    exact measure_mono (Set.union_subset (convexHull_mono hSU) (convexHull_mono hTU))
  have hreal := ENNReal.toReal_mono hfiniteU hsum
  rw [ENNReal.toReal_add hfiniteS hfiniteT] at hreal
  exact hreal

theorem vertexRemovalGain_of_simplexVolumeLower
    (hlower : SimplexVolumeLower) : VertexRemovalGain := by
  classical
  intro e he L a S v hcoset hv hspan
  obtain ⟨p, f, hp0, hpind, hps, hf⟩ := exists_visible_simplex he S v hv hspan
  have hpS : ∀ i, p i ∈ S := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hp0]
      exact hv.1
    · exact Finset.mem_of_mem_erase (hps j).1
  have hsimplex : simplexPoints p ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hpS i
  have hbound : ∀ x ∈ simplexPoints p, f x ≤ f v + 1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hp0]
      linarith
    · exact (hps j).2.le
  let j : Fin e := ⟨0, he⟩
  have hadd := volHull_add_le_of_separated (S.erase v) (simplexPoints p) S
    (Finset.erase_subset _ _) hsimplex f (f v + 1) (p j.succ) v
    (hps j).2 (by linarith) hf hbound
  have hl := hlower e L a p (fun i => hcoset (p i) (hpS i)) hpind
  exact (add_le_add_right hl _).trans hadd

theorem vertexRemovalGain (hlower : SimplexVolumeLower)
    (_hexposed : ExposedPoint) : VertexRemovalGain :=
  vertexRemovalGain_of_simplexVolumeLower hlower

end VertexGain

end Praxis.Algebra.Point
