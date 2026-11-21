import Praxis.Algebra.Trans.ChartModel
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Trans.Definitions

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open MeasureTheory

open Praxis.Algebra.Point

namespace Praxis.Algebra.Trans

namespace ChartCountProof

variable {r q : ℕ}

def projectLinear (B : ChartBasis r q) : (Fin (r+1) → ℝ) →ₗ[ℝ] E (r-q+1) where
  toFun := B.project
  map_add' := by
    intro x y; ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [ChartBasis.project]
  map_smul' := by
    intro s x; ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [ChartBasis.project]

theorem point_fibre (T : ChartData r q) {w : Fin (r+1) → ℤ} (hw : w ∈ T.S) :
    (realMatrix T.K).transpose.mulVec (fun i => (w i : ℝ)) = T.target :=
  (T.affine_span _).mp (mem_affineSpan ℝ ⟨w, hw, rfl⟩)

theorem pivot_unit (B : ChartBasis r q) (hp : B.HasPivot) :
    IsUnit B.pivotReal.transpose.det := by
  rw [Matrix.det_transpose]
  have heq : B.pivotReal.det = (B.a : ℝ) := by
    change ((B.U.submatrix B.pivot id).map (Int.castRingHom ℝ)).det = _
    exact (Int.cast_det _).symm
  rw [heq]
  exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hp)

theorem normal_split (B : ChartBasis r q) (w : Fin (r+1) → ℝ) :
    (realMatrix B.K).transpose.mulVec w =
      B.pivotReal.transpose.mulVec (fun i => w (B.pivot i).castSucc) +
      B.freeReal.transpose.mulVec (fun i => w (B.free i).castSucc) +
      (fun j => (B.v j : ℝ) * w (Fin.last r)) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply]
  rw [Fin.sum_univ_castSucc]
  congr 1
  have h := Equiv.sum_comp B.rows
    (fun i : Fin r => (realMatrix B.K) i.castSucc j * w i.castSucc)
  rw [Fintype.sum_sum_type] at h
  simpa [ChartBasis.pivotReal, ChartBasis.freeReal, ChartBasis.U, ChartBasis.pivot,
    ChartBasis.free, oldBlock, realMatrix] using h.symm

theorem reconstruct_project (T : ChartGeometry r q) (hp : T.HasPivot)
    (w : Fin (r+1) → ℝ)
    (hw : (realMatrix T.K).transpose.mulVec w = T.target) :
    T.reconstruct (T.project w) = fun i => w i.castSucc := by
  have hs := normal_split T.toChartBasis w
  rw [hw] at hs
  have heq : T.pivotReal.transpose.mulVec (fun i => w (T.pivot i).castSucc) =
      T.target - T.freeReal.transpose.mulVec (fun i => w (T.free i).castSucc) -
      (fun j => (T.v j : ℝ) * w (Fin.last r)) := by
    rw [hs]; abel
  have hvx : (fun j => (T.v j : ℝ) * w (Fin.last r)) =
      w (Fin.last r) • (fun j => (T.v j : ℝ)) := by
    ext j; simp [mul_comm]
  rw [hvx] at heq
  have hi := congrArg (T.pivotReal.transpose⁻¹.mulVec) heq
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (pivot_unit _ hp),
    Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul] at hi
  ext i
  obtain ⟨k, rfl⟩ := T.rows.surjective i
  cases k with
  | inl k =>
    have hA : T.A.mulVec (fun j => w (T.free j).castSucc) (T.rows (Sum.inl k)) =
        -((T.pivotReal.transpose⁻¹ * T.freeReal.transpose).mulVec
          (fun j => w (T.free j).castSucc) k) := by
      simp [Matrix.mulVec, dotProduct, ChartBasis.A, Finset.sum_neg_distrib]
    have hk := congrFun hi k
    rw [Matrix.mulVec_mulVec] at hk
    simpa [ChartGeometry.reconstruct, ChartBasis.project, ChartBasis.A, ChartBasis.b,
      ChartBasis.c, ChartBasis.pivot, hA, Matrix.sub_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_add, Matrix.neg_mulVec, Matrix.mulVec_smul,
      sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
      add_assoc] using hk.symm
  | inr k =>
    simp [ChartGeometry.reconstruct, ChartBasis.project, ChartBasis.A, ChartBasis.b,
      ChartBasis.c, ChartBasis.free, Matrix.mulVec, dotProduct]

theorem sectionVolume_top {e : ℕ} (D : Set (E e)) :
    sectionVolume D 0 (⊤ : Submodule ℝ (E e)) = ChartGeometry.bodyVolume D := by
  let chart : (⊤ : Submodule ℝ (E e)) ≃ₗᵢ[ℝ] E e :=
    LinearIsometryEquiv.ofTop (E e) _ rfl
  have h := chart.measurePreserving.measure_preimage_emb
    chart.toHomeomorph.measurableEmbedding D
  have heq : {w : (⊤ : Submodule ℝ (E e)) | (0 : E e) + (w : E e) ∈ D} =
      chart ⁻¹' D := by ext w; simp [chart]
  unfold sectionVolume ChartGeometry.bodyVolume
  rw [heq, h]

theorem sectionCount3_fullRank (hc : SectionCount3) (L : FullLat 3) (b : E 3)
    (D : Set (E 3)) (S : Finset (E 3)) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hcontained : (S : Set (E 3)) ⊆ D)
    (hcoset : InCoset L b S) (hdim : spanDim S = 3) :
    (S.card : ℝ) ≤ 81 * ChartGeometry.bodyVolume (differenceBody D) / L.det := by
  classical
  let chart : (⊤ : Submodule ℝ (E 3)) ≃ₗᵢ[ℝ] E 3 :=
    LinearIsometryEquiv.ofTop (E 3) _ rfl
  let lift : E 3 → (⊤ : Submodule ℝ (E 3)) := fun x => ⟨x, Submodule.mem_top⟩
  have hi : Function.Injective lift := fun _ _ h => congrArg Subtype.val h
  have himage : (S.image lift).image chart = S := by
    rw [Finset.image_image]
    change S.image id = S
    exact Finset.image_id
  have h := (hc 3 (by decide) ⊤ chart L 0 b D (S.image lift) hcompact hconvex
    (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact (zero_add y).symm ▸ hcontained hy)
    (by rw [himage]; exact hcoset) (by rw [himage]; exact hdim)).1
  rw [Finset.card_image_of_injective _ hi, sectionVolume_top] at h
  exact h

theorem cast_project (B : ChartBasis r q) (w : Fin (r+1) → ℤ) :
    B.project (fun i => (w i : ℝ)) = ChartBasis.castCoordinates _ (B.projectZ w) := by
  ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [ChartBasis.project, ChartBasis.projectZ, ChartBasis.castCoordinates]

theorem chartPoints_card (hindex : ProjectedKernelIndex) (T : ChartData r q) :
    T.chartPoints.card = T.S.card := by
  classical
  obtain ⟨anchor, ha⟩ := T.nonempty
  have hb := (hindex r q T.toChartBasis T.dimensionCase T.primitive T.pivot_ne_zero).2.2.2.2
    T.target anchor (point_fibre T ha)
  apply Finset.card_image_iff.mpr
  intro x hx y hy heq
  apply hb.injOn (point_fibre T hx) (point_fibre T hy)
  change T.project (fun i => (x i : ℝ)) = T.project (fun i => (y i : ℝ)) at heq
  rw [cast_project, cast_project] at heq
  ext i
  have hi := congrArg (fun z : E (r-q+1) => z i) heq
  change (T.projectZ x i : ℝ) = (T.projectZ y i : ℝ) at hi
  exact_mod_cast hi

theorem chartPoints_span (hindex : ProjectedKernelIndex) (T : ChartData r q) :
    spanDim T.chartPoints = r-q+1 := by
  classical
  obtain ⟨anchor, ha⟩ := T.nonempty
  obtain ⟨_, _, hfull, _, hfibre⟩ :=
    hindex r q T.toChartBasis T.dimensionCase T.primitive T.pivot_ne_zero
  let V := vectorSpan ℝ (T.chartPoints : Set (E (r-q+1)))
  have hle : T.realGamma ≤ V.restrictScalars ℤ := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hproj⟩ := (hfibre T.target anchor (point_fibre T ha)).surjOn
      (show z + T.projectZ anchor - T.projectZ anchor ∈ T.Gamma by simpa using hz)
    have hpoint (v : Fin (r+1) → ℝ)
        (hv : (realMatrix T.K).transpose.mulVec v = T.target) :
        T.project v ∈ affineSpan ℝ (T.chartPoints : Set (E (r-q+1))) := by
      have hmem := AffineSubspace.mem_map_of_mem (f := (projectLinear T.toChartBasis).toAffineMap)
        ((T.affine_span v).mpr hv)
      rw [AffineSubspace.map_span] at hmem
      have he : (T.chartPoints : Set (E (r-q+1))) =
          (projectLinear T.toChartBasis).toAffineMap ''
            (Set.image (fun z : Fin (r+1) → ℤ => fun i => (z i : ℝ))
              (T.S : Set (Fin (r+1) → ℤ))) := by
        simp only [ChartData.chartPoints, Finset.coe_image, Set.image_image]
        rfl
      rw [he]
      exact hmem
    have hd := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (hpoint _ hw) (hpoint _ (point_fibre T ha))
    change T.project (fun i => (w i : ℝ)) - T.project (fun i => (anchor i : ℝ)) ∈ V at hd
    rw [cast_project, cast_project, hproj, map_add, add_sub_cancel_right] at hd
    exact hd
  have hv : V = ⊤ := by
    apply top_unique
    rw [← hfull]
    exact Submodule.span_le.mpr hle
  change Module.finrank ℝ V = r-q+1
  rw [hv, finrank_top, finrank_euclideanSpace_fin]

theorem chartPoints_coset (hindex : ProjectedKernelIndex) (T : ChartData r q)
    (L : FullLat (r-q+1)) (hL : L.carrier = T.realGamma)
    (anchor : Fin (r+1) → ℤ) (ha : anchor ∈ T.S) :
    InCoset L (T.project (fun i => (anchor i : ℝ))) T.chartPoints := by
  have hb := (hindex r q T.toChartBasis T.dimensionCase T.primitive T.pivot_ne_zero).2.2.2.2
    T.target anchor (point_fibre T ha)
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  rw [hL, cast_project, cast_project, ← map_sub]
  exact ⟨T.projectZ w - T.projectZ anchor, hb.mapsTo (point_fibre T hw), rfl⟩

theorem chartPoints_contained (hshear : ShearedCylinderEnvelope) (T : ChartData r q) :
    (T.chartPoints : Set (E (r-q+1))) ⊆ T.envelope := by
  have hs := (hshear r q T.toChartGeometry T.dimensionCase T.pivot_ne_zero
    T.positive T.radius_pos T.interval_order).2.2.1
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  apply hs
  have hr := reconstruct_project T.toChartGeometry T.pivot_ne_zero _ (point_fibre T hw)
  change (T.project (fun i => (w i : ℝ))) (Fin.last (r-q)) ∈
      Set.Icc T.lower T.upper ∧
    quadratic T.Sigma⁻¹ (T.reconstruct (T.project (fun i => (w i : ℝ))) - T.mu) ≤ T.R^2
  rw [hr]
  simpa [ChartBasis.project] using T.contained w hw

theorem volHull_le_bodyVolume {e : ℕ} (S : Finset (E e)) (D : Set (E e))
    (hc : IsCompact D) (hv : Convex ℝ D) (hs : (S : Set (E e)) ⊆ D) :
    volHull S ≤ ChartGeometry.bodyVolume D :=
  measureReal_mono (convexHull_min hs hv) hc.measure_ne_top

theorem chartCountEnvelope (hindex : ProjectedKernelIndex)
    (hshear : ShearedCylinderEnvelope) {r q : ℕ} : ChartCountEnvelope r q := by
  classical
  intro hp hs T
  obtain ⟨_, _, _, ⟨L, hL, _, hdet⟩, _⟩ :=
    hindex r q T.toChartBasis T.dimensionCase T.primitive T.pivot_ne_zero
  obtain ⟨anchor, ha⟩ := T.nonempty
  have hcoset := chartPoints_coset hindex T L hL anchor ha
  have hdim := chartPoints_span hindex T
  have hcontained := chartPoints_contained hshear T
  obtain ⟨_, _, _, _, _, hcompact, hconvex, _, _, hdiff⟩ :=
    hshear r q T.toChartGeometry T.dimensionCase T.pivot_ne_zero T.positive
      T.radius_pos T.interval_order
  have hpos : 0 < L.det := ZLattice.covolume_pos L.carrier volume
  have hcard := chartPoints_card hindex T
  rcases T.dimensionCase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hc := hp L _ T.chartPoints hcoset hdim
    have hv := volHull_le_bodyVolume T.chartPoints T.envelope hcompact hconvex hcontained
    rw [hcard] at hc
    calc
      _ ≤ 6 * volHull T.chartPoints / L.det := hc
      _ ≤ 6 * ChartGeometry.bodyVolume T.envelope / L.det :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by norm_num)) hpos.le
      _ = _ := by rw [hdet]; norm_num
  · have hc := hp L _ T.chartPoints hcoset hdim
    have hv := volHull_le_bodyVolume T.chartPoints T.envelope hcompact hconvex hcontained
    rw [hcard] at hc
    calc
      _ ≤ 6 * volHull T.chartPoints / L.det := hc
      _ ≤ 6 * ChartGeometry.bodyVolume T.envelope / L.det :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by norm_num)) hpos.le
      _ = _ := by rw [hdet]; norm_num
  · have hc := sectionCount3_fullRank hs L _ T.envelope T.chartPoints hcompact
      hconvex hcontained hcoset hdim
    rw [hcard, hdiff, hdet] at hc
    convert hc using 1 <;> norm_num <;> ring

theorem pivot_cancellation (hgram : ComplementaryGram) (hshear : ShearedCylinderEnvelope)
    (T : ChartData r q) :
    Real.sqrt (T.normalGram T.Sigma).det =
      |(T.a : ℝ)| * Real.sqrt T.Sigma.det * Real.sqrt (T.C T.Sigma).det := by
  have hc := (hshear r q T.toChartGeometry T.dimensionCase T.pivot_ne_zero
    T.positive T.radius_pos T.interval_order).1.det_pos
  have hg := hgram r q T.toChartBasis T.Sigma T.dimensionCase T.pivot_ne_zero T.positive
  rw [← hg, Real.sqrt_mul (mul_nonneg (sq_nonneg _) T.positive.det_pos.le),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem chartCount (hindex : ProjectedKernelIndex) (hshear : ShearedCylinderEnvelope)
    (hgram : ComplementaryGram) {r q : ℕ} : ChartCount r q := by
  intro hp hs T
  have hc := chartCountEnvelope hindex hshear hp hs T
  have hvol := (hshear r q T.toChartGeometry T.dimensionCase T.pivot_ne_zero
    T.positive T.radius_pos T.interval_order).2.2.2.2.2.2.2.2.1
  have hC := (hshear r q T.toChartGeometry T.dimensionCase T.pivot_ne_zero
    T.positive T.radius_pos T.interval_order).1.det_pos
  have ha : (T.a : ℝ) ≠ 0 := by exact_mod_cast T.pivot_ne_zero
  have hS := T.positive.det_pos
  have hcancel := pivot_cancellation hgram hshear T
  rw [hvol] at hc
  apply hc.trans_eq
  rw [hcancel]
  unfold ChartGeometry.cylinderVolume
  field_simp [abs_ne_zero.mpr ha, Real.sqrt_ne_zero'.mpr hC,
    Real.sqrt_ne_zero'.mpr hS]

theorem ballVolume_one : ChartGeometry.ballVolume 1 = 2 := by
  unfold ChartGeometry.ballVolume
  rw [InnerProductSpace.volume_closedBall_of_dim_odd (k := 0) (by simp)]
  norm_num

theorem ballVolume_two : ChartGeometry.ballVolume 2 = Real.pi := by
  unfold ChartGeometry.ballVolume
  rw [EuclideanSpace.volume_closedBall_fin_two]
  norm_num [Real.pi_pos.le]

end ChartCountProof

theorem chartCount32 (hi : ProjectedKernelIndex) (hs : ShearedCylinderEnvelope)
    (hg : ComplementaryGram) : ChartCount 3 2 := ChartCountProof.chartCount hi hs hg

theorem chartCount21 (hi : ProjectedKernelIndex) (hs : ShearedCylinderEnvelope)
    (hg : ComplementaryGram) : ChartCount 2 1 := ChartCountProof.chartCount hi hs hg

theorem chartCount31 (hi : ProjectedKernelIndex) (hs : ShearedCylinderEnvelope)
    (hg : ComplementaryGram) : ChartCount 3 1 := ChartCountProof.chartCount hi hs hg

end Praxis.Algebra.Trans
