import Praxis.Algebra.Trans.ChartModel
import Praxis.Algebra.Trans.Pullback
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.InverseBranches.IntegerLift

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

open Praxis.Algebra.Point

namespace Praxis.Algebra.Trans

theorem primitive_transpose_surjective {n q : ℕ}
    (K : Matrix (Fin n) (Fin q) ℤ) (hK : PrimitiveMatrix K) :
    Function.Surjective K.transpose.mulVec := by
  obtain ⟨L, hL⟩ := primitive_left_inverse K hK
  intro y
  refine ⟨L.transpose.mulVec y, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hL, Matrix.transpose_one,
    Matrix.one_mulVec]

namespace ChartBasis

variable {r q : ℕ} (B : ChartBasis r q)

def pivotMatrix : Matrix (Fin q) (Fin q) ℤ := (B.U.submatrix B.pivot id).transpose

def pivotLift (p : Fin q → ℤ) : Fin (r+1) → ℤ :=
  Fin.snoc (fun i => Sum.elim p (fun _ => 0) (B.rows.symm i)) 0

def freeLift (z : Fin (r-q+1) → ℤ) : Fin (r+1) → ℤ :=
  Fin.snoc (fun i => Sum.elim (fun _ => 0) (fun j => z j.castSucc) (B.rows.symm i))
    (z (Fin.last (r-q)))

theorem project_freeLift (z : Fin (r-q+1) → ℤ) : B.projectZ (B.freeLift z) = z := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [projectZ, freeLift, free]

theorem project_pivotLift (p : Fin q → ℤ) : B.projectZ (B.pivotLift p) = 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [projectZ, pivotLift, free]

theorem split_coordinates (w : Fin (r+1) → ℤ) :
    w = B.pivotLift (fun j => w (B.pivot j).castSucc) + B.freeLift (B.projectZ w) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [pivotLift, freeLift, projectZ]
  · obtain ⟨j, rfl⟩ := B.rows.surjective j
    cases j <;> simp [pivotLift, freeLift, projectZ, pivot, free]

theorem normal_pivotLift (p : Fin q → ℤ) :
    B.K.transpose.mulVec (B.pivotLift p) = B.pivotMatrix.mulVec p := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, pivotLift,
    Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
  rw [← B.rows.sum_comp]
  simp [Fintype.sum_sum_type, pivotMatrix, U, oldBlock, pivot]

def remainderMap : (Fin (r-q+1) → ℤ) →ₗ[ℤ] (Fin q → ℤ) :=
  { toFun := fun z => B.K.transpose.mulVec (B.freeLift z)
    map_add' := by
      intro x y
      have h : B.freeLift (x+y) = B.freeLift x + B.freeLift y := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [freeLift]
        · cases hrow : B.rows.symm j <;> simp [freeLift, hrow]
      rw [h, Matrix.mulVec_add]
    map_smul' := by
      intro c x
      have h : B.freeLift (c • x) = c • B.freeLift x := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [freeLift]
        · cases hrow : B.rows.symm j <;> simp [freeLift, hrow]
      change B.K.transpose.mulVec (B.freeLift (c • x)) = c • _
      rw [h, Matrix.mulVec_smul] }

theorem normal_split (w : Fin (r+1) → ℤ) :
    B.K.transpose.mulVec w =
      B.pivotMatrix.mulVec (fun j => w (B.pivot j).castSucc) +
        B.remainderMap (B.projectZ w) := by
  conv_lhs => rw [B.split_coordinates w]
  rw [Matrix.mulVec_add, B.normal_pivotLift]
  rfl

theorem gamma_iff (z : Fin (r-q+1) → ℤ) :
    z ∈ B.Gamma ↔ B.remainderMap z ∈ B.pivotMatrix.mulVecLin.range := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change B.K.transpose.mulVec w = 0 at hw
    rw [B.normal_split] at hw
    refine ⟨-(fun j => w (B.pivot j).castSucc), ?_⟩
    change B.pivotMatrix.mulVec (-(fun j => w (B.pivot j).castSucc)) = _
    rw [Matrix.mulVec_neg]
    exact neg_eq_of_add_eq_zero_right hw
  · rintro ⟨p, hp⟩
    refine ⟨B.freeLift z - B.pivotLift p, ?_, ?_⟩
    · change B.K.transpose.mulVec _ = 0
      rw [Matrix.mulVec_sub, B.normal_pivotLift]
      exact sub_eq_zero.mpr hp.symm
    · rw [map_sub]
      exact (congrArg₂ (· - ·) (B.project_freeLift z) (B.project_pivotLift p)).trans
        (sub_zero z)

def quotientMap := B.pivotMatrix.mulVecLin.range.mkQ.comp B.remainderMap

theorem quotientMap_surjective (hK : PrimitiveMatrix B.K) :
    Function.Surjective B.quotientMap := by
  intro y
  obtain ⟨y, rfl⟩ := B.pivotMatrix.mulVecLin.range.mkQ_surjective y
  obtain ⟨w, hw⟩ := primitive_transpose_surjective B.K hK y
  refine ⟨B.projectZ w, ?_⟩
  change B.pivotMatrix.mulVecLin.range.mkQ (B.remainderMap (B.projectZ w)) =
    B.pivotMatrix.mulVecLin.range.mkQ y
  rw [← hw, B.normal_split, map_add]
  have hz : B.pivotMatrix.mulVecLin.range.mkQ
      (B.pivotMatrix.mulVec (fun j => w (B.pivot j).castSucc)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [hz, zero_add]

theorem quotientMap_ker : B.quotientMap.ker = B.Gamma := by
  ext z
  change B.pivotMatrix.mulVecLin.range.mkQ (B.remainderMap z) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, B.gamma_iff]

theorem gamma_index (hK : PrimitiveMatrix B.K) (ha : B.HasPivot) :
    B.Gamma.toAddSubgroup.index = B.a.natAbs := by
  rw [← B.quotientMap_ker]
  have h := AddSubgroup.index_comap_of_surjective (⊥ : AddSubgroup
    ((Fin q → ℤ) ⧸ B.pivotMatrix.mulVecLin.range))
      (f := B.quotientMap.toAddMonoidHom) (B.quotientMap_surjective hK)
  change B.quotientMap.toAddMonoidHom.ker.index = _
  rw [show B.quotientMap.toAddMonoidHom.ker =
    (⊥ : AddSubgroup ((Fin q → ℤ) ⧸ B.pivotMatrix.mulVecLin.range)).comap
      B.quotientMap.toAddMonoidHom by rfl, h, AddSubgroup.index_bot]
  change B.pivotMatrix.mulVecLin.range.toAddSubgroup.index = _
  rw [Algebra.VectorInverse.matrix_range_index _ (by
    change (B.U.submatrix B.pivot id).transpose.det ≠ 0
    rw [Matrix.det_transpose]
    exact ha)]
  change (B.U.submatrix B.pivot id).transpose.det.natAbs = _
  rw [Matrix.det_transpose]
  rfl

theorem normal_project_injective (ha : B.HasPivot)
    {w w' : Fin (r+1) → ℤ}
    (hn : B.K.transpose.mulVec w = B.K.transpose.mulVec w')
    (hp : B.projectZ w = B.projectZ w') : w = w' := by
  have hi := Matrix.mulVec_injective_of_det_ne_zero
    (show B.pivotMatrix.det ≠ 0 by
      change (B.U.submatrix B.pivot id).transpose.det ≠ 0
      rw [Matrix.det_transpose]
      exact ha)
  have hc : (fun j => w (B.pivot j).castSucc) =
      (fun j => w' (B.pivot j).castSucc) := by
    apply hi
    rw [B.normal_split w, B.normal_split w', hp] at hn
    exact add_right_cancel hn
  rw [B.split_coordinates w, B.split_coordinates w', hc, hp]

theorem real_normal_cast (w : Fin (r+1) → ℤ) :
    (realMatrix B.K).transpose.mulVec (fun i => (w i : ℝ)) =
      fun j => (B.K.transpose.mulVec w j : ℝ) := by
  ext j
  simp [realMatrix, Matrix.mulVec, dotProduct]

theorem normal_eq_of_real_eq {w w' : Fin (r+1) → ℤ}
    (h : (realMatrix B.K).transpose.mulVec (fun i => (w i : ℝ)) =
      (realMatrix B.K).transpose.mulVec (fun i => (w' i : ℝ))) :
    B.K.transpose.mulVec w = B.K.transpose.mulVec w' := by
  rw [B.real_normal_cast, B.real_normal_cast] at h
  ext j
  exact Int.cast_injective (congrFun h j)

theorem affine_bijOn (ha : B.HasPivot) (t : Fin q → ℝ)
    (anchor : Fin (r+1) → ℤ)
    (hanchor : (realMatrix B.K).transpose.mulVec (fun i => (anchor i : ℝ)) = t) :
    Set.BijOn B.projectZ
      {w | (realMatrix B.K).transpose.mulVec (fun i => (w i : ℝ)) = t}
      {z | z - B.projectZ anchor ∈ B.Gamma} := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    refine ⟨w-anchor, ?_, ?_⟩
    · change B.K.transpose.mulVec (w-anchor) = 0
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact B.normal_eq_of_real_eq (hw.trans hanchor.symm)
    · exact B.projectLinear.map_sub w anchor
  · intro w hw w' hw' hp
    exact B.normal_project_injective ha (B.normal_eq_of_real_eq (hw.trans hw'.symm)) hp
  · intro z hz
    obtain ⟨v, hv, hp⟩ := hz
    refine ⟨v+anchor, ?_, ?_⟩
    · change (realMatrix B.K).transpose.mulVec _ = t
      have hv' : (realMatrix B.K).transpose.mulVec (fun i => (v i : ℝ)) = 0 := by
        rw [B.real_normal_cast]
        change B.K.transpose.mulVec v = 0 at hv
        simp only [hv, Pi.zero_apply, Int.cast_zero]
        rfl
      change (realMatrix B.K).transpose.mulVec (fun i => ((v+anchor) i : ℝ)) = t
      simp only [Pi.add_apply, Int.cast_add]
      rw [show (fun i => (v i : ℝ) + (anchor i : ℝ)) =
        (fun i => (v i : ℝ)) + (fun i => (anchor i : ℝ)) from rfl,
        Matrix.mulVec_add, hv', zero_add, hanchor]
    · change B.projectLinear (v+anchor) = z
      rw [map_add]
      change B.projectZ v + B.projectZ anchor = z
      change B.projectZ v = z - B.projectZ anchor at hp
      rw [hp, sub_add_cancel]

end ChartBasis

namespace ChartIndex

theorem cast_injective (e : ℕ) : Function.Injective (ChartBasis.castCoordinates e) := by
  intro x y h
  ext i
  exact Int.cast_injective (congrArg (fun z : E e => z i) h)

theorem cast_top (e : ℕ) :
    (⊤ : Submodule ℤ (Fin e → ℤ)).map (ChartBasis.castCoordinates e) = integerLattice e := by
  classical
  apply le_antisymm
  · rintro _ ⟨z, _, rfl⟩
    have heq : ChartBasis.castCoordinates e z =
        ∑ i, z i • EuclideanSpace.basisFun (Fin e) ℝ i := by
      ext j
      simp [ChartBasis.castCoordinates, EuclideanSpace.basisFun_apply, Pi.single_apply]
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, trivial, ?_⟩
    ext j
    simp [ChartBasis.castCoordinates, EuclideanSpace.basisFun_apply, Pi.single_apply]

theorem cast_span {e : ℕ} (H : Submodule ℤ (Fin e → ℤ))
    (hH : H.toAddSubgroup.index ≠ 0) :
    Submodule.span ℝ (H.map (ChartBasis.castCoordinates e) : Set (E e)) = ⊤ := by
  classical
  apply top_unique
  rw [← (EuclideanSpace.basisFun (Fin e) ℝ).toBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change EuclideanSpace.basisFun (Fin e) ℝ i ∈
    (Submodule.span ℝ (H.map (ChartBasis.castCoordinates e) : Set (E e)))
  obtain ⟨n, hn, _, hm⟩ := H.toAddSubgroup.exists_nsmul_mem_of_index_ne_zero hH
    (Pi.single i 1)
  have hcast : ChartBasis.castCoordinates e (n • Pi.single i 1) =
      (n : ℝ) • EuclideanSpace.basisFun (Fin e) ℝ i := by
    ext j
    simp [ChartBasis.castCoordinates, EuclideanSpace.basisFun_apply, Pi.single_apply]
  have hmem : (n : ℝ) • EuclideanSpace.basisFun (Fin e) ℝ i ∈
      Submodule.span ℝ (H.map (ChartBasis.castCoordinates e) : Set (E e)) := by
    rw [← hcast]
    exact Submodule.subset_span ⟨_, hm, rfl⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh := Submodule.smul_mem
    (Submodule.span ℝ (H.map (ChartBasis.castCoordinates e) : Set (E e))) (n : ℝ)⁻¹ hmem
  simpa only [smul_smul, inv_mul_cancel₀ hn', one_smul] using hh

theorem finite_index_lattice {e : ℕ} (H : Submodule ℤ (Fin e → ℤ))
    (hH : H.toAddSubgroup.index ≠ 0) :
    ∃ L : FullLat e, L.carrier = H.map (ChartBasis.castCoordinates e) ∧
      L.det = (H.toAddSubgroup.index : ℝ) := by
  let M := H.map (ChartBasis.castCoordinates e)
  have hle : M ≤ integerLattice e := by
    rw [← cast_top]
    exact Submodule.map_mono le_top
  let : DiscreteTopology (integerLattice e) := (Coordinates.coordinateLattice e).discrete
  let : DiscreteTopology M := DiscreteTopology.of_subset inferInstance hle
  let : IsZLattice ℝ M := ⟨cast_span H hH⟩
  let L : FullLat e := ⟨M, inferInstance, inferInstance⟩
  refine ⟨L, rfl, ?_⟩
  have hcov := ZLattice.covolume_div_covolume_eq_relIndex' M
    (Coordinates.coordinateLattice e).carrier hle
  have hunit : ZLattice.covolume (Coordinates.coordinateLattice e).carrier = 1 :=
    Coordinates.coordinate_det e
  rw [hunit, div_one] at hcov
  change ZLattice.covolume M = _
  rw [hcov]
  congr 1
  change (H.map (ChartBasis.castCoordinates e)).toAddSubgroup.relIndex
    (integerLattice e).toAddSubgroup = _
  rw [← cast_top, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (cast_injective e),
    Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]

end ChartIndex

theorem projectedKernelIndex : ProjectedKernelIndex := by
  intro r q B _hcase hK ha
  have hi := B.gamma_index hK ha
  have hn : B.Gamma.toAddSubgroup.index ≠ 0 := by
    rw [hi]
    exact Int.natAbs_ne_zero.mpr ha
  obtain ⟨L, hL, hdet⟩ := ChartIndex.finite_index_lattice B.Gamma hn
  refine ⟨primitive_transpose_surjective B.K hK, hi,
    ChartIndex.cast_span B.Gamma hn, ⟨L, hL, hdet, ?_⟩, ?_⟩
  · rw [hdet, hi, Nat.cast_natAbs, Int.cast_abs]
  · exact B.affine_bijOn ha

end Praxis.Algebra.Trans
