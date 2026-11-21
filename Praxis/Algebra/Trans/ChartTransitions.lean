import Praxis.Algebra.Trans.ChartCount
import Praxis.Algebra.Trans.ChartIndex
import Praxis.Algebra.Trans.ChartShear
import Praxis.Algebra.Trans.ChartGram
import Praxis.Algebra.Trans.GramBridge
import Praxis.Algebra.Trans.Pullback
import Praxis.Algebra.Trans.Singleton
import Praxis.Algebra.Trans.Esym
import Praxis.Algebra.Trans.Adj2
import Praxis.Algebra.Trans.Cross3
import Praxis.Algebra.Trans.Pairs3
import Praxis.Algebra.Trim.Assemble
import Mathlib.Algebra.QuadraticDiscriminant
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Trans.ChartModel
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

open Matrix Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

namespace Praxis.Algebra.Trans

namespace ChartTransitions

theorem rank_cast {ι κ : Type} [Fintype ι] [Fintype κ]
    (D : Matrix ι κ ℚ) : (D.map (Rat.castHom ℝ)).rank = D.rank := by
  classical
  apply le_antisymm
  · obtain ⟨I, J, hd⟩ := Analysis.exists_rank_minor (D.map (Rat.castHom ℝ))
    have hq : (D.submatrix I J).det ≠ 0 := by
      intro he
      apply hd
      rw [Matrix.submatrix_map]
      change ((D.submatrix I J).map (fun x : ℚ => (x : ℝ))).det = 0
      rw [← Rat.cast_det, he]
      simp
    have h := D.rank_submatrix_le I J
    rw [Matrix.rank_of_det_ne_zero hq, Fintype.card_fin] at h
    exact h
  · obtain ⟨I, J, hd⟩ := Analysis.exists_rank_minor D
    have hr : ((D.map (Rat.castHom ℝ)).submatrix I J).det ≠ 0 := by
      rw [Matrix.submatrix_map]
      change ((D.submatrix I J).map (fun x : ℚ => (x : ℝ))).det ≠ 0
      rw [← Rat.cast_det]
      exact_mod_cast hd
    have h := (D.map (Rat.castHom ℝ)).rank_submatrix_le I J
    rw [Matrix.rank_of_det_ne_zero hr, Fintype.card_fin] at h
    exact h

theorem primitive_cast_injective {m d : ℕ} (B : Matrix (Fin m) (Fin d) ℤ)
    (hB : PrimitiveMatrix B) (F : Type) [Field F] [CharZero F] :
    Function.Injective (B.map (Int.castRingHom F)).mulVec := by
  obtain ⟨L, hL⟩ := primitive_left_inverse B hB
  have hl : L.map (Int.castRingHom F) * B.map (Int.castRingHom F) = 1 := by
    rw [← Matrix.map_mul, hL]
    simp
  intro x y hxy
  have hh := congrArg (L.map (Int.castRingHom F)).mulVec hxy
  simpa only [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec] using hh

theorem exists_basis {r q : ℕ} (K : Matrix (Fin (r+1)) (Fin q) ℤ)
    (hp : ∃ p : Fin q → Fin r, ((oldBlock K).submatrix p id).det ≠ 0) :
    ∃ B : ChartBasis r q, B.K = K ∧ B.HasPivot := by
  classical
  obtain ⟨p, hp⟩ := hp
  have hinj : Function.Injective p := by
    intro i j hij
    apply (Matrix.linearIndependent_rows_of_det_ne_zero hp).injective
    simp only [Matrix.submatrix_apply]
    exact congrArg (oldBlock K) hij
  let ep := Equiv.ofInjective p hinj
  let ej : Fin (r-q) ≃ ↥((Set.range p)ᶜ : Set (Fin r)) := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_compl_set, Fintype.card_fin,
      ← Fintype.card_congr ep, Fintype.card_fin])
  let rows := (Equiv.sumCongr ep ej).trans (Equiv.Set.sumCompl (Set.range p))
  refine ⟨⟨K, rows⟩, rfl, ?_⟩
  change ((oldBlock K).submatrix (fun i => rows (Sum.inl i)) id).det ≠ 0
  have he : (fun i => rows (Sum.inl i)) = p := by rfl
  rwa [he]

theorem quadratic_cs {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) (u v : Fin d → ℝ) :
    (dotProduct u (S.mulVec v))^2 ≤ quadratic S u * quadratic S v := by
  have hsym : S.transpose = S := by simpa using hS.1.eq
  have he : dotProduct v (S.mulVec u) = dotProduct u (S.mulVec v) := by
    simpa only [hsym] using dotProduct_transpose_mulVec S v u
  have hd := discrim_le_zero (a := quadratic S u)
    (b := 2 * dotProduct u (S.mulVec v)) (c := quadratic S v) (by
      intro t
      have hn := hS.posSemidef.dotProduct_mulVec_nonneg (t • u + v)
      simp only [star_trivial] at hn
      convert hn using 1
      simp only [quadratic, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [he]
      ring)
  dsimp [discrim] at hd
  nlinarith

theorem quadratic_adjugate_cs {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) (u v : Fin d → ℝ) :
    (dotProduct u v)^2 * S.det ≤ quadratic S u * quadratic S.adjugate v := by
  have hv : S.mulVec (S⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hS.det_pos.ne'), Matrix.one_mulVec]
  have hc := quadratic_cs S hS u (S⁻¹.mulVec v)
  have hq : quadratic S (S⁻¹.mulVec v) = quadratic S⁻¹ v := by
    unfold quadratic
    rw [hv, dotProduct_comm]
  rw [hv, hq] at hc
  have he : quadratic S⁻¹ v * S.det = quadratic S.adjugate v := by
    rw [Matrix.inv_def]
    simp only [quadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Ring.inverse_eq_inv]
    field_simp [hS.det_pos.ne']
  have hh := mul_le_mul_of_nonneg_right hc hS.det_pos.le
  simpa only [mul_assoc, he] using hh

theorem gram_cross (S : Matrix (Fin 3) (Fin 3) ℝ)
    (U : Matrix (Fin 3) (Fin 2) ℝ) :
    (U.transpose * S * U).det =
      quadratic S.adjugate (crossProduct (U.col 0) (U.col 1)) := by
  simp [Matrix.det_fin_two, Matrix.adjugate_fin_three, quadratic, crossProduct,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.col]
  <;> ring

def pairSum {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), w i * w j

theorem pairSum_eq {m : ℕ} (w : Fin m → ℝ) :
    pairSum w = elementarySymmetric w 2 := by
  have ht (i j : Fin m) : w i * w j =
      (if i < j then w i * w j else 0) +
      (if j < i then w j * w i else 0) +
      (if j = i then w i ^ 2 else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le, h.ne.symm]
    · subst j; simp [pow_two]
    · simp [h, not_lt.mpr h.le, h.ne]; ring
  have hs : (∑ i, w i)^2 = 2 * pairSum w + ∑ i, w i^2 := by
    calc
      _ = ∑ i, ∑ j, w i * w j := by simp [pow_two, Finset.sum_mul_sum]
      _ = ∑ i, ∑ j, ((if i < j then w i * w j else 0) +
          (if j < i then w j * w i else 0) + (if j = i then w i^2 else 0)) := by
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ht i j))
      _ = 2 * pairSum w + ∑ i, w i^2 := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => if j < i then w j * w i else 0)]
        simp [pairSum, Finset.sum_filter]
        <;> ring
  rw [elementarySymmetric_two_eq]
  linarith

theorem minor_le_height {m d : ℕ} (B : Matrix (Fin m) (Fin d) ℤ)
    (p : Fin d → Fin m) :
    |((realMatrix B).submatrix p id).det| ≤ (height B : ℝ) := by
  have h : (B.submatrix p id).det.natAbs ≤ height B :=
    Finset.le_sup (f := fun p : Fin d → Fin m => (B.submatrix p id).det.natAbs)
      (Finset.mem_univ p)
  have he : ((realMatrix B).submatrix p id).det = ((B.submatrix p id).det : ℝ) :=
    (Int.cast_det _).symm
  rw [he]
  have hh : ((B.submatrix p id).det.natAbs : ℝ) ≤ (height B : ℝ) := by exact_mod_cast h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hh

theorem detRows2_sq_le {m : ℕ} (B : Matrix (Fin m) (Fin 2) ℤ) (i j : Fin m) :
    detRows2 (realMatrix B i) (realMatrix B j)^2 ≤ (height B : ℝ)^2 := by
  have h := minor_le_height B ![i,j]
  have he : ((realMatrix B).submatrix ![i,j] id).det =
      detRows2 (realMatrix B i) (realMatrix B j) := by
    congr 1
    ext k l
    fin_cases k <;> rfl
  rw [he] at h
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

theorem detRows3_sq_le {m : ℕ} (B : Matrix (Fin m) (Fin 3) ℤ) (i j k : Fin m) :
    detRows3 (realMatrix B i) (realMatrix B j) (realMatrix B k)^2 ≤
      (height B : ℝ)^2 := by
  have h := minor_le_height B ![i,j,k]
  have he : ((realMatrix B).submatrix ![i,j,k] id).det =
      detRows3 (realMatrix B i) (realMatrix B j) (realMatrix B k) := by
    congr 1
    ext a b
    fin_cases a <;> rfl
  rw [he] at h
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

theorem counts : ChartCount 3 2 ∧ ChartCount 2 1 ∧ ChartCount 3 1 :=
  ⟨chartCount32 projectedKernelIndex ChartShear.shearedCylinderEnvelope
      ChartGram.complementaryGram,
    chartCount21 projectedKernelIndex ChartShear.shearedCylinderEnvelope
      ChartGram.complementaryGram,
    chartCount31 projectedKernelIndex ChartShear.shearedCylinderEnvelope
      ChartGram.complementaryGram⟩

end ChartTransitions

namespace TransitionInput

variable {n r q : ℕ} (T : TransitionInput n r q)

def imageInt (x : Grid T.grids) : Fin (r+1) → ℤ :=
  Fin.snoc (imageZ T.oldGrids T.old (T.oldPoint x)) (x (Fin.last n) : ℕ)

def normalCovariance : Matrix (Fin q) (Fin q) ℝ :=
  (realMatrix (oldBlock T.imageNormal)).transpose * T.sigma *
    realMatrix (oldBlock T.imageNormal)

theorem oldMass_nonneg (hw : ∀ i, 0 < T.grids i) : 0 ≤ T.oldMass := by
  letI : Nonempty (Grid T.oldGrids) := ⟨fun i => ⟨0, hw i.castSucc⟩⟩
  exact Algebra.FiniteProbability.atomMass_nonneg _

theorem imageQ_eq_cast (x : Grid T.grids) :
    T.imageQ x = fun j => (T.imageInt x j : ℚ) := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [imageQ, imageInt]
  · simp [imageQ, imageInt, imageZ, oldPoint]

def differences : Matrix (Fin (r+1)) (T.event × T.event) ℤ :=
  fun i p => T.imageInt p.1 i - T.imageInt p.2 i

theorem normal_kernel (hI : T.ImageNormals) :
    (T.differences.map (Int.castRingHom ℚ)).transpose.mulVecLin.ker =
      (ratMatrix T.imageNormal).mulVecLin.range := by
  classical
  ext z
  change ((T.differences.map (Int.castRingHom ℚ)).transpose.mulVec z = 0) ↔ _
  have he : ((T.differences.map (Int.castRingHom ℚ)).transpose.mulVec z = 0) ↔
      rationalNormal T.event T.imageQ z := by
    simp only [funext_iff, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      ratMatrix, Matrix.map_apply, Int.coe_castRingHom, differences, Int.cast_sub,
      Pi.zero_apply, rationalNormal, T.imageQ_eq_cast]
    constructor
    · intro h x hx y hy
      simpa [mul_comm] using h (⟨x, hx⟩, ⟨y, hy⟩)
    · intro h p
      simpa [mul_comm] using h p.1 p.1.property p.2 p.2.property
  rw [he]
  simpa only [LinearMap.mem_range, Matrix.mulVecLin_apply, eq_comm] using hI.2.1 z

theorem differences_rank (hI : T.ImageNormals) :
    (T.differences.map (Int.castRingHom ℝ)).rank + q = r+1 := by
  have hn := LinearMap.finrank_range_add_finrank_ker
    (T.differences.map (Int.castRingHom ℚ)).transpose.mulVecLin
  have hk : Module.finrank ℚ (ratMatrix T.imageNormal).mulVecLin.range = q := by
    simpa using LinearMap.finrank_range_of_inj (f := (ratMatrix T.imageNormal).mulVecLin)
      (ChartTransitions.primitive_cast_injective T.imageNormal hI.1 ℚ)
  rw [T.normal_kernel hI, hk] at hn
  have he : (T.differences.map (Int.castRingHom ℝ)).rank = (T.differences.map (Int.castRingHom ℚ)).rank := by
    have hm : (T.differences.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
        T.differences.map (Int.castRingHom ℝ) := by
      ext i j
      simp
    simpa only [hm] using ChartTransitions.rank_cast (T.differences.map (Int.castRingHom ℚ))
  rw [he, ← Matrix.rank_transpose]
  simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hn

theorem differences_range :
    (T.differences.map (Int.castRingHom ℝ)).mulVecLin.range =
      vectorSpan ℝ (Set.image (fun z : Fin (r+1) → ℤ => fun i => (z i : ℝ))
        (T.event.image T.imageInt : Set (Fin (r+1) → ℤ))) := by
  classical
  rw [Matrix.range_mulVecLin, vectorSpan_def]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨_, ⟨T.imageInt x, Finset.mem_image_of_mem _ x.property, rfl⟩,
      _, ⟨T.imageInt y, Finset.mem_image_of_mem _ y.property, rfl⟩, ?_⟩
    ext i
    simp [realMatrix, differences, Matrix.col]
  · rintro ⟨_, ⟨z, hz, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
    ext i
    simp [realMatrix, differences, Matrix.col]

theorem differences_range_le (hI : T.ImageNormals) :
    (T.differences.map (Int.castRingHom ℝ)).mulVecLin.range ≤
      (realMatrix T.imageNormal).transpose.mulVecLin.ker := by
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change _ = 0
  ext j
  have hn : rationalNormal T.event T.imageQ
      ((ratMatrix T.imageNormal).mulVec (Pi.single j 1)) :=
    (hI.2.1 _).mpr ⟨Pi.single j 1, rfl⟩
  have hh := hn x x.property y y.property
  simp only [Matrix.mulVec_single_one, T.imageQ_eq_cast, dotProduct,
    Pi.sub_apply, ratMatrix, Matrix.col, Matrix.transpose_apply, Matrix.map_apply,
    Int.coe_castRingHom] at hh
  have hh' : (∑ i, (T.imageNormal i j : ℝ) *
      ((T.imageInt x i : ℝ) - (T.imageInt y i : ℝ))) = 0 := by exact_mod_cast hh
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, realMatrix,
    Matrix.transpose_apply, Matrix.map_apply, Int.coe_castRingHom, Matrix.col,
    differences, Int.cast_sub, Pi.zero_apply] using hh'

theorem image_affine_span (hI : T.ImageNormals) {x₀ : Grid T.grids}
    (hx₀ : x₀ ∈ T.event) (w : Fin (r+1) → ℝ) :
    w ∈ affineSpan ℝ (Set.image (fun z : Fin (r+1) → ℤ => fun i => (z i : ℝ))
      (T.event.image T.imageInt : Set (Fin (r+1) → ℤ))) ↔
    (realMatrix T.imageNormal).transpose.mulVec w =
      (realMatrix T.imageNormal).transpose.mulVec (fun i => (T.imageInt x₀ i : ℝ)) := by
  let V := (T.differences.map (Int.castRingHom ℝ)).mulVecLin.range
  let K := (realMatrix T.imageNormal).transpose.mulVecLin.ker
  have hd := T.differences_rank hI
  have hk := LinearMap.finrank_range_add_finrank_ker
    (realMatrix T.imageNormal).transpose.mulVecLin
  have hr : (realMatrix T.imageNormal).transpose.rank = q := by
    rw [Matrix.rank_transpose, Matrix.rank]
    simpa using LinearMap.finrank_range_of_inj (f := (realMatrix T.imageNormal).mulVecLin)
      (ChartTransitions.primitive_cast_injective T.imageNormal hI.1 ℝ)
  have hvk : V = K := by
    apply Submodule.eq_of_le_of_finrank_eq (T.differences_range_le hI)
    change (T.differences.map (Int.castRingHom ℝ)).rank = Module.finrank ℝ K
    change (realMatrix T.imageNormal).transpose.rank + Module.finrank ℝ K = _ at hk
    rw [hr] at hk
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hk
    omega
  have ha : (fun i => (T.imageInt x₀ i : ℝ)) ∈
      Set.image (fun z : Fin (r+1) → ℤ => fun i => (z i : ℝ))
        (T.event.image T.imageInt : Set (Fin (r+1) → ℤ)) :=
    ⟨_, Finset.mem_image_of_mem _ hx₀, rfl⟩
  have hm := AffineSubspace.vadd_mem_iff_mem_direction
    (w - fun i => (T.imageInt x₀ i : ℝ)) (mem_affineSpan ℝ ha)
  simp only [vadd_eq_add, sub_add_cancel] at hm
  rw [hm, direction_affineSpan, ← T.differences_range]
  change (w - fun i => (T.imageInt x₀ i : ℝ)) ∈ V ↔ _
  rw [hvk]
  change (realMatrix T.imageNormal).transpose.mulVec
    (w - fun i => (T.imageInt x₀ i : ℝ)) = 0 ↔ _
  rw [Matrix.mulVec_sub, sub_eq_zero]

theorem sigma_posDef (hB : T.OldLattice) (hw : ∀ i, 0 < T.grids i) : T.sigma.PosDef := by
  have hi := ChartTransitions.primitive_cast_injective T.old hB ℝ
  have hreal : LinearIndependent ℝ (realMatrix T.old).col :=
    Matrix.mulVec_injective_iff.mp hi
  have hz : LinearIndependent ℤ T.old.col := by
    apply (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := T.old.col)).mp
    exact hreal
  exact Algebra.Trim.gridCovariance_posDef T.oldGrids (fun i => hw i.castSucc) T.old hz

theorem normalCovariance_posDef (hB : T.OldLattice) (hI : T.ImageNormals)
    (hw : ∀ i, 0 < T.grids i) : T.normalCovariance.PosDef := by
  obtain ⟨p, hp⟩ := hI.2.2
  let U := realMatrix (oldBlock T.imageNormal)
  have hp' : (U.submatrix p id).det ≠ 0 := by
    have he : (U.submatrix p id).det =
        (((oldBlock T.imageNormal).submatrix p id).det : ℝ) := (Int.cast_det _).symm
    rw [he]
    exact_mod_cast hp
  have hu : Function.Injective U.mulVec := by
    intro x y hxy
    apply Matrix.mulVec_injective_of_det_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hp')
    exact congrArg (fun z => fun i => z (p i)) hxy
  have h := (T.sigma_posDef hB hw).conjTranspose_mul_mul_same hu
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, U, normalCovariance] using h

theorem exists_chartData (P : VITParameters) (hcase : ChartCase r q)
    (hT : TransitionData r q P.toVITData T) :
    ∃ C : ChartData r q, C.S = T.event.image T.imageInt ∧
      C.Sigma = T.sigma ∧ C.K = T.imageNormal ∧ C.R = P.R ∧
      C.intervalLength = (T.grids (Fin.last n) : ℝ) := by
  classical
  obtain ⟨hB, htrim, _, _, hI, _, hw, _⟩ := hT
  obtain ⟨B, hBK, hBp⟩ := ChartTransitions.exists_basis T.imageNormal hI.2.2
  obtain ⟨x₀, hx₀⟩ := htrim.1
  let C : ChartData r q := {
    toChartGeometry := {
      toChartBasis := B
      Sigma := T.sigma
      mu := T.center
      target := (realMatrix T.imageNormal).transpose.mulVec
        (fun i => (T.imageInt x₀ i : ℝ))
      R := P.R
      lower := 0
      upper := (T.grids (Fin.last n) : ℝ) }
    S := T.event.image T.imageInt
    dimensionCase := hcase
    primitive := hBK ▸ hI.1
    pivot_ne_zero := hBp
    positive := T.sigma_posDef hB hw
    radius_pos := by rw [P.R_eq]; norm_num
    interval_order := Nat.cast_nonneg _
    nonempty := htrim.1.image T.imageInt
    affine_span := by
      intro w
      simpa only [hBK] using T.image_affine_span hI hx₀ w
    contained := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      constructor
      · change (T.imageInt x (Fin.last r) : ℝ) ∈ Set.Icc 0 _
        simp only [imageInt, Fin.snoc_last, Int.cast_natCast, Set.mem_Icc]
        exact ⟨Nat.cast_nonneg _, by exact_mod_cast (x (Fin.last n)).isLt.le⟩
      · simpa only [imageInt, Fin.snoc_castSucc, quadratic,
          Analysis.mahalanobisSq, Pi.sub_apply] using htrim.2 x hx }
  exact ⟨C, rfl, rfl, hBK, rfl, by simp [C, ChartGeometry.intervalLength]⟩

theorem image_fibre_card_le (y : Fin (r+1) → ℤ) :
    (T.event.filter (fun x => T.imageInt x = y)).card ≤
      Algebra.FiniteProbability.fibreCount (imageZ T.oldGrids T.old) (fun j => y j.castSucc) := by
  classical
  unfold Algebra.FiniteProbability.fibreCount
  apply Finset.card_le_card_of_injOn T.oldPoint
  · intro x hx
    have h := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    ext j
    simpa [imageInt] using congrFun h j.castSucc
  · intro x hx z hz he
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hlast := congrFun (hx'.trans hz'.symm) (Fin.last r)
    have he' : x (Fin.last n) = z (Fin.last n) := by
      apply Fin.ext
      simpa [imageInt] using hlast
    funext i
    exact Fin.lastCases he' (fun j => congrFun he j) i

theorem density_le_image_card_mul_oldMass :
    T.density ≤ ((T.event.image T.imageInt).card : ℝ) * T.oldMass /
      (T.grids (Fin.last n) : ℝ) := by
  classical
  have hf (y : Fin (r+1) → ℤ) :
      ((T.event.filter (fun x => T.imageInt x = y)).card : ℝ) /
        (Fintype.card (Grid T.grids) : ℝ) ≤
        T.oldMass / (T.grids (Fin.last n) : ℝ) := by
    have hc : ((T.event.filter (fun x => T.imageInt x = y)).card : ℝ) ≤
        Algebra.FiniteProbability.fibreCount (imageZ T.oldGrids T.old) (fun j => y j.castSucc) := by
      exact_mod_cast T.image_fibre_card_le y
    calc
      _ ≤ Algebra.FiniteProbability.pointProb (imageZ T.oldGrids T.old)
          (fun j => y j.castSucc) / (T.grids (Fin.last n) : ℝ) := by
        unfold Algebra.FiniteProbability.pointProb
        rw [T.grid_card_split, Nat.cast_mul, div_div]
        exact div_le_div_of_nonneg_right hc (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_right
        (Algebra.FiniteProbability.pointProb_le_mass _ _) (Nat.cast_nonneg _)
  unfold density
  rw [Finset.card_eq_sum_card_image T.imageInt T.event, Nat.cast_sum, Finset.sum_div]
  exact (Finset.sum_le_sum (fun y _ => hf y)).trans_eq (by simp; ring)

theorem density_le_chart (P : VITParameters) (hcase : ChartCase r q)
    (hc : ChartCount r q) (hp : PlanarCount) (h3 : SectionCount3)
    (hT : TransitionData r q P.toVITData T) :
    T.density ≤ (if r-q+1 = 2 then 6 else 648) *
      ChartGeometry.ballVolume (r-q) * P.R^(r-q) * T.oldMass *
      Real.sqrt T.sigma.det / Real.sqrt T.normalCovariance.det := by
  obtain ⟨C, hS, hSigma, hK, hR, hI⟩ := T.exists_chartData P hcase hT
  have hn : C.normalGram C.Sigma = T.normalCovariance := by
    simp only [ChartBasis.normalGram, ChartBasis.U, hSigma, hK, normalCovariance]
  have hcount := hc hp h3 C
  rw [hS, hn, hSigma, hR, hI] at hcount
  have hw := hT.2.2.2.2.2.2.1
  have hm := T.oldMass_nonneg hw
  have hg : (0 : ℝ) < T.grids (Fin.last n) := by exact_mod_cast hw (Fin.last n)
  apply T.density_le_image_card_mul_oldMass.trans
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcount hm) hg.le).trans_eq
  field_simp
  <;> ring

end TransitionInput

namespace ChartTransitions

theorem weighted_row2 {m : ℕ} (B : Matrix (Fin m) (Fin 2) ℤ)
    (s : Fin m → ℝ) (hw : WeightedAdj2 (realMatrix B) s) (i : Fin m) :
    quadratic (weightedGram (realMatrix B) s).adjugate (realMatrix B i) ≤
      (height B : ℝ)^2 * ∑ j, s j^2 := by
  rw [hw i, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [mul_le_mul_of_nonneg_left (detRows2_sq_le B i j) (sq_nonneg (s j))]

theorem weighted_cross3 {m : ℕ} (B : Matrix (Fin m) (Fin 3) ℤ)
    (s : Fin m → ℝ) (hw : WeightedCross3 (realMatrix B) s) (i j : Fin m) :
    quadratic (weightedGram (realMatrix B) s) (crossProduct (realMatrix B i) (realMatrix B j)) ≤
      (height B : ℝ)^2 * ∑ k, s k^2 := by
  rw [hw i j, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  nlinarith [mul_le_mul_of_nonneg_left (detRows3_sq_le B i j k) (sq_nonneg (s k))]

theorem weighted_row3 {m : ℕ} (B : Matrix (Fin m) (Fin 3) ℤ)
    (s : Fin m → ℝ) (hw : WeightedPairs3 (realMatrix B) s) (i : Fin m) :
    quadratic (weightedGram (realMatrix B) s).adjugate (realMatrix B i) ≤
      (height B : ℝ)^2 * elementarySymmetric (fun j => s j^2) 2 := by
  rw [hw i, ← pairSum_eq]
  simp only [pairSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  nlinarith [mul_le_mul_of_nonneg_left (detRows3_sq_le B i j k)
    (mul_nonneg (sq_nonneg (s j)) (sq_nonneg (s k)))]

theorem gram_one {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin 1) ℝ) :
    (U.transpose * S * U).det = quadratic S (U.col 0) := by
  have he : quadratic (U.transpose * S * U) (1 : Fin 1 → ℝ) =
      quadratic S (U.mulVec (1 : Fin 1 → ℝ)) := by
    unfold quadratic
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_transpose_mulVec, dotProduct_comm]
  simpa [Matrix.det_fin_one, quadratic, Matrix.mulVec, dotProduct] using he

theorem pulled_minor_one {n r : ℕ} (T : TransitionInput n r 1) (p : Fin 1 → Fin n) :
    (((T.pulledNormal.submatrix (fun j => (p j).castSucc) id).det : ℤ) : ℝ) =
      dotProduct (realMatrix T.old (p 0))
        (fun j => (T.imageNormal j.castSucc 0 : ℝ)) := by
  simp [Matrix.det_fin_one, pulledNormal_old_entry, dotProduct, realMatrix]

theorem pulled_minor_two {n : ℕ} (T : TransitionInput n 3 2) (p : Fin 2 → Fin n) :
    (((T.pulledNormal.submatrix (fun j => (p j).castSucc) id).det : ℤ) : ℝ) =
      dotProduct
        (crossProduct (fun j : Fin 3 => (T.imageNormal j.castSucc 0 : ℝ))
          (fun j : Fin 3 => (T.imageNormal j.castSucc 1 : ℝ)))
        (crossProduct (realMatrix T.old (p 0)) (realMatrix T.old (p 1))) := by
  have hp : p = ![p 0, p 1] := by ext j; fin_cases j <;> rfl
  have he : (fun j => (p j).castSucc) = ![(p 0).castSucc, (p 1).castSucc] := by
    ext j; fin_cases j <;> rfl
  rw [he, pulled_minor_cross]
  simp [dotProduct, crossProduct, realMatrix, Fin.sum_univ_succ]

theorem covariance32 (P : VITParameters) {n : ℕ} (T : TransitionInput n 3 2)
    (hT : TransitionData 3 2 P.toVITData T) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedCross3 B s) :
    ∃ h : ℕ, 1 ≤ h ∧ T.sigma.det * ((h : ℝ) * T.newHeight)^2 ≤
      (T.oldHeight : ℝ)^2 * (∑ i, ((T.oldGrids i : ℝ) / Real.sqrt 12)^2) *
        T.normalCovariance.det := by
  obtain ⟨_, h, p, _, _, hh, _, hm⟩ := hn n 3 2 P.toVITData T hT
  let v := crossProduct (fun j : Fin 3 => (T.imageNormal j.castSucc 0 : ℝ))
    (fun j : Fin 3 => (T.imageNormal j.castSucc 1 : ℝ))
  let b := crossProduct (realMatrix T.old (p 0)) (realMatrix T.old (p 1))
  have hs := T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1
  have hg := T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1
  have hc := quadratic_adjugate_cs T.sigma hs b v
  have he : quadratic T.sigma.adjugate v = T.normalCovariance.det := by
    exact (gram_cross T.sigma (realMatrix (oldBlock T.imageNormal))).symm
  have hm' : |dotProduct v b| = (h : ℝ) * T.newHeight := by
    rw [← pulled_minor_two T p]
    have hcast := congrArg (fun k : ℕ => (k : ℝ)) hm
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul] using hcast
  have hb := weighted_cross3 T.old (fun i => (T.oldGrids i : ℝ) / Real.sqrt 12)
    (hw n _ _) (p 0) (p 1)
  rw [weightedGram_gridSigma] at hb
  change quadratic T.sigma b ≤ _ at hb
  rw [he, dotProduct_comm, ← sq_abs, hm'] at hc
  refine ⟨h, hh, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hb hg.det_pos.le
  change _ ≤ (T.oldHeight : ℝ)^2 * _ * _ at hmul
  nlinarith

theorem covariance21 (P : VITParameters) {n : ℕ} (T : TransitionInput n 2 1)
    (hT : TransitionData 2 1 P.toVITData T) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 2) ℝ) (s : Fin n → ℝ), WeightedAdj2 B s) :
    ∃ h : ℕ, 1 ≤ h ∧ T.sigma.det * ((h : ℝ) * T.newHeight)^2 ≤
      (T.oldHeight : ℝ)^2 * (∑ i, ((T.oldGrids i : ℝ) / Real.sqrt 12)^2) *
        T.normalCovariance.det := by
  obtain ⟨_, h, p, _, _, hh, _, hm⟩ := hn n 2 1 P.toVITData T hT
  let u := fun j : Fin 2 => (T.imageNormal j.castSucc 0 : ℝ)
  let b := realMatrix T.old (p 0)
  have hs := T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1
  have hg := T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1
  have hc := quadratic_adjugate_cs T.sigma hs u b
  have he : quadratic T.sigma u = T.normalCovariance.det :=
    (gram_one T.sigma (realMatrix (oldBlock T.imageNormal))).symm
  have hm' : |dotProduct u b| = (h : ℝ) * T.newHeight := by
    rw [dotProduct_comm, ← pulled_minor_one T p]
    have hcast := congrArg (fun k : ℕ => (k : ℝ)) hm
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul] using hcast
  have hb := weighted_row2 T.old (fun i => (T.oldGrids i : ℝ) / Real.sqrt 12)
    (hw n _ _) (p 0)
  rw [weightedGram_gridSigma] at hb
  change quadratic T.sigma.adjugate b ≤ _ at hb
  rw [he, ← sq_abs, hm'] at hc
  refine ⟨h, hh, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hb hg.det_pos.le
  change _ ≤ _ * ((T.oldHeight : ℝ)^2 * _) at hmul
  nlinarith

theorem covariance31 (P : VITParameters) {n : ℕ} (T : TransitionInput n 3 1)
    (hT : TransitionData 3 1 P.toVITData T) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedPairs3 B s) :
    ∃ h : ℕ, 1 ≤ h ∧ T.sigma.det * ((h : ℝ) * T.newHeight)^2 ≤
      (T.oldHeight : ℝ)^2 *
        elementarySymmetric (fun i => ((T.oldGrids i : ℝ) / Real.sqrt 12)^2) 2 *
          T.normalCovariance.det := by
  obtain ⟨_, h, p, _, _, hh, _, hm⟩ := hn n 3 1 P.toVITData T hT
  let u := fun j : Fin 3 => (T.imageNormal j.castSucc 0 : ℝ)
  let b := realMatrix T.old (p 0)
  have hs := T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1
  have hg := T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1
  have hc := quadratic_adjugate_cs T.sigma hs u b
  have he : quadratic T.sigma u = T.normalCovariance.det :=
    (gram_one T.sigma (realMatrix (oldBlock T.imageNormal))).symm
  have hm' : |dotProduct u b| = (h : ℝ) * T.newHeight := by
    rw [dotProduct_comm, ← pulled_minor_one T p]
    have hcast := congrArg (fun k : ℕ => (k : ℝ)) hm
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul] using hcast
  have hb := weighted_row3 T.old (fun i => (T.oldGrids i : ℝ) / Real.sqrt 12)
    (hw n _ _) (p 0)
  rw [weightedGram_gridSigma] at hb
  change quadratic T.sigma.adjugate b ≤ _ at hb
  rw [he, ← sq_abs, hm'] at hc
  refine ⟨h, hh, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hb hg.det_pos.le
  change _ ≤ _ * ((T.oldHeight : ℝ)^2 * _) at hmul
  nlinarith

theorem sqrt_ratio_index {a b M W H : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hM : 0 ≤ M) (hW : 0 ≤ W) (hH : 0 ≤ H)
    (h : a * H^2 ≤ M^2 * W * b) :
    Real.sqrt a / Real.sqrt b * H ≤ M * Real.sqrt W := by
  have hs : (Real.sqrt a * H)^2 ≤ (M * Real.sqrt W * Real.sqrt b)^2 := by
    simpa only [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hW, Real.sq_sqrt hb.le] using h
  have hl := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hH)
    (mul_nonneg (mul_nonneg hM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).mp hs
  have hr : (Real.sqrt a * H) / Real.sqrt b ≤ M * Real.sqrt W :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hb)).mpr hl
  calc
    Real.sqrt a / Real.sqrt b * H = (Real.sqrt a * H) / Real.sqrt b := by ring
    _ ≤ _ := hr

theorem weight_budget (P : VITParameters) {n r q : ℕ} (T : TransitionInput n r q)
    (hT : TransitionData r q P.toVITData T) :
    (∑ i, ((T.oldGrids i : ℝ) / Real.sqrt 12)^2) ≤ (P.g : ℝ)^2 * P.S / 12 := by
  have hb := hT.2.2.2.2.2.2.2
  rw [Fin.sum_univ_castSucc] at hb
  have ho : (∑ i : Fin n, (T.oldGrids i : ℝ)^2) ≤ (P.g : ℝ)^2 * P.S := by
    exact le_trans (le_add_of_nonneg_right (sq_nonneg _)) hb
  simp_rw [gridSigma_sq]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right ho (by norm_num)

theorem D_factor (P : VITParameters) {W : ℝ} (hW : 0 ≤ W)
    (hb : W ≤ (P.g : ℝ)^2 * P.S / 12) :
    12 * P.R * Real.sqrt W ≤ P.D * P.g := by
  have hD := P.D_pos
  apply (sq_le_sq₀ (by rw [P.R_eq]; positivity) (by positivity)).mp
  calc
    (12 * P.R * Real.sqrt W)^2 = 144 * P.R^2 * W := by
      rw [mul_pow, Real.sq_sqrt hW]; ring
    _ ≤ 12 * P.R^2 * P.S * (P.g : ℝ)^2 := by
      have hmul := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 144 * P.R^2)
      nlinarith only [hmul]
    _ ≤ (P.D * P.g)^2 := by
      have hmul := mul_le_mul_of_nonneg_right P.D_geometry (sq_nonneg (P.g : ℝ))
      nlinarith only [hmul]

theorem pair_weight_budget (P : VITParameters) {n r q : ℕ} (T : TransitionInput n r q)
    (hT : TransitionData r q P.toVITData T)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S) :
    0 ≤ elementarySymmetric (fun i => ((T.oldGrids i : ℝ) / Real.sqrt 12)^2) 2 ∧
    elementarySymmetric (fun i => ((T.oldGrids i : ℝ) / Real.sqrt 12)^2) 2 ≤
      (P.g : ℝ)^4 * P.S^2 / 288 := by
  let w := fun i : Fin n => ((T.oldGrids i : ℝ) / Real.sqrt 12)^2
  have hw : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hb := weight_budget P T hT
  have hs := (he n w (∑ i, w i) hw rfl).1
  have hsq := pow_le_pow_left₀ hsum hb 2
  constructor
  · rw [← pairSum_eq]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (hw i) (hw j)))
  · apply hs.trans
    convert div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

theorem E_factor (P : VITParameters) {W : ℝ} (hW : 0 ≤ W)
    (hb : W ≤ (P.g : ℝ)^4 * P.S^2 / 288) :
    648 * Real.pi * P.R^2 * Real.sqrt W ≤ P.E * (P.g : ℝ)^2 := by
  have hE := P.E_pos
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (648 * Real.pi * P.R^2 * Real.sqrt W)^2 =
        648^2 * Real.pi^2 * P.R^4 * W := by
      rw [mul_pow, Real.sq_sqrt hW]; ring
    _ ≤ (54^2 * Real.pi^2 * P.R^4 * P.S^2 / 2) * (P.g : ℝ)^4 := by
      have hmul := mul_le_mul_of_nonneg_left hb
        (by positivity : (0 : ℝ) ≤ 648^2 * Real.pi^2 * P.R^4)
      nlinarith only [hmul]
    _ ≤ (P.E * (P.g : ℝ)^2)^2 := by
      have hmul := mul_le_mul_of_nonneg_right P.E_geometry (by positivity : (0 : ℝ) ≤ (P.g : ℝ)^4)
      nlinarith only [hmul]

theorem density_with_index {m f a b W c B : ℝ} {h H M : ℕ}
    (hh : 1 ≤ h) (ha : 0 ≤ a) (hb : 0 < b) (hf : 0 ≤ f)
    (hc : 0 ≤ c) (hW : 0 ≤ W)
    (hcount : m ≤ c * f * Real.sqrt a / Real.sqrt b)
    (hdet : a * ((h : ℝ) * H)^2 ≤ (M : ℝ)^2 * W * b)
    (hfactor : c * Real.sqrt W ≤ B) :
    m * H ≤ B * M * f / (h : ℝ) := by
  have hp : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hr := sqrt_ratio_index ha hb (Nat.cast_nonneg M) hW (by positivity) hdet
  apply (le_div_iff₀ hp).mpr
  calc
    m * H * h = m * ((h : ℝ) * H) := by ring
    _ ≤ (c * f * Real.sqrt a / Real.sqrt b) * ((h : ℝ) * H) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = c * f * (Real.sqrt a / Real.sqrt b * ((h : ℝ) * H)) := by ring
    _ ≤ c * f * (M * Real.sqrt W) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hc hf)
    _ = (c * Real.sqrt W) * M * f := by ring
    _ ≤ B * M * f := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg M)) hf

theorem transition32_index (P : VITParameters) (hc : ChartCount 3 2)
    (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedCross3 B s)
    (hp : PlanarCount) (h3 : SectionCount3) {n : ℕ} (T : TransitionInput n 3 2)
    (hT : TransitionData 3 2 P.toVITData T) :
    ∃ h : ℕ, 1 ≤ h ∧ T.density * T.newHeight ≤
      (P.D * P.g * T.oldHeight * T.oldMass) / (h : ℝ) := by
  obtain ⟨h, hh, hd⟩ := covariance32 P T hT hn hw
  have hcount := T.density_le_chart P (Or.inl ⟨rfl, rfl⟩) hc hp h3 hT
  simp only [show 3-2+1 = 2 from rfl, show 3-2 = 1 from rfl, if_true,
    ChartCountProof.ballVolume_one, pow_one] at hcount
  have hW : 0 ≤ ∑ i, ((T.oldGrids i : ℝ) / Real.sqrt 12)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨h, hh, density_with_index hh
    (T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1).det_pos.le
    (T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1).det_pos
    (T.oldMass_nonneg hT.2.2.2.2.2.2.1)
    (show 0 ≤ 12 * P.R by rw [P.R_eq]; norm_num) hW ?_ hd
    (D_factor P hW (weight_budget P T hT))⟩
  convert hcount using 1 <;> ring

theorem transition21_index (P : VITParameters) (hc : ChartCount 2 1)
    (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 2) ℝ) (s : Fin n → ℝ), WeightedAdj2 B s)
    (hp : PlanarCount) (h3 : SectionCount3) {n : ℕ} (T : TransitionInput n 2 1)
    (hT : TransitionData 2 1 P.toVITData T) :
    ∃ h : ℕ, 1 ≤ h ∧ T.density * T.newHeight ≤
      (P.D * P.g * T.oldHeight * T.oldMass) / (h : ℝ) := by
  obtain ⟨h, hh, hd⟩ := covariance21 P T hT hn hw
  have hcount := T.density_le_chart P (Or.inr (Or.inl ⟨rfl, rfl⟩)) hc hp h3 hT
  simp only [show 2-1+1 = 2 from rfl, show 2-1 = 1 from rfl, if_true,
    ChartCountProof.ballVolume_one, pow_one] at hcount
  have hW : 0 ≤ ∑ i, ((T.oldGrids i : ℝ) / Real.sqrt 12)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨h, hh, density_with_index hh
    (T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1).det_pos.le
    (T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1).det_pos
    (T.oldMass_nonneg hT.2.2.2.2.2.2.1)
    (show 0 ≤ 12 * P.R by rw [P.R_eq]; norm_num) hW ?_ hd
    (D_factor P hW (weight_budget P T hT))⟩
  convert hcount using 1 <;> ring

theorem transition31_index (P : VITParameters) (hc : ChartCount 3 1)
    (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedPairs3 B s)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S)
    (hp : PlanarCount) (h3 : SectionCount3) {n : ℕ} (T : TransitionInput n 3 1)
    (hT : TransitionData 3 1 P.toVITData T) :
    ∃ h : ℕ, 1 ≤ h ∧ T.density * T.newHeight ≤
      (P.E * (P.g : ℝ)^2 * T.oldHeight * T.oldMass) / (h : ℝ) := by
  obtain ⟨h, hh, hd⟩ := covariance31 P T hT hn hw
  have hcount := T.density_le_chart P (Or.inr (Or.inr ⟨rfl, rfl⟩)) hc hp h3 hT
  simp only [show 3-1+1 = 3 from rfl, show 3-1 = 2 from rfl,
    show ¬ (3 : ℕ) = 2 by decide, if_false, ChartCountProof.ballVolume_two] at hcount
  obtain ⟨hW, hbudget⟩ := pair_weight_budget P T hT he
  refine ⟨h, hh, density_with_index hh
    (T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1).det_pos.le
    (T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1).det_pos
    (T.oldMass_nonneg hT.2.2.2.2.2.2.1) (by positivity) hW ?_ hd
    (E_factor P hW hbudget)⟩
  exact hcount

theorem drop_index {a b : ℝ} {h : ℕ} (hh : 1 ≤ h) (hb : 0 ≤ b)
    (ha : a ≤ b / (h : ℝ)) : a ≤ b :=
  ha.trans (div_le_self hb (by exact_mod_cast hh))

theorem transition32 (P : VITParameters) : Chart.Transition32 P := by
  intro hc hn hw _ hp h3 _ n T hT
  obtain ⟨h, hh, hb⟩ := transition32_index P hc hn hw hp h3 T hT
  have hm := T.oldMass_nonneg hT.2.2.2.2.2.2.1
  have hD := P.D_pos
  exact drop_index hh (by positivity) hb

theorem transition21 (P : VITParameters) : Chart.Transition21 P := by
  intro hc hn hw _ hp h3 _ n T hT
  obtain ⟨h, hh, hb⟩ := transition21_index P hc hn hw hp h3 T hT
  have hm := T.oldMass_nonneg hT.2.2.2.2.2.2.1
  have hD := P.D_pos
  exact drop_index hh (by positivity) hb

theorem transition31 (P : VITParameters) : Chart.Transition31 P := by
  intro hc hn hw he hp h3 _ n T hT
  obtain ⟨h, hh, hb⟩ := transition31_index P hc hn hw he hp h3 T hT
  have hm := T.oldMass_nonneg hT.2.2.2.2.2.2.1
  have hE := P.E_pos
  exact drop_index hh (by positivity) hb

theorem transition32_compat (P : VITParameters) : Algebra.Trans.Transition32 P :=
  Chart.transition32_compat P (transition32 P) counts.1 normalPullback
    (fun _ B s => weightedCross3 B s) (fun _ w S => esymBounds w S)

theorem transition21_compat (P : VITParameters) : Algebra.Trans.Transition21 P :=
  Chart.transition21_compat P (transition21 P) counts.2.1 normalPullback
    (fun _ B s => weightedAdj2 B s) (fun _ w S => esymBounds w S)

theorem transition31_compat (P : VITParameters) : Algebra.Trans.Transition31 P :=
  Chart.transition31_compat P (transition31 P) counts.2.2 normalPullback
    (fun _ B s => weightedPairs3 B s) (fun _ w S => esymBounds w S)

end ChartTransitions

end Praxis.Algebra.Trans
