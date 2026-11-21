import Praxis.Algebra.Trans.ChartModel
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Ring
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.AlgModel

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

open Matrix Praxis.Algebra.Point

namespace Praxis.Algebra.Trans.ChartShear

variable {r q : ℕ}

theorem free_A (B : ChartBasis r q) (i j : Fin (r-q)) :
    B.A (B.free i) j = if i = j then 1 else 0 := by
  simp [ChartBasis.A, ChartBasis.free]

theorem A_injective (B : ChartBasis r q) : Function.Injective B.A.mulVec := by
  intro x y h
  funext i
  have hi := congrFun h (B.free i)
  simpa [Matrix.mulVec, dotProduct, free_A] using hi

theorem C_posDef (T : ChartGeometry r q) (h : T.Sigma.PosDef) :
    (T.C T.Sigma).PosDef := by
  simpa [ChartBasis.C] using
    (Matrix.posDef_inv_iff.mpr h).conjTranspose_mul_mul_same (A_injective T.toChartBasis)

theorem ell_equation (T : ChartGeometry r q) (h : T.Sigma.PosDef) (x : ℝ) :
    (T.C T.Sigma).mulVec (T.ell x) =
      T.A.transpose.mulVec (T.Sigma⁻¹.mulVec (T.delta x)) := by
  rw [ChartGeometry.ell, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((T.C T.Sigma).isUnit_iff_isUnit_det.mp (C_posDef T h).isUnit),
    Matrix.one_mulVec]

theorem residual_orthogonal (T : ChartGeometry r q) (h : T.Sigma.PosDef) (x : ℝ) :
    T.A.transpose.mulVec (T.Sigma⁻¹.mulVec (T.rho x)) = 0 := by
  simp only [ChartGeometry.rho, Matrix.mulVec_sub]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  apply sub_eq_zero.mpr
  simpa only [ChartBasis.C, Matrix.mulVec_mulVec] using (ell_equation T h x).symm

theorem quadratic_pullback (B : ChartBasis r q) (Q : Matrix (Fin r) (Fin r) ℝ)
    (z : Fin (r-q) → ℝ) :
    quadratic Q (B.A.mulVec z) = quadratic (B.A.transpose * Q * B.A) z := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec,
    dotProduct_comm]

theorem completed_square (T : ChartGeometry r q) (h : T.Sigma.PosDef)
    (z : Fin (r-q) → ℝ) (x : ℝ) :
    quadratic T.Sigma⁻¹ (T.A.mulVec z + T.delta x) =
      quadratic (T.C T.Sigma) (z + T.ell x) + quadratic T.Sigma⁻¹ (T.rho x) := by
  have hQ : T.Sigma⁻¹.transpose = T.Sigma⁻¹ := by
    simpa using (Matrix.posDef_inv_iff.mpr h).isHermitian.eq
  have ho : dotProduct (T.A.mulVec (z + T.ell x))
      (T.Sigma⁻¹.mulVec (T.rho x)) = 0 := by
    rw [dotProduct_comm, ← dotProduct_transpose_mulVec,
      residual_orthogonal T h, dotProduct_zero]
  have ho' : dotProduct (T.rho x)
      (T.Sigma⁻¹.mulVec (T.A.mulVec (z + T.ell x))) = 0 := by
    rw [← hQ, dotProduct_transpose_mulVec]
    exact ho
  have he : T.A.mulVec z + T.delta x =
      T.A.mulVec (z + T.ell x) + T.rho x := by
    simp [ChartGeometry.rho, Matrix.mulVec_add]
  have qadd (u v : Fin r → ℝ) :
      quadratic T.Sigma⁻¹ (u + v) = quadratic T.Sigma⁻¹ u +
        quadratic T.Sigma⁻¹ v + dotProduct u (T.Sigma⁻¹.mulVec v) +
        dotProduct v (T.Sigma⁻¹.mulVec u) := by
    unfold quadratic
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  rw [he]
  rw [qadd, ho, ho', add_zero, add_zero, quadratic_pullback]
  rfl

theorem section_subset (T : ChartGeometry r q) (h : T.Sigma.PosDef) :
    T.actualSection ⊆ T.envelope := by
  intro w hw
  refine ⟨hw.1, ?_⟩
  have he : T.reconstruct w - T.mu =
      T.A.mulVec (fun j => w j.castSucc) + T.delta (w (Fin.last (r-q))) := by
    ext i
    simp [ChartGeometry.reconstruct, ChartGeometry.delta]
    ring
  have hn : 0 ≤ quadratic T.Sigma⁻¹ (T.rho (w (Fin.last (r-q)))) :=
    (Matrix.posDef_inv_iff.mpr h).posSemidef.dotProduct_mulVec_nonneg _
  have hb := hw.2
  rw [he, completed_square T h] at hb
  exact le_trans (le_add_of_nonneg_right hn) hb

def unshear (T : ChartGeometry r q) (w : E (r-q+1)) : E (r-q+1) :=
  WithLp.toLp 2 (Fin.snoc ((fun j => w j.castSucc) - T.ell (w (Fin.last (r-q))))
    (w (Fin.last (r-q))))

theorem unshear_shear (T : ChartGeometry r q) (w : E (r-q+1)) :
    unshear T (T.shear w) = w := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [unshear, ChartGeometry.shear]

theorem shear_unshear (T : ChartGeometry r q) (w : E (r-q+1)) :
    T.shear (unshear T w) = w := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [unshear, ChartGeometry.shear]

theorem shear_bijOn (T : ChartGeometry r q) :
    Set.BijOn T.shear T.envelope T.straightCylinder := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    simpa [ChartGeometry.envelope, ChartGeometry.straightCylinder, ChartGeometry.shear,
      Pi.add_def] using hw
  · intro x _ y _ hxy
    simpa only [unshear_shear] using congrArg (unshear T) hxy
  · intro w hw
    refine ⟨unshear T w, ?_, shear_unshear T w⟩
    simpa [ChartGeometry.envelope, ChartGeometry.straightCylinder, unshear,
      ← Pi.sub_def] using hw

theorem shear_det (T : ChartGeometry r q) : T.shearMatrix.det = 1 := by
  have ht : T.shearMatrix.IsUpperTriangular := by
    intro i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    all_goals intro hji
    · simp only [ChartGeometry.shearMatrix, Fin.lastCases_last]
      split_ifs with hj
      · subst j; exact (lt_irrefl _ hji).elim
      · rfl
    · simp only [ChartGeometry.shearMatrix, Fin.lastCases_castSucc]
      have hj : j ≠ Fin.last (r-q) := by
        intro he; subst j; exact (not_lt_of_ge (Fin.le_last _) hji).elim
      have hk : j ≠ k.castSucc := ne_of_lt hji
      simp [hj, hk]
  rw [Matrix.det_of_isUpperTriangular ht]
  apply Finset.prod_eq_one
  intro i _
  refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [ChartGeometry.shearMatrix]

theorem ell_affine (T : ChartGeometry r q) (x : ℝ) :
    T.ell x = x • (T.ell 1 - T.ell 0) + T.ell 0 := by
  have hd : T.delta x = x • (T.delta 1 - T.delta 0) + T.delta 0 := by
    ext i
    simp [ChartGeometry.delta]
    ring
  unfold ChartGeometry.ell
  rw [hd]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem ell_reflect (T : ChartGeometry r q) (x : ℝ) :
    T.ell (2 * T.midpoint - x) = 2 • T.ell T.midpoint - T.ell x := by
  rw [ell_affine T (2 * T.midpoint - x), ell_affine T T.midpoint, ell_affine T x]
  ext i
  simp
  ring

theorem quadratic_neg {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) :
    quadratic C (-z) = quadratic C z := by
  simp only [quadratic, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem envelope_symmetric (T : ChartGeometry r q) :
    ∀ w, w ∈ T.envelope ↔ 2 • T.envelopeCenter - w ∈ T.envelope := by
  intro w
  have hx : 2 * T.midpoint - w (Fin.last (r-q)) ∈ Set.Icc T.lower T.upper ↔
      w (Fin.last (r-q)) ∈ Set.Icc T.lower T.upper := by
    simp only [Set.mem_Icc, ChartGeometry.midpoint]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hz : (fun j => (2 • T.envelopeCenter - w) j.castSucc) +
      T.ell ((2 • T.envelopeCenter - w) (Fin.last (r-q))) =
      -((fun j => w j.castSucc) + T.ell (w (Fin.last (r-q)))) := by
    simp only [ChartGeometry.envelopeCenter, PiLp.sub_apply, PiLp.smul_apply,
      Fin.snoc_castSucc, Fin.snoc_last]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    rw [ell_reflect]
    ext i
    simp
    ring
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hz, quadratic_neg]
  exact and_congr (by simpa [ChartGeometry.envelopeCenter] using hx.symm) Iff.rfl

theorem factor_exists {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosDef) :
    ∃ F : Matrix (Fin d) (Fin d) ℝ,
      F.transpose * F = C ∧ |F.det| = Real.sqrt C.det ∧ F.det ≠ 0 := by
  let U := hC.isHermitian.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal
    (fun i => Real.sqrt (hC.isHermitian.eigenvalues i))
  let F := D * (star U : Matrix (Fin d) (Fin d) ℝ)
  have hD : D.transpose * D = Matrix.diagonal hC.isHermitian.eigenvalues := by
    simp only [D, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hC.eigenvalues_pos i).le
  have hF : F.transpose * F = C := by
    calc
      F.transpose * F = (U : Matrix (Fin d) (Fin d) ℝ) *
          (D.transpose * D) * (star U : Matrix (Fin d) (Fin d) ℝ) := by
        simp [F, Matrix.transpose_mul, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mul_assoc]
      _ = C := by
        rw [hD]
        simpa [U, Unitary.conjStarAlgAut_apply] using hC.isHermitian.spectral_theorem.symm
  have hs : F.det^2 = C.det := by
    simpa [Matrix.det_mul, pow_two] using congrArg Matrix.det hF
  have ha : |F.det| = Real.sqrt C.det := by rw [← hs, Real.sqrt_sq_eq_abs]
  refine ⟨F, hF, ha, ?_⟩
  intro hz
  have := hC.det_pos
  rw [← hs, hz] at this
  norm_num at this

theorem factor_norm {d : ℕ} (F : Matrix (Fin d) (Fin d) ℝ) (z : E d) :
    ‖F.toEuclideanLin z‖^2 = quadratic (F.transpose * F) (WithLp.ofLp z) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    Matrix.toLpLin_apply]
  rw [quadratic, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec]

def ellipsoid {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (R : ℝ) : Set (E d) :=
  {z | quadratic C (WithLp.ofLp z) ≤ R^2}

theorem ellipsoid_preimage {d : ℕ} (C F : Matrix (Fin d) (Fin d) ℝ)
    (hF : F.transpose * F = C) (R : ℝ) (hR : 0 ≤ R) :
    ellipsoid C R = F.toEuclideanLin ⁻¹' Metric.closedBall 0 R := by
  ext z
  simp only [ellipsoid, Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right, ← hF, ← factor_norm]
  exact sq_le_sq₀ (norm_nonneg _) hR

theorem ellipsoid_compact_convex {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : C.PosDef) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (ellipsoid C R) ∧ Convex ℝ (ellipsoid C R) := by
  obtain ⟨F, hF, _, hdet⟩ := factor_exists C hC
  rw [ellipsoid_preimage C F hF R hR]
  have hf : LinearMap.det F.toEuclideanLin ≠ 0 := by simpa using hdet
  let H := (F.toEuclideanLin.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph
  exact ⟨H.isCompact_preimage.mpr (isCompact_closedBall 0 R),
    (convex_closedBall (0 : E d) R).linear_preimage F.toEuclideanLin⟩

theorem ellipsoid_volume {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : C.PosDef) (R : ℝ) (hR : 0 < R) :
    ChartGeometry.bodyVolume (ellipsoid C R) =
      ChartGeometry.ballVolume d * R^d / Real.sqrt C.det := by
  by_cases hd : d = 0
  · subst d
    have he : ellipsoid C R = Set.univ := by ext z; simp [ellipsoid, quadratic, sq_nonneg]
    have hb : Metric.closedBall (0 : E 0) 1 = Set.univ := by
      ext z
      rw [Subsingleton.elim z 0]
      simp
    simp [he, hb, ChartGeometry.bodyVolume, ChartGeometry.ballVolume, Matrix.det_isEmpty]
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  obtain ⟨F, hF, ha, hdet⟩ := factor_exists C hC
  have hf : LinearMap.det F.toEuclideanLin ≠ 0 := by simpa using hdet
  unfold ChartGeometry.bodyVolume
  rw [ellipsoid_preimage C F hF R hR.le,
    MeasureTheory.Measure.addHaar_preimage_linearMap MeasureTheory.volume hf,
    ENNReal.toReal_mul]
  have hball : (MeasureTheory.volume (Metric.closedBall (0 : E d) R)).toReal =
      R^d * ChartGeometry.ballVolume d := by
    rw [EuclideanSpace.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hR.le]
    simp only [Fintype.card_fin]
    congr 1
    simp [ChartGeometry.ballVolume, EuclideanSpace.volume_closedBall]
  rw [hball]
  simp only [Matrix.toEuclideanLin, LinearMap.det_toLpLin, abs_inv, ha]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  ring

def splitLast (d : ℕ) : E (d+1) ≃ₗ[ℝ] ℝ × E d where
  toFun w := (w (Fin.last d), WithLp.toLp 2 (fun j => w j.castSucc))
  invFun p := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp p.2) p.1)
  left_inv w := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_smul' s x := by ext <;> simp

theorem splitLast_preserving (d : ℕ) :
    MeasureTheory.MeasurePreserving (splitLast d) := by
  have h := ((MeasureTheory.MeasurePreserving.id (MeasureTheory.volume (α := ℝ))).prod
    (PiLp.volume_preserving_toLp (Fin d))).comp
      ((MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ)
        (Fin.last d)).comp (PiLp.volume_preserving_ofLp (Fin (d+1))))
  convert h using 1
  · ext w <;> simp [splitLast, MeasurableEquiv.piFinSuccAbove, Fin.init]
  · rfl

theorem straight_preimage (T : ChartGeometry r q) :
    T.straightCylinder = splitLast (r-q) ⁻¹'
      (Set.Icc T.lower T.upper ×ˢ ellipsoid (T.C T.Sigma) T.R) := by
  rfl

theorem straight_compact_convex (T : ChartGeometry r q) (h : T.Sigma.PosDef)
    (hR : 0 < T.R) : IsCompact T.straightCylinder ∧ Convex ℝ T.straightCylinder := by
  obtain ⟨hc, hv⟩ := ellipsoid_compact_convex (T.C T.Sigma) (C_posDef T h) T.R hR.le
  rw [straight_preimage]
  exact ⟨(splitLast (r-q)).toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr
    (isCompact_Icc.prod hc),
    (convex_Icc T.lower T.upper |>.prod hv).linear_preimage (splitLast (r-q)).toLinearMap⟩

theorem straight_volume (T : ChartGeometry r q) (h : T.Sigma.PosDef)
    (hR : 0 < T.R) (hI : T.lower ≤ T.upper) :
    ChartGeometry.bodyVolume T.straightCylinder = T.cylinderVolume := by
  have hm : MeasurableSet (ellipsoid (T.C T.Sigma) T.R) :=
    (ellipsoid_compact_convex _ (C_posDef T h) _ hR.le).1.measurableSet
  rw [ChartGeometry.bodyVolume, straight_preimage,
    (splitLast_preserving (r-q)).measure_preimage
      (measurableSet_Icc.prod hm).nullMeasurableSet,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, ENNReal.toReal_mul]
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hI)]
  change (T.upper - T.lower) * ChartGeometry.bodyVolume (ellipsoid (T.C T.Sigma) T.R) = _
  rw [ellipsoid_volume _ (C_posDef T h) _ hR]
  simp only [ChartGeometry.cylinderVolume, ChartGeometry.intervalLength]
  ring

def shearOffset (T : ChartGeometry r q) : E (r-q+1) :=
  WithLp.toLp 2 (Fin.snoc (T.ell 0) 0)

theorem shear_linear (T : ChartGeometry r q) (w : E (r-q+1)) :
    T.shear w = T.shearMatrix.toEuclideanLin w + shearOffset T := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [ChartGeometry.shear, ChartGeometry.shearMatrix, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, shearOffset]
  · simp only [ChartGeometry.shear, Fin.snoc_castSucc,
      Pi.add_apply, PiLp.add_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, ChartGeometry.shearMatrix,
      Fin.lastCases_castSucc, Fin.castSucc_ne_last, ↓reduceIte,
      shearOffset]
    have he := congrFun (ell_affine T (w (Fin.last (r-q)))) k
    simp at he
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using congrArg
      (fun a => w k.castSucc + a) he

theorem envelope_preimage (T : ChartGeometry r q) :
    T.envelope = T.shear ⁻¹' T.straightCylinder := by
  ext w
  simp [ChartGeometry.envelope, ChartGeometry.shear, ChartGeometry.straightCylinder,
    Pi.add_def]

theorem envelope_compact_convex (T : ChartGeometry r q) (h : T.Sigma.PosDef)
    (hR : 0 < T.R) : IsCompact T.envelope ∧ Convex ℝ T.envelope := by
  obtain ⟨hc, hv⟩ := straight_compact_convex T h hR
  have hd : LinearMap.det T.shearMatrix.toEuclideanLin ≠ 0 := by
    simpa using ne_of_eq_of_ne (shear_det T) one_ne_zero
  let L := (T.shearMatrix.toEuclideanLin.equivOfDetNeZero hd).toContinuousLinearEquiv
  let H := L.toHomeomorph.trans (Homeomorph.addRight (shearOffset T))
  have he : T.envelope = H ⁻¹' T.straightCylinder := by
    rw [envelope_preimage]
    congr 1
    exact funext (shear_linear T)
  refine ⟨he ▸ H.isCompact_preimage.mpr hc, ?_⟩
  rw [envelope_preimage]
  change Convex ℝ ((fun w => T.shear w) ⁻¹' T.straightCylinder)
  simp_rw [shear_linear]
  exact (hv.translate_preimage_left (shearOffset T)).linear_preimage
    T.shearMatrix.toEuclideanLin

theorem envelope_volume (T : ChartGeometry r q) (h : T.Sigma.PosDef)
    (hR : 0 < T.R) (hI : T.lower ≤ T.upper) :
    ChartGeometry.bodyVolume T.envelope = T.cylinderVolume := by
  have hd : LinearMap.det T.shearMatrix.toEuclideanLin ≠ 0 := by
    simpa using ne_of_eq_of_ne (shear_det T) one_ne_zero
  have he : T.envelope = T.shearMatrix.toEuclideanLin ⁻¹'
      ((fun w => w + shearOffset T) ⁻¹' T.straightCylinder) := by
    rw [envelope_preimage]
    ext w
    simp only [Set.mem_preimage, shear_linear]
  rw [ChartGeometry.bodyVolume, he,
    MeasureTheory.Measure.addHaar_preimage_linearMap MeasureTheory.volume hd,
    Matrix.toEuclideanLin, LinearMap.det_toLpLin, shear_det]
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_mul,
    MeasureTheory.measure_preimage_add_right]
  exact straight_volume T h hR hI

theorem differenceBody_homothety {d : ℕ} (D : Set (E d)) (c : E d)
    (hv : Convex ℝ D) (hs : ∀ w, w ∈ D ↔ 2 • c - w ∈ D) :
    differenceBody D = AffineMap.homothety (2 • c) (2 : ℝ) '' D := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    let m := (1/2 : ℝ) • x + (1/2 : ℝ) • (2 • c - y)
    have hm : m ∈ D := hv hx ((hs y).mp hy) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨m, hm, ?_⟩
    ext i
    simp [m, AffineMap.homothety_apply]
    ring
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, 2 • c - w, (hs w).mp hw, ?_⟩
    ext i
    simp [AffineMap.homothety_apply]
    ring

theorem difference_volume (T : ChartGeometry r q) (h : T.Sigma.PosDef)
    (hR : 0 < T.R) :
    ChartGeometry.bodyVolume (differenceBody T.envelope) =
      (2 : ℝ)^(r-q+1) * ChartGeometry.bodyVolume T.envelope := by
  rw [ChartGeometry.bodyVolume, differenceBody_homothety T.envelope T.envelopeCenter
      (envelope_compact_convex T h hR).2 (envelope_symmetric T),
    MeasureTheory.Measure.addHaar_image_homothety, ENNReal.toReal_mul]
  simp [abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _),
    ChartGeometry.bodyVolume]

theorem shearedCylinderEnvelope : ShearedCylinderEnvelope := by
  intro r q T _ _ h hR hI
  exact ⟨C_posDef T h, completed_square T h, section_subset T h, shear_bijOn T,
    shear_det T, (envelope_compact_convex T h hR).1, (envelope_compact_convex T h hR).2,
    envelope_symmetric T, envelope_volume T h hR hI, difference_volume T h hR⟩

end Praxis.Algebra.Trans.ChartShear
