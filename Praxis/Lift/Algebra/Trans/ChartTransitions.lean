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
import Praxis.Lift.Algebra.Trans.ChartModel
import Praxis.Algebra.Trans.ChartTransitions
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Trans.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Trans.ChartModel
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.CovarianceTrim

set_option autoImplicit false

set_option linter.ambiguousOpen false

noncomputable section

open scoped BigOperators Matrix

open Matrix Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

namespace Praxis.Lift

namespace Algebra.Trans

open Praxis.Algebra

open Praxis.Algebra.Trans hiding Transition32 Transition21 Transition31

open Praxis.Algebra.Trans.Chart hiding Transition32 Transition21 Transition31
  transition32_compat transition21_compat transition31_compat
  transition32_of_base transition21_of_base transition31_of_base

open Praxis.Algebra.Trans.ChartTransitions hiding covariance32 covariance21 covariance31
  weight_budget D_factor pair_weight_budget E_factor transition32_index
  transition21_index transition31_index transition32 transition21 transition31
  transition32_compat transition21_compat transition31_compat

namespace TransitionInput

open Praxis.Algebra.Trans.TransitionInput hiding exists_chartData density_le_chart

variable {n r q : ℕ} (T : TransitionInput n r q)

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
    radius_pos := P.R_pos
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

theorem density_le_chart (P : VITParameters) (hcase : ChartCase r q)
    (hc : ChartCount r q) (hp : PlanarCount) (h3 : SectionCount3)
    (hT : TransitionData r q P.toVITData T) :
    T.density ≤ (if r-q+1 = 2 then 6 else 648) *
      ChartGeometry.ballVolume (r-q) * P.R^(r-q) * T.oldMass *
      Real.sqrt T.sigma.det / Real.sqrt T.normalCovariance.det := by
  obtain ⟨C, hS, hSigma, hK, hR, hI⟩ := exists_chartData T P hcase hT
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
  apply (sq_le_sq₀ (mul_nonneg (mul_nonneg (by norm_num) P.R_pos.le)
    (Real.sqrt_nonneg _)) (by positivity)).mp
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
  have hcount := TransitionInput.density_le_chart T P (Or.inl ⟨rfl, rfl⟩) hc hp h3 hT
  simp only [show 3-2+1 = 2 from rfl, show 3-2 = 1 from rfl, if_true,
    ChartCountProof.ballVolume_one, pow_one] at hcount
  have hW : 0 ≤ ∑ i, ((T.oldGrids i : ℝ) / Real.sqrt 12)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨h, hh, density_with_index hh
    (T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1).det_pos.le
    (T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1).det_pos
    (T.oldMass_nonneg hT.2.2.2.2.2.2.1)
    (show 0 ≤ 12 * P.R by linarith [P.R_pos]) hW ?_ hd
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
  have hcount := TransitionInput.density_le_chart T P (Or.inr (Or.inl ⟨rfl, rfl⟩)) hc hp h3 hT
  simp only [show 2-1+1 = 2 from rfl, show 2-1 = 1 from rfl, if_true,
    ChartCountProof.ballVolume_one, pow_one] at hcount
  have hW : 0 ≤ ∑ i, ((T.oldGrids i : ℝ) / Real.sqrt 12)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨h, hh, density_with_index hh
    (T.sigma_posDef hT.1 hT.2.2.2.2.2.2.1).det_pos.le
    (T.normalCovariance_posDef hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.1).det_pos
    (T.oldMass_nonneg hT.2.2.2.2.2.2.1)
    (show 0 ≤ 12 * P.R by linarith [P.R_pos]) hW ?_ hd
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
  have hcount := TransitionInput.density_le_chart T P (Or.inr (Or.inr ⟨rfl, rfl⟩)) hc hp h3 hT
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

end Algebra.Trans

end Praxis.Lift
