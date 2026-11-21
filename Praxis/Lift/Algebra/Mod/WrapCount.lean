import Praxis.Lift.Algebra.Mod.WrapSupport
import Praxis.Algebra.Trans.ChartIndex
import Praxis.Algebra.Trans.ChartShear
import Praxis.Algebra.Trans.ChartCount
import Praxis.Lift.Record
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Trans.ChartModel
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

open Finset Module Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.WrapCount

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Lift.Algebra.Mod.Definitions

theorem sectionCount4_fullRank (hc : SectionCount4) (L : FullLat 4) (b a : E 4)
    (C : Set (E 4)) (S : Finset (E 4)) (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) (hsymm : CentrallySymmetric C)
    (hcontained : ∀ x ∈ S, a + x ∈ C)
    (hcoset : InCoset L b S) (hdim : spanDim S = 4) :
    (S.card : ℝ) ≤ 15552 * Algebra.Trans.ChartGeometry.bodyVolume C / L.det := by
  classical
  let chart : (⊤ : Submodule ℝ (E 4)) ≃ₗᵢ[ℝ] E 4 :=
    LinearIsometryEquiv.ofTop (E 4) _ rfl
  let lift : E 4 → (⊤ : Submodule ℝ (E 4)) := fun x => ⟨x, Submodule.mem_top⟩
  have hi : Function.Injective lift := fun _ _ h => congrArg Subtype.val h
  have himage : (S.image lift).image chart = S := by
    rw [Finset.image_image]
    change S.image id = S
    exact Finset.image_id
  have h := (hc 4 (by decide) ⊤ chart L a b C (S.image lift) hcompact hconvex
    (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact hcontained y hy)
    (by rw [himage]; exact hcoset) (by rw [himage]; exact hdim)).2 hsymm
  rw [Finset.card_image_of_injective _ hi] at h
  simp_rw [Algebra.Trans.ChartCountProof.sectionVolume_top] at h
  norm_num at h
  exact h.2

theorem real_span_top {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : Matrix (Fin 4) κ ℤ) (hr : Analysis.rationalRank D = 4) :
    Submodule.span ℝ (Set.range (D.map (Int.castRingHom ℝ)).col) = ⊤ := by
  have hm : ∃ (I : Fin 4 → Fin 4) (J : Fin 4 → κ),
      ((D.map (Int.castRingHom ℚ)).submatrix I J).det ≠ 0 := by
    have h := Analysis.exists_rank_minor (D.map (Int.castRingHom ℚ))
    change (D.map (Int.castRingHom ℚ)).rank = 4 at hr
    rw [hr] at h
    exact h
  obtain ⟨I, J, hij⟩ := hm
  have hz : (D.submatrix I J).det ≠ 0 := by
    intro he
    have hcast : ((D.map (Int.castRingHom ℚ)).submatrix I J).det =
        ((D.submatrix I J).det : ℚ) := (Int.cast_det _).symm
    exact hij (by rw [hcast, he, Int.cast_zero])
  have hR : ((D.map (Int.castRingHom ℝ)).submatrix I J).det ≠ 0 := by
    have hcast : ((D.map (Int.castRingHom ℝ)).submatrix I J).det =
        ((D.submatrix I J).det : ℝ) := (Int.cast_det _).symm
    rw [hcast]
    exact_mod_cast hz
  have hrR : (D.map (Int.castRingHom ℝ)).rank = 4 := by
    apply le_antisymm
    · simpa using (D.map (Int.castRingHom ℝ)).rank_le_card_height
    · have hsub := (D.map (Int.castRingHom ℝ)).rank_submatrix_le I J
      rw [Matrix.rank_of_det_ne_zero hR] at hsub
      simpa using hsub
  apply Submodule.eq_top_of_finrank_eq
  simpa only [← Matrix.rank_eq_finrank_span_cols, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using hrR

def coords (x : Option (Fin 3) → ℤ) : Fin 4 → ℤ :=
  fun i => x ((finSuccEquiv' (Fin.last 3)) i)

@[simp] theorem coords_last (x : Option (Fin 3) → ℤ) :
    coords x (Fin.last 3) = x none := by simp [coords]

@[simp] theorem coords_three (x : Option (Fin 3) → ℤ) :
    coords x 3 = x none := coords_last x

@[simp] theorem coords_old (x : Option (Fin 3) → ℤ) (j : Fin 3) :
    coords x j.castSucc = x (some j) := by
  simp only [coords, finSuccEquiv'_below (Fin.castSucc_lt_last j)]

def realCoords (x : Option (Fin 3) → ℤ) : E 4 :=
  Algebra.Trans.ChartBasis.castCoordinates 4 (coords x)

theorem realCoords_injective : Function.Injective realCoords := by
  intro x y h
  have he : coords x = coords y := Algebra.Trans.ChartIndex.cast_injective 4 h
  funext i
  cases i with
  | none => simpa only [coords_last] using congrFun he (Fin.last 3)
  | some j => simpa only [coords_old] using congrFun he j.castSucc

def coordsEquiv : (Option (Fin 3) → ℤ) ≃+ (Fin 4 → ℤ) where
  toFun := coords
  invFun y := fun i => i.elim (y (Fin.last 3)) (fun j => y j.castSucc)
  left_inv x := by ext i; cases i <;> simp
  right_inv y := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_add' x y := by ext i; rfl

theorem congruence_lattice {p : ℕ} [Fact p.Prime]
    (c : Option (Fin 3) → ZMod p) (hc : c ≠ 0) :
    ∃ L : FullLat 4, L.det = (p : ℝ) ∧
      ∀ x ∈ congruenceKernel p c, realCoords x ∈ L.carrier := by
  let H := ((congruenceKernel p c).map coordsEquiv.toAddMonoidHom).toIntSubmodule
  have hi : H.toAddSubgroup.index = p := by
    change ((congruenceKernel p c).map coordsEquiv.toAddMonoidHom).index = p
    rw [AddSubgroup.index_map_of_bijective coordsEquiv.bijective,
      AddSubgroup.index_eq_card]
    exact Algebra.Mod.Wrap3.congruenceKernel_card c hc
  have hne : H.toAddSubgroup.index ≠ 0 := by
    rw [hi]
    exact (Fact.out : p.Prime).ne_zero
  obtain ⟨L, hL, hdet⟩ := Algebra.Trans.ChartIndex.finite_index_lattice H hne
  refine ⟨L, by rw [hdet, hi], ?_⟩
  intro x hx
  rw [hL]
  exact ⟨coords x, ⟨x, hx, rfl⟩, rfl⟩

theorem image_spanDim {A : Type*} [Fintype A] [DecidableEq A]
    (X : A → Option (Fin 3) → ℤ) (F : Finset A)
    (hr : Analysis.rationalRank (imageDifferences X F) = 4) :
    spanDim (F.image (fun r => realCoords (X r))) = 4 := by
  classical
  let D := imageDifferences X F
  let e : Fin 4 ≃ Option (Fin 3) := finSuccEquiv' (Fin.last 3)
  let D' : Matrix (Fin 4) (F × F) ℤ := D.submatrix e id
  have hr' : Analysis.rationalRank D' = 4 := by
    change ((D.map (Int.castRingHom ℚ)).submatrix e (Equiv.refl _)).rank = 4
    rw [Matrix.rank_submatrix _ e (Equiv.refl _)]
    exact hr
  let V := vectorSpan ℝ ((F.image (fun r => realCoords (X r))) : Set (E 4))
  have hcol : ∀ j, WithLp.toLp 2 ((D'.map (Int.castRingHom ℝ)).col j) ∈ V := by
    intro j
    have hm := vsub_mem_vectorSpan ℝ
      (Finset.mem_image_of_mem (fun r => realCoords (X r)) j.1.property)
      (Finset.mem_image_of_mem (fun r => realCoords (X r)) j.2.property)
    convert hm using 1
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [D', D, imageDifferences, e, realCoords,
        Algebra.Trans.ChartBasis.castCoordinates, Int.cast_sub]
    · have hek : e k.castSucc = some k := finSuccEquiv'_below (Fin.castSucc_lt_last k)
      change ((X j.1.val (e k.castSucc) - X j.2.val (e k.castSucc) : ℤ) : ℝ) =
        realCoords (X j.1.val) k.castSucc - realCoords (X j.2.val) k.castSucc
      rw [hek]
      simp [realCoords, Algebra.Trans.ChartBasis.castCoordinates, Int.cast_sub]
  have ht := real_span_top D' hr'
  have hmap : Submodule.span ℝ
      (Set.range (fun j => WithLp.toLp 2 ((D'.map (Int.castRingHom ℝ)).col j))) = ⊤ := by
    change Submodule.span ℝ (Set.range
      ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm ∘ (D'.map (Int.castRingHom ℝ)).col)) = ⊤
    rw [Set.range_comp]
    change Submodule.span ℝ
      ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap ''
        Set.range (D'.map (Int.castRingHom ℝ)).col) = ⊤
    rw [← Submodule.map_span, ht, Submodule.map_top]
    exact LinearEquiv.range (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm
  have hv : V = ⊤ := by
    apply top_unique
    rw [← hmap]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hcol j)
  change Module.finrank ℝ V = 4
  rw [hv]
  simp

theorem image_count_in_body {A : Type*} [Fintype A] [DecidableEq A]
    {p : ℕ} [Fact p.Prime] (hcount : SectionCount4)
    (X : A → Option (Fin 3) → ℤ) (F : Finset A) (hne : F.Nonempty)
    (c : Option (Fin 3) → ZMod p) (hc : c ≠ 0) (t : ZMod p)
    (hf : ∀ r ∈ F, ∑ i, c i * (X r i : ZMod p) = t)
    (hr : Analysis.rationalRank (imageDifferences X F) = 4)
    (C : Set (E 4)) (a : E 4) (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) (hsymm : CentrallySymmetric C)
    (hcontained : ∀ r ∈ F, a + realCoords (X r) ∈ C) :
    ((F.image X).card : ℝ) ≤
      15552 * Algebra.Trans.ChartGeometry.bodyVolume C / (p : ℝ) := by
  classical
  obtain ⟨L, hdet, hL⟩ := congruence_lattice c hc
  obtain ⟨y, hy⟩ := Algebra.Mod.Wrap3.fibre_in_coset X c t F hne hf
  let S := F.image (fun r => realCoords (X r))
  have hs : InCoset L (realCoords y) S := by
    intro z hz
    obtain ⟨r, hrF, rfl⟩ := Finset.mem_image.mp hz
    have hsub : realCoords (X r) - realCoords y = realCoords (X r - y) := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp [realCoords, Algebra.Trans.ChartBasis.castCoordinates]
    rw [hsub]
    exact hL _ (hy r hrF)
  have h := sectionCount4_fullRank hcount L (realCoords y) a C S hcompact hconvex
    hsymm (by intro z hz; obtain ⟨r, hrF, rfl⟩ := Finset.mem_image.mp hz
              exact hcontained r hrF) hs (image_spanDim X F hr)
  have hcard : S.card = (F.image X).card := by
    change (F.image (realCoords ∘ X)).card = _
    rw [← Finset.image_image, Finset.card_image_of_injective _ realCoords_injective]
  simpa only [hcard, hdet] using h

open Praxis.Algebra.Trans Praxis.Algebra.Trans.ChartShear

open Praxis.Algebra.Trans hiding Transition32 Transition21 Transition31

def cylinder (Sigma : Matrix (Fin 3) (Fin 3) ℝ) (R w : ℝ) : Set (E 4) :=
  splitLast 3 ⁻¹' (Set.Icc (-w / 2) (w / 2) ×ˢ ellipsoid Sigma⁻¹ R)

theorem cylinder_compact_convex (Sigma : Matrix (Fin 3) (Fin 3) ℝ)
    (hSigma : Sigma.PosDef) (R w : ℝ) (hR : 0 ≤ R) :
    IsCompact (cylinder Sigma R w) ∧ Convex ℝ (cylinder Sigma R w) := by
  obtain ⟨hc, hv⟩ := ellipsoid_compact_convex Sigma⁻¹
    (Matrix.posDef_inv_iff.mpr hSigma) R hR
  exact ⟨(splitLast 3).toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr
      (isCompact_Icc.prod hc),
    ((convex_Icc (-w/2) (w/2)).prod hv).linear_preimage (splitLast 3).toLinearMap⟩

theorem cylinder_symmetric (Sigma : Matrix (Fin 3) (Fin 3) ℝ) (R w : ℝ) :
    CentrallySymmetric (cylinder Sigma R w) := by
  intro z
  have hq : quadratic Sigma⁻¹ (fun j => (-z) j.castSucc) =
      quadratic Sigma⁻¹ (fun j => z j.castSucc) := by
    change quadratic Sigma⁻¹ (-(fun j => z j.castSucc)) = _
    simp [quadratic, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg]
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [splitLast, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.neg_apply, Set.mem_Icc, ellipsoid, Set.mem_setOf_eq, hq]
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [show quadratic Sigma⁻¹ (fun j => -z j.castSucc) =
      quadratic Sigma⁻¹ (fun j => z j.castSucc) from hq]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩

theorem ballVolume_three : ChartGeometry.ballVolume 3 = 4 * Real.pi / 3 := by
  unfold ChartGeometry.ballVolume
  rw [InnerProductSpace.volume_closedBall_of_dim_odd (k := 1) (by simp)]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem cylinder_volume (Sigma : Matrix (Fin 3) (Fin 3) ℝ)
    (hSigma : Sigma.PosDef) (R w : ℝ) (hR : 0 < R) (hw : 0 ≤ w) :
    ChartGeometry.bodyVolume (cylinder Sigma R w) =
      w * (4 * Real.pi / 3) * R^3 * Real.sqrt Sigma.det := by
  have hInv := Matrix.posDef_inv_iff.mpr hSigma
  have hm := (ellipsoid_compact_convex Sigma⁻¹ hInv R hR.le).1.measurableSet
  rw [ChartGeometry.bodyVolume, cylinder,
    (splitLast_preserving 3).measure_preimage
      (measurableSet_Icc.prod hm).nullMeasurableSet,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, ENNReal.toReal_mul,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ w/2 - -w/2)]
  change (w/2 - -w/2) * ChartGeometry.bodyVolume (ellipsoid Sigma⁻¹ R) = _
  rw [ellipsoid_volume _ hInv _ hR, ballVolume_three, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', Real.sqrt_inv, div_inv_eq_mul]
  ring

theorem trimmed_image_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcount : SectionCount4) (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι 3) (c : Option (Fin 3) → ZMod P.p) (hc : c ≠ 0) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) (hne : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t)
    (ht : Trimmed P.toVITData G Gx L.matrix F)
    (hr : Analysis.rationalRank (imageDifferences (stepImage G Gx L.matrix) F) = 4)
    (hSigma : (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).PosDef) :
    ((F.image (stepImage G Gx L.matrix)).card : ℝ) ≤
      15552 * (4 * Real.pi / 3) * P.R^3 * (Gx : ℝ) *
        Real.sqrt (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det /
          (P.p : ℝ) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  let Sigma := Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))
  let center : E 4 := WithLp.toLp 2
    (Fin.snoc (imageCenter G L.matrix) ((Gx : ℝ)/2))
  have hR : 0 < P.R := P.R_pos
  have hcontained : ∀ r ∈ F,
      -center + realCoords (stepImage G Gx L.matrix r) ∈ cylinder Sigma P.R (Gx : ℝ) := by
    intro r hrF
    change (_ ∈ Set.Icc _ _) ∧ _
    constructor
    · have h0 : (0 : ℝ) ≤ ((r none : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : ((r none : ℕ) : ℝ) ≤ (Gx : ℝ) := by
        exact_mod_cast (r none).isLt.le
      change -center (Fin.last 3) + realCoords (stepImage G Gx L.matrix r) (Fin.last 3)
        ∈ Set.Icc _ _
      simp only [center, Fin.snoc_last, realCoords,
        Algebra.Trans.ChartBasis.castCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
        coords_last, Wrap3.stepImage_none, Int.cast_natCast]
      constructor <;> linarith
    · have h := ht r hrF
      change quadratic Sigma⁻¹
        (fun j => (-center + realCoords (stepImage G Gx L.matrix r)) j.castSucc) ≤ P.R^2
      convert h using 1
      unfold quadratic Analysis.mahalanobisSq
      congr 2 <;> ext j <;>
        simp [center, realCoords, Algebra.Trans.ChartBasis.castCoordinates,
          Fin.snoc_castSucc, sub_eq_add_neg, add_comm]
  have hgeom := image_count_in_body hcount (stepImage G Gx L.matrix) F hne c hc t hf hr
    (cylinder Sigma P.R (Gx : ℝ)) (-center)
    (cylinder_compact_convex Sigma hSigma P.R (Gx : ℝ) hR.le).1
    (cylinder_compact_convex Sigma hSigma P.R (Gx : ℝ) hR.le).2
    (cylinder_symmetric Sigma P.R (Gx : ℝ)) hcontained
  rw [cylinder_volume Sigma hSigma P.R (Gx : ℝ) hR (Nat.cast_nonneg _)] at hgeom
  convert hgeom using 1 <;> ring

end Algebra.Mod.WrapCount

end Praxis.Lift
