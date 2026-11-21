import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Trans.GramBridge
import Praxis.Algebra.Trim.Definitions
import Praxis.Algebra.Trans.ChartIndex
import Praxis.Algebra.Trans.ChartCount
import Praxis.Algebra.Trans.ChartShear
import Mathlib.GroupTheory.QuotientGroup.Basic
import Praxis.Lift.Record
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.ChartModel
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators

open Praxis.Algebra.Inverse.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.Wrap2

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Lift.Algebra.Mod.Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def congruenceHom {d p : ℕ} (c : Option (Fin d) → ZMod p) :
    (Option (Fin d) → ℤ) →+ ZMod p where
  toFun x := ∑ i, c i * (x i : ZMod p)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

theorem congruenceHom_ker {d p : ℕ} (c : Option (Fin d) → ZMod p) :
    (congruenceHom c).ker = congruenceKernel p c := by
  ext x
  rfl

theorem congruenceHom_surjective {d p : ℕ} [Fact p.Prime]
    (c : Option (Fin d) → ZMod p) (hc : c ≠ 0) :
    Function.Surjective (congruenceHom c) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := Function.ne_iff.mp hc
  intro t
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (t / c i)
  refine ⟨Pi.single i z, ?_⟩
  change (∑ j, c j * (((Pi.single i z : Option (Fin d) → ℤ) j : ℤ) : ZMod p)) = t
  rw [Finset.sum_eq_single i]
  · simp [hz, div_eq_mul_inv, mul_left_comm, hi]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem congruenceKernel_card {d p : ℕ} [Fact p.Prime]
    (c : Option (Fin d) → ZMod p) (hc : c ≠ 0) :
    Nat.card ((Option (Fin d) → ℤ) ⧸ congruenceKernel p c) = p := by
  rw [← congruenceHom_ker c]
  have h := Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective (congruenceHom c)
      (congruenceHom_surjective c hc)).toEquiv
  simpa using h

theorem fibre_in_coset {d p : ℕ} {A : Type*} [Fintype A]
    (X : A → Option (Fin d) → ℤ) (c : Option (Fin d) → ZMod p)
    (t : ZMod p) (F : Finset A) (hF : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (X r i : ZMod p) = t) :
    ∃ y : Option (Fin d) → ℤ, ∀ r ∈ F, X r - y ∈ congruenceKernel p c := by
  obtain ⟨r₀, hr₀⟩ := hF
  refine ⟨X r₀, ?_⟩
  intro r hr
  change (∑ i, c i * ((X r - X r₀) i : ZMod p)) = 0
  simp only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib,
    hf r hr, hf r₀ hr₀, sub_self]

theorem stepImage_none {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) :
    stepImage G Gx B r none = ((r none : ℕ) : ℤ) := by
  simp [stepImage, Matrix.mulVec, dotProduct, stepMatrix, Fintype.sum_option]

theorem stepImage_some {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) (j : Fin d) :
    stepImage G Gx B r (some j) = imageZ G B (fun i => r (some i)) j := by
  simp [stepImage, Matrix.mulVec, dotProduct, stepMatrix, Fintype.sum_option, imageZ]

open Praxis.Algebra.Trans

open Praxis.Algebra.Trans hiding Transition32 Transition21 Transition31

theorem real_minor_le_height {d : ℕ} (B : Matrix ι (Fin d) ℤ) (f : Fin d → ι) :
    |((B.map (Int.castRingHom ℝ)).submatrix f id).det| ≤ (height B : ℝ) := by
  have hn : (B.submatrix f id).det.natAbs ≤ height B :=
    Finset.le_sup (f := fun q : Fin d → ι => (B.submatrix q id).det.natAbs)
      (Finset.mem_univ f)
  have he : ((B.map (Int.castRingHom ℝ)).submatrix f id).det =
      ((B.submatrix f id).det : ℝ) := by
    exact (Int.cast_det _).symm
  rw [he]
  have hn' : ((B.submatrix f id).det.natAbs : ℝ) ≤ (height B : ℝ) := by
    exact_mod_cast hn
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hn'

theorem weightedGram_det_le_height [LinearOrder ι] {d : ℕ}
    (B : Matrix ι (Fin d) ℤ) (sigma : ι → ℝ)
    (hCB : CauchyBinet3 (B.map (Int.castRingHom ℝ)) sigma) (hd : d ≤ 3) :
    (weightedGram (B.map (Int.castRingHom ℝ)) sigma).det ≤
      (height B : ℝ)^2 * elementarySymmetric (fun i => sigma i^2) d := by
  classical
  rw [hCB hd, elementarySymmetric, Finset.esymm_map_val, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I hI
  have hc : I.card = d := (Finset.mem_powersetCard.mp hI).2
  have hm := real_minor_le_height B (I.orderEmbOfFin hc)
  have hs : rowMinor (B.map (Int.castRingHom ℝ)) I ^ 2 ≤ (height B : ℝ)^2 := by
    rw [rowMinor, dif_pos hc]
    nlinarith [abs_nonneg (((B.map (Int.castRingHom ℝ)).submatrix
      (I.orderEmbOfFin hc) id).det), sq_abs (((B.map (Int.castRingHom ℝ)).submatrix
      (I.orderEmbOfFin hc) id).det)]
  exact mul_le_mul_of_nonneg_right hs (Finset.prod_nonneg (fun i _ => sq_nonneg _))

theorem covariance_det_le [LinearOrder ι] (P : VITParameters)
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 2)
    (hbudget : GridBudget P.toVITData (extend G Gx))
    (hCB : CauchyBinet3 (L.matrix.map (Int.castRingHom ℝ))
      (fun i => (G i : ℝ) / Real.sqrt 12))
    (he : ESymBounds (fun i => ((G i : ℝ) / Real.sqrt 12)^2)
      (∑ i, ((G i : ℝ) / Real.sqrt 12)^2)) :
    (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det ≤
      (L.H : ℝ)^2 * ((P.g : ℝ)^2 * P.S)^2 / (12^2 * 2) := by
  have hsum : (∑ i, (G i : ℝ)^2) ≤ (P.g : ℝ)^2 * P.S := by
    have hb := hbudget.2.1
    simp only [Fintype.sum_option, extend, Option.elim_none, Option.elim_some] at hb
    nlinarith [sq_nonneg (Gx : ℝ)]
  have hsigma : (∑ i, ((G i : ℝ) / Real.sqrt 12)^2) =
      (∑ i, (G i : ℝ)^2) / 12 := by
    simp_rw [gridSigma_sq]
    rw [Finset.sum_div]
  have hes := (he (fun i => sq_nonneg _) rfl).1
  have hdet := weightedGram_det_le_height L.matrix _ hCB (by decide)
  rw [weightedGram_gridSigma] at hdet
  have hmul := mul_le_mul_of_nonneg_left hes (sq_nonneg (L.H : ℝ))
  have hsq : ((∑ i, (G i : ℝ)^2) / 12)^2 ≤
      ((P.g : ℝ)^2 * P.S / 12)^2 := by
    have hS := P.S_pos
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    exact div_le_div_of_nonneg_right hsum (by norm_num)
  rw [hsigma] at hmul
  have hmul2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg (L.H : ℝ))
  change _ ≤ (L.H : ℝ)^2 * _ at hdet
  nlinarith

theorem density_le_image_mul_mass {A Y : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq Y] [Nonempty Y] (f : A → Y) (F : Finset A) :
    density F ≤ ((F.image f).card : ℝ) * Algebra.FiniteProbability.atomMass f := by
  classical
  have hcard := Finset.card_eq_sum_card_image f F
  have hf (y : Y) : ((F.filter (fun x => f x = y)).card : ℝ) /
      (Fintype.card A : ℝ) ≤ Algebra.FiniteProbability.atomMass f := by
    calc
      _ ≤ Algebra.FiniteProbability.pointProb f y := by
        unfold Algebra.FiniteProbability.pointProb Algebra.FiniteProbability.fibreCount
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
      _ ≤ _ := Algebra.FiniteProbability.pointProb_le_mass f y
  unfold density
  rw [hcard, Nat.cast_sum, Finset.sum_div]
  exact (Finset.sum_le_sum (fun y _ => hf y)).trans_eq (by simp)

theorem card_extended_grid (G : ι → ℕ) (Gx : ℕ) :
    Fintype.card (Grid (extend G Gx)) = Gx * Fintype.card (Grid G) := by
  change Fintype.card ((i : Option ι) → Fin ((extend G Gx) i)) =
    Gx * Fintype.card ((i : ι) → Fin (G i))
  rw [Fintype.card_pi, Fintype.card_pi]
  simp [Fintype.prod_option, extend, Fintype.card_fin]

theorem step_fibreCount_le {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (y : Option (Fin d) → ℤ) :
    Algebra.FiniteProbability.fibreCount (stepImage G Gx B) y ≤
      Algebra.FiniteProbability.fibreCount (imageZ G B) (fun j => y (some j)) := by
  classical
  unfold Algebra.FiniteProbability.fibreCount
  apply Finset.card_le_card_of_injOn
    (fun (r : Grid (extend G Gx)) (i : ι) => r (some i))
  · intro r hr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    ext j
    rw [← stepImage_some, hr]
  · intro r hr s hs he
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr hs
    funext i
    cases i with
    | none =>
      have hn := congrFun (hr.trans hs.symm) none
      rw [stepImage_none, stepImage_none] at hn
      apply Fin.ext
      exact_mod_cast hn
    | some i => exact congrFun he i

theorem step_mass_le {d : ℕ} (G : ι → ℕ) (Gx : ℕ) (hGx : 0 < Gx)
    (B : Matrix ι (Fin d) ℤ) :
    mass (extend G Gx) (stepImage G Gx B) ≤ mass G (imageZ G B) / Gx := by
  apply Algebra.FiniteProbability.atomMass_le
  intro y
  have h := step_fibreCount_le G Gx B y
  have hc : (Algebra.FiniteProbability.fibreCount (stepImage G Gx B) y : ℝ) ≤
      Algebra.FiniteProbability.fibreCount (imageZ G B) (fun j => y (some j)) := by exact_mod_cast h
  calc
    _ ≤ Algebra.FiniteProbability.pointProb (imageZ G B) (fun j => y (some j)) / Gx := by
      unfold Algebra.FiniteProbability.pointProb
      rw [card_extended_grid, Nat.cast_mul]
      exact (div_le_div_of_nonneg_right hc (by positivity)).trans_eq (by ring)
    _ ≤ _ := div_le_div_of_nonneg_right
      (Algebra.FiniteProbability.pointProb_le_mass _ _) (Nat.cast_nonneg _)

theorem density_le_image_mul_old_mass {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (hGx : 0 < Gx) (L : IntLat ι d) (F : Finset (Grid (extend G Gx))) :
    density F ≤ ((F.image (stepImage G Gx L.matrix)).card : ℝ) * L.mZ G / Gx := by
  exact (density_le_image_mul_mass _ F).trans
    ((mul_le_mul_of_nonneg_left (step_mass_le G Gx hGx L.matrix)
      (Nat.cast_nonneg _)).trans_eq (by change _ = _ * mass G (imageZ G L.matrix) / _; ring))

theorem covariance_wrap_factor [LinearOrder ι] (P : VITParameters)
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 2)
    (hbudget : GridBudget P.toVITData (extend G Gx))
    (hCB : CauchyBinet3 (L.matrix.map (Int.castRingHom ℝ))
      (fun i => (G i : ℝ) / Real.sqrt 12))
    (he : ESymBounds (fun i => ((G i : ℝ) / Real.sqrt 12)^2)
      (∑ i, ((G i : ℝ) / Real.sqrt 12)^2)) :
    648 * Real.pi * P.R^2 *
      Real.sqrt (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det ≤
      P.E * (L.H : ℝ) * (P.g : ℝ)^2 := by
  let v := (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det
  have hd := covariance_det_le P G Gx L hbudget hCB he
  change v ≤ _ at hd
  have hcoef : 0 ≤ 648 * Real.pi * P.R^2 := by positivity
  have hbound : 0 ≤ P.E * (L.H : ℝ) * (P.g : ℝ)^2 := by
    exact mul_nonneg (mul_nonneg P.E_pos.le (Nat.cast_nonneg _)) (sq_nonneg _)
  by_cases hv : v ≤ 0
  · rw [show Real.sqrt v = 0 from Real.sqrt_eq_zero_of_nonpos hv]
    simpa using hbound
  have hsv : (Real.sqrt v)^2 = v := Real.sq_sqrt (le_of_not_ge hv)
  have hmul := mul_le_mul_of_nonneg_left hd (sq_nonneg (648 * Real.pi * P.R^2))
  have hgeo := mul_le_mul_of_nonneg_left P.E_geometry
    (mul_nonneg (sq_nonneg (L.H : ℝ)) (pow_nonneg (Nat.cast_nonneg P.g) 4))
  have hsq : (648 * Real.pi * P.R^2 * Real.sqrt v)^2 ≤
      (P.E * (L.H : ℝ) * (P.g : ℝ)^2)^2 := by
    rw [mul_pow, hsv]
    nlinarith
  exact (sq_le_sq₀ (mul_nonneg hcoef (Real.sqrt_nonneg _)) hbound).mp hsq

theorem density_bound_of_image_count [LinearOrder ι] (P : VITParameters)
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 2)
    (F : Finset (Grid (extend G Gx)))
    (hbudget : GridBudget P.toVITData (extend G Gx))
    (hreg : Regular P.toVITData G L)
    (hCB : CauchyBinet3 (L.matrix.map (Int.castRingHom ℝ))
      (fun i => (G i : ℝ) / Real.sqrt 12))
    (he : ESymBounds (fun i => ((G i : ℝ) / Real.sqrt 12)^2)
      (∑ i, ((G i : ℝ) / Real.sqrt 12)^2))
    (hcount : ((F.image (stepImage G Gx L.matrix)).card : ℝ) ≤
      648 * Real.pi * P.R^2 * (Gx : ℝ) *
        Real.sqrt (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det /
          (P.p : ℝ)) :
    density F ≤ P.E * P.C2 / (P.p : ℝ) := by
  have hg : 0 < P.g := lt_of_lt_of_le (by positivity : 0 < 2^P.L0) P.g_lower
  have hx : 0 < Gx := hg.trans_le (hbudget.1 none)
  have hG : ∀ i, 0 < G i := fun i => hg.trans_le (hbudget.1 (some i))
  letI : Nonempty (Grid G) := ⟨fun i => ⟨0, hG i⟩⟩
  have hm : 0 ≤ L.mZ G := Algebra.FiniteProbability.atomMass_nonneg _
  have hpp : 0 < (P.p : ℝ) := by exact_mod_cast P.p_prime.pos
  have hxp : 0 < (Gx : ℝ) := by exact_mod_cast hx
  have hgp : 0 < (P.g : ℝ)^2 := by positivity
  have hfactor := covariance_wrap_factor P G Gx L hbudget hCB he
  have hregular : L.mZ G * (L.H : ℝ) * (P.g : ℝ)^2 ≤ P.C2 := by
    have hr : L.mZ G * (L.H : ℝ) ≤ P.C2 / (P.g : ℝ)^2 := by
      simpa [Regular, VITData.C] using hreg
    exact (le_div_iff₀ hgp).mp hr
  calc
    density F ≤ ((F.image (stepImage G Gx L.matrix)).card : ℝ) * L.mZ G / Gx :=
      density_le_image_mul_old_mass G Gx hx L F
    _ ≤ (648 * Real.pi * P.R^2 * (Gx : ℝ) *
        Real.sqrt (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det /
        (P.p : ℝ)) * L.mZ G / Gx :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hm) hxp.le
    _ = (648 * Real.pi * P.R^2 *
        Real.sqrt (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det) *
        L.mZ G / P.p := by field_simp
    _ ≤ (P.E * (L.H : ℝ) * (P.g : ℝ)^2) * L.mZ G / P.p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor hm) hpp.le
    _ ≤ P.E * P.C2 / P.p := by
      apply div_le_div_of_nonneg_right _ hpp.le
      nlinarith [mul_le_mul_of_nonneg_left hregular P.E_pos.le]

def coordinates : (Option (Fin 2) → ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) where
  toFun x j := x (finSuccEquivLast j)
  invFun x j := x (finSuccEquivLast.symm j)
  left_inv x := by ext j; simp
  right_inv x := by ext j; simp
  map_add' x y := rfl
  map_smul' a x := rfl

def realCoordinates (x : Option (Fin 2) → ℤ) : Algebra.Point.E 3 :=
  ChartBasis.castCoordinates 3 (coordinates x)

theorem realCoordinates_injective : Function.Injective realCoordinates :=
  (ChartIndex.cast_injective 3).comp coordinates.injective

theorem congruence_fullLat {p : ℕ} [Fact p.Prime]
    (c : Option (Fin 2) → ZMod p) (hc : c ≠ 0) :
    ∃ Λ : Algebra.Point.FullLat 3,
      Λ.carrier = ((congruenceKernel p c).toIntSubmodule.map coordinates.toLinearMap).map
        (ChartBasis.castCoordinates 3) ∧ Λ.det = (p : ℝ) := by
  have hi : ((congruenceKernel p c).toIntSubmodule.map
      coordinates.toLinearMap).toAddSubgroup.index = p := by
    rw [Submodule.map_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup]
    change ((congruenceKernel p c).map coordinates.toAddEquiv.toAddMonoidHom).index = p
    rw [AddSubgroup.index_map_of_bijective coordinates.toAddEquiv.bijective]
    exact congruenceKernel_card c hc
  obtain ⟨Λ, hΛ, hdet⟩ := ChartIndex.finite_index_lattice
    ((congruenceKernel p c).toIntSubmodule.map coordinates.toLinearMap)
    (by rw [hi]; exact (Fact.out : p.Prime).ne_zero)
  exact ⟨Λ, hΛ, by rw [hdet, hi]⟩

theorem real_image_in_coset {p : ℕ} [Fact p.Prime] {A : Type*} [Fintype A]
    (X : A → Option (Fin 2) → ℤ) (c : Option (Fin 2) → ZMod p)
    (t : ZMod p) (F : Finset A) (hF : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (X r i : ZMod p) = t)
    (Λ : Algebra.Point.FullLat 3)
    (hΛ : Λ.carrier =
      ((congruenceKernel p c).toIntSubmodule.map coordinates.toLinearMap).map
        (ChartBasis.castCoordinates 3)) (a : Algebra.Point.E 3) :
    ∃ b, Algebra.Point.InCoset Λ b (F.image (fun r => realCoordinates (X r) - a)) := by
  obtain ⟨y, hy⟩ := fibre_in_coset X c t F hF hf
  refine ⟨realCoordinates y - a, ?_⟩
  intro z hz
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  rw [hΛ]
  have hmem : coordinates (X r - y) ∈
      (congruenceKernel p c).toIntSubmodule.map coordinates.toLinearMap :=
    Submodule.mem_map_of_mem (hy r hr)
  have hcast := Submodule.mem_map_of_mem (f := ChartBasis.castCoordinates 3) hmem
  have he : realCoordinates (X r) - a - (realCoordinates y - a) =
      ChartBasis.castCoordinates 3 (coordinates (X r - y)) := by
    rw [map_sub, map_sub]
    change _ = realCoordinates (X r) - realCoordinates y
    abel
  rwa [he]

theorem real_image_span {A : Type*} [Fintype A] [DecidableEq A]
    (X : A → Option (Fin 2) → ℤ) (F : Finset A)
    (hrank : Analysis.rationalRank (imageDifferences X F) = 3)
    (a : Algebra.Point.E 3) :
    Algebra.Point.spanDim (F.image (fun r => realCoordinates (X r) - a)) = 3 := by
  classical
  let D := imageDifferences X F
  have hr : (D.map (Int.castRingHom ℚ)).rank = 3 := hrank
  obtain ⟨I, J, hdet⟩ : ∃ (I : Fin 3 → Option (Fin 2)) (J : Fin 3 → F × F),
      (((D.map (Int.castRingHom ℚ)).submatrix I J).det ≠ 0) := by
    rw [← hr]
    exact Analysis.exists_rank_minor (D.map (Int.castRingHom ℚ))
  have hInt : (D.submatrix I J).det ≠ 0 := by
    have hq : ((D.submatrix I J).det : ℚ) ≠ 0 := by
      rw [Int.cast_det]
      simpa only [Matrix.submatrix_map, Int.coe_castRingHom] using hdet
    exact_mod_cast hq
  have hReal : (((D.map (Int.castRingHom ℝ)).submatrix I J).det ≠ 0) := by
    have he := Int.cast_det (R := ℝ) (D.submatrix I J)
    change ((D.submatrix I J).map (fun z : ℤ => (z : ℝ))).det ≠ 0
    rw [← he]
    exact_mod_cast hInt
  let v : Fin 3 → Algebra.Point.E 3 := fun j =>
    realCoordinates (X (J j).1) - realCoordinates (X (J j).2)
  let project : Algebra.Point.E 3 →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun x j => x (finSuccEquivLast.symm (I j))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp project
    have he : project ∘ v = ((D.map (Int.castRingHom ℝ)).submatrix I J).col := by
      ext j i
      simp [project, v, LinearMap.coe_mk, realCoordinates, ChartBasis.castCoordinates, coordinates,
        Matrix.col, Matrix.submatrix_apply, D, imageDifferences]
    rw [he]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hReal
  let V := vectorSpan ℝ (↑(F.image (fun r => realCoordinates (X r) - a)) : Set (Algebra.Point.E 3))
  have hmem : ∀ j, v j ∈ V := by
    intro j
    have h₁ : realCoordinates (X (J j).1) - a ∈
        (F.image (fun r => realCoordinates (X r) - a) : Finset _) :=
      Finset.mem_image.mpr ⟨_, (J j).1.property, rfl⟩
    have h₂ : realCoordinates (X (J j).2) - a ∈
        (F.image (fun r => realCoordinates (X r) - a) : Finset _) :=
      Finset.mem_image.mpr ⟨_, (J j).2.property, rfl⟩
    have hh := vsub_mem_vectorSpan ℝ h₁ h₂
    change (realCoordinates (X (J j).1) - a) -
      (realCoordinates (X (J j).2) - a) ∈ V at hh
    have he : (realCoordinates (X (J j).1) - a) -
        (realCoordinates (X (J j).2) - a) = v j := by dsimp [v]; abel
    rwa [he] at hh
  have hlow : 3 ≤ Module.finrank ℝ V := by
    have hsub : LinearIndependent ℝ (fun j => (⟨v j, hmem j⟩ : V)) := by
      apply LinearIndependent.of_comp V.subtype
      exact hv
    simpa using hsub.fintype_card_le_finrank
  have hu : Module.finrank ℝ V ≤ 3 := by
    simpa using (Submodule.finrank_le V)
  exact le_antisymm hu hlow

open Praxis.Algebra.Point MeasureTheory

def cylinder (Sigma : Matrix (Fin 2) (Fin 2) ℝ) (R g : ℝ) : Set (E 3) :=
  ChartShear.splitLast 2 ⁻¹'
    (Set.Icc (-(g/2)) (g/2) ×ˢ ChartShear.ellipsoid Sigma⁻¹ R)

theorem cylinder_compact_convex (Sigma : Matrix (Fin 2) (Fin 2) ℝ) (hSigma : Sigma.PosDef)
    (R g : ℝ) (hR : 0 ≤ R) :
    IsCompact (cylinder Sigma R g) ∧ Convex ℝ (cylinder Sigma R g) := by
  obtain ⟨hc, hv⟩ := ChartShear.ellipsoid_compact_convex Sigma⁻¹
    (Matrix.posDef_inv_iff.mpr hSigma) R hR
  exact ⟨(ChartShear.splitLast 2).toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr
      (isCompact_Icc.prod hc),
    ((convex_Icc _ _).prod hv).linear_preimage (ChartShear.splitLast 2).toLinearMap⟩

theorem cylinder_symmetric (Sigma : Matrix (Fin 2) (Fin 2) ℝ) (R g : ℝ) :
    ∀ w, w ∈ cylinder Sigma R g ↔ -w ∈ cylinder Sigma R g := by
  intro w
  change ((-(g/2) ≤ w (Fin.last 2) ∧ w (Fin.last 2) ≤ g/2) ∧
    quadratic Sigma⁻¹ (fun j => w j.castSucc) ≤ R^2) ↔ _
  change _ ↔ ((-(g/2) ≤ -w (Fin.last 2) ∧ -w (Fin.last 2) ≤ g/2) ∧
    quadratic Sigma⁻¹ (-(fun j => w j.castSucc)) ≤ R^2)
  rw [ChartShear.quadratic_neg]
  constructor <;> rintro ⟨⟨h₁,h₂⟩, hq⟩ <;> exact ⟨⟨by linarith, by linarith⟩, hq⟩

theorem cylinder_volume (Sigma : Matrix (Fin 2) (Fin 2) ℝ) (hSigma : Sigma.PosDef)
    (R g : ℝ) (hR : 0 < R) (hg : 0 ≤ g) :
    ChartGeometry.bodyVolume (cylinder Sigma R g) =
      g * Real.pi * R^2 * Real.sqrt Sigma.det := by
  have hm : MeasurableSet (ChartShear.ellipsoid Sigma⁻¹ R) :=
    (ChartShear.ellipsoid_compact_convex _ (Matrix.posDef_inv_iff.mpr hSigma) _ hR.le).1.measurableSet
  rw [ChartGeometry.bodyVolume, cylinder,
    (ChartShear.splitLast_preserving 2).measure_preimage
      (measurableSet_Icc.prod hm).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ g/2 - -(g/2))]
  change (g/2 - -(g/2)) * ChartGeometry.bodyVolume (ChartShear.ellipsoid Sigma⁻¹ R) = _
  rw [ChartShear.ellipsoid_volume _ (Matrix.posDef_inv_iff.mpr hSigma) _ hR,
    ChartCountProof.ballVolume_two, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.sqrt_inv]
  field_simp <;> ring

theorem cylinder_difference_volume (Sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (hSigma : Sigma.PosDef) (R g : ℝ) (hR : 0 < R) :
    ChartGeometry.bodyVolume (differenceBody (cylinder Sigma R g)) =
      8 * ChartGeometry.bodyVolume (cylinder Sigma R g) := by
  rw [ChartGeometry.bodyVolume, ChartShear.differenceBody_homothety _ 0
      (cylinder_compact_convex Sigma hSigma R g hR.le).2 (by
        intro w; simpa using cylinder_symmetric Sigma R g w),
    Measure.addHaar_image_homothety, ENNReal.toReal_mul]
  norm_num [ChartGeometry.bodyVolume]

theorem image_count (hc : SectionCount3) (P : VITParameters)
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 2)
    (c : Option (Fin 2) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) (hnc : c ≠ 0) (hF : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t)
    (htrim : Trimmed P.toVITData G Gx L.matrix F)
    (hrank : Analysis.rationalRank (imageDifferences (stepImage G Gx L.matrix) F) = 3)
    (hSigma : (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).PosDef) :
    ((F.image (stepImage G Gx L.matrix)).card : ℝ) ≤
      648 * Real.pi * P.R^2 * (Gx : ℝ) *
        Real.sqrt (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det /
          (P.p : ℝ) := by
  classical
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  let Sigma := Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))
  let X := stepImage G Gx L.matrix
  let a : E 3 := WithLp.toLp 2 (Fin.snoc (imageCenter G L.matrix) ((Gx : ℝ)/2))
  let S := F.image (fun r => realCoordinates (X r) - a)
  obtain ⟨Λ, hΛ, hdet⟩ := congruence_fullLat c hnc
  obtain ⟨b, hb⟩ := real_image_in_coset X c t F hF hf Λ hΛ a
  have hR : 0 < P.R := P.R_pos
  have hcompact := (cylinder_compact_convex Sigma hSigma P.R Gx hR.le).1
  have hconvex := (cylinder_compact_convex Sigma hSigma P.R Gx hR.le).2
  have hcontained : (S : Set (E 3)) ⊆ cylinder Sigma P.R Gx := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hw
    change _ ∈ Set.Icc (-((Gx : ℝ)/2)) ((Gx : ℝ)/2) ×ˢ
      ChartShear.ellipsoid Sigma⁻¹ P.R
    constructor
    · change -((Gx : ℝ)/2) ≤ _ ∧ _ ≤ (Gx : ℝ)/2
      have hz : (0 : ℝ) ≤ ((r none : ℕ) : ℝ) := Nat.cast_nonneg _
      have hu : (((r none : ℕ)) : ℝ) < (Gx : ℝ) := by
        exact_mod_cast (r none).isLt
      change -((Gx : ℝ)/2) ≤
        (realCoordinates (X r) - a) (Fin.last 2) ∧
        (realCoordinates (X r) - a) (Fin.last 2) ≤ (Gx : ℝ)/2
      simp only [PiLp.sub_apply]
      change -((Gx : ℝ)/2) ≤ (X r none : ℝ) - (Gx : ℝ)/2 ∧
        (X r none : ℝ) - (Gx : ℝ)/2 ≤ (Gx : ℝ)/2
      dsimp only [X]
      rw [stepImage_none, Int.cast_natCast]
      constructor <;> linarith
    · have ht := htrim r hr
      change quadratic Sigma⁻¹
        (fun j => (realCoordinates (X r) - a) j.castSucc) ≤ P.R^2
      change quadratic Sigma⁻¹
        (fun j => (X r (some j) : ℝ) - imageCenter G L.matrix j) ≤ P.R^2
      exact ht
  have hdim := real_image_span X F hrank a
  have hcount := ChartCountProof.sectionCount3_fullRank hc Λ b (cylinder Sigma P.R Gx) S
    hcompact hconvex hcontained hb hdim
  have hcard : S.card = (F.image X).card := by
    change (F.image ((fun x => realCoordinates x - a) ∘ X)).card = _
    rw [← Finset.image_image, Finset.card_image_of_injective]
    exact fun x y he => realCoordinates_injective (sub_left_injective he)
  rw [hcard, hdet, cylinder_difference_volume Sigma hSigma P.R Gx hR,
    cylinder_volume Sigma hSigma P.R Gx hR (Nat.cast_nonneg _)] at hcount
  convert hcount using 1 <;> ring

end Algebra.Mod.Wrap2

end Praxis.Lift
