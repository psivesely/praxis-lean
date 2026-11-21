import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Algebra.Trans.ChartIndex
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Trim.Definitions
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.ChartModel
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

set_option linter.style.haveILetI false

noncomputable section

open scoped BigOperators Matrix

open Finset Praxis.Algebra.Inverse.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.Wrap1

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Lift.Algebra.Mod.Definitions

def congruenceHom {κ : Type*} [Fintype κ] {p : ℕ} (c : κ → ZMod p) :
    (κ → ℤ) →+ ZMod p where
  toFun x := ∑ i, c i * (x i : ZMod p)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, sum_add_distrib]

theorem congruenceHom_surjective {κ : Type*} [Fintype κ] [DecidableEq κ]
    {p : ℕ} (hp : p.Prime) (c : κ → ZMod p) (hc : c ≠ 0) :
    Function.Surjective (congruenceHom c) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := Function.ne_iff.mp hc
  intro t
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (t / c i)
  refine ⟨Pi.single i a, ?_⟩
  change (∑ j, c j * (((Pi.single i a : κ → ℤ) j) : ZMod p)) = t
  rw [Finset.sum_eq_single i]
  · simp [ha, hi, mul_div_cancel₀]
  · intro j _ hji
    simp [hji]
  · simp

theorem congruenceKernel_card {d p : ℕ} (hp : p.Prime)
    (c : Option (Fin d) → ZMod p) (hc : c ≠ 0) :
    Nat.card ((Option (Fin d) → ℤ) ⧸ congruenceKernel p c) = p := by
  have hk : (congruenceHom c).ker = congruenceKernel p c := by
    ext x
    rfl
  rw [← hk]
  have he := QuotientAddGroup.quotientKerEquivOfSurjective
    (congruenceHom c) (congruenceHom_surjective hp c hc)
  exact (Nat.card_congr he.toEquiv).trans (by simp)

theorem fibre_in_coset {A : Type*} [Fintype A] {d p : ℕ}
    (X : A → Option (Fin d) → ℤ) (F : Finset A)
    (c : Option (Fin d) → ZMod p) (t : ZMod p) (hne : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (X r i : ZMod p) = t) :
    ∃ y : Option (Fin d) → ℤ, ∀ r ∈ F, X r - y ∈ congruenceKernel p c := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨X a, fun r hr => ?_⟩
  change (∑ i, c i * ((X r - X a) i : ZMod p)) = 0
  simp only [Pi.sub_apply, Int.cast_sub, mul_sub, sum_sub_distrib,
    hf r hr, hf a ha, sub_self]

theorem rank_one_wrap_lt (P : VITParameters) :
    wrapFactor P.toVITData 1 * P.toVITData.C 1 / (P.p : ℝ) < P.toVITData.mu := by
  simpa [wrapFactor, VITData.C] using P.wrap1

theorem density_le_wrap_of_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : VITParameters) (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 1)
    (F : Finset (Grid (extend G Gx))) (N : ℝ)
    (hreg : Regular P.toVITData G L)
    (hcount : N * (P.p : ℝ) ≤ P.D * (P.g : ℝ) * L.H * (Gx : ℝ))
    (hdensity : density F * (Gx : ℝ) ≤ N * L.mZ G)
    (hGx : 0 < Gx) :
    density F ≤ P.D * P.C1 / (P.p : ℝ) := by
  have hg : (0 : ℝ) < P.g := by
    exact_mod_cast lt_of_lt_of_le (Nat.two_pow_pos P.L0) P.g_lower
  have hp : (0 : ℝ) < P.p := by exact_mod_cast P.p_prime.pos
  have hx : (0 : ℝ) < Gx := by exact_mod_cast hGx
  have hm : 0 ≤ L.mZ G := by
    unfold IntLat.mZ mass Algebra.FiniteProbability.atomMass
    exact le_ciSup_of_le ⟨1, by
      rintro _ ⟨t, rfl⟩
      exact Algebra.FiniteProbability.pointProb_le_one _ t⟩ (0 : Fin 1 → ℤ)
      (Algebra.FiniteProbability.pointProb_nonneg _ _)
  have hr : L.mZ G * (L.H : ℝ) ≤ P.C1 / (P.g : ℝ) := by
    simpa [Regular, VITData.C] using hreg
  have hr' := (le_div_iff₀ hg).mp hr
  have h1 := mul_le_mul_of_nonneg_right hdensity hp.le
  have h2 := mul_le_mul_of_nonneg_right hcount hm
  have h3 := mul_le_mul_of_nonneg_left hr' (mul_nonneg P.D_pos.le hx.le)
  apply (le_div_iff₀ hp).mpr
  nlinarith

section ImageCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oldSample (G : ι → ℕ) (Gx : ℕ) (r : Grid (extend G Gx)) : Grid G :=
  fun i => r (some i)

@[simp] theorem stepImage_none {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) :
    stepImage G Gx B r none = ((r none : ℕ) : ℤ) := by
  simp [stepImage, stepMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem stepImage_some {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) (j : Fin d) :
    stepImage G Gx B r (some j) = imageZ G B (oldSample G Gx r) j := by
  simp [stepImage, stepMatrix, Matrix.mulVec, dotProduct, imageZ, oldSample]

theorem oldSample_injective_on_atom {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (y : Option (Fin d) → ℤ) :
    Set.InjOn (oldSample G Gx) {r | stepImage G Gx B r = y} := by
  intro r hr s hs he
  funext i
  cases i with
  | none =>
    apply Fin.ext
    have h := congrFun (hr.trans hs.symm) none
    simpa only [stepImage_none, Int.natCast_inj] using h
  | some i => exact congrFun he i

theorem step_atom_card_le {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (F : Finset (Grid (extend G Gx)))
    (y : Option (Fin d) → ℤ) :
    (F.filter (fun r => stepImage G Gx B r = y)).card ≤
      Algebra.FiniteProbability.fibreCount (imageZ G B) (fun j => y (some j)) := by
  classical
  let S : Finset (Grid G) := univ.filter
    (fun r => imageZ G B r = fun j => y (some j))
  have hS : Algebra.FiniteProbability.fibreCount (imageZ G B) (fun j => y (some j)) = S.card := by
    unfold Algebra.FiniteProbability.fibreCount S
    congr 1
    ext r
    simp only [mem_filter, mem_univ, true_and]
  rw [hS]
  apply Finset.card_le_card_of_injOn (oldSample G Gx)
  · intro r hr
    have hy := (Finset.mem_filter.mp hr).2
    change oldSample G Gx r ∈ S
    dsimp only [S]
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    funext j
    simpa only [stepImage_some] using congrFun hy (some j)
  · intro r hr s hs he
    exact oldSample_injective_on_atom G Gx B y
      (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2 he

theorem density_mul_width_le_image_card {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (F : Finset (Grid (extend G Gx)))
    (hG : ∀ i, 0 < G i) (hx : 0 < Gx) :
    density F * (Gx : ℝ) ≤
      ((F.image (stepImage G Gx B)).card : ℝ) * mass G (imageZ G B) := by
  classical
  have hcard : Fintype.card (Grid (extend G Gx)) =
      Gx * Fintype.card (Grid G) := by
    change Fintype.card ((i : Option ι) → Fin (extend G Gx i)) =
      Gx * Fintype.card ((i : ι) → Fin (G i))
    rw [Fintype.card_pi, Fintype.card_pi, Fintype.prod_option]
    simp only [extend, Option.elim_none, Option.elim_some, Fintype.card_fin]
  have hpos : (0 : ℝ) < Fintype.card (Grid G) := by
    have : Nonempty (Grid G) := ⟨fun i => ⟨0, hG i⟩⟩
    exact_mod_cast Fintype.card_pos
  have hxp : (0 : ℝ) < Gx := by exact_mod_cast hx
  have hfiber (y : Option (Fin d) → ℤ) :
      ((F.filter (fun r => stepImage G Gx B r = y)).card : ℝ) ≤
        mass G (imageZ G B) * Fintype.card (Grid G) := by
    have hp := Algebra.FiniteProbability.pointProb_le_mass (imageZ G B) (fun j => y (some j))
    have hle : ((F.filter (fun r => stepImage G Gx B r = y)).card : ℝ) ≤
        Algebra.FiniteProbability.fibreCount (imageZ G B) (fun j => y (some j)) := by
      exact_mod_cast step_atom_card_le G Gx B F y
    exact hle.trans ((div_le_iff₀ hpos).mp hp)
  have heq := Finset.card_eq_sum_card_image (stepImage G Gx B) F
  have hsum : (F.card : ℝ) ≤
      ((F.image (stepImage G Gx B)).card : ℝ) *
        (mass G (imageZ G B) * Fintype.card (Grid G)) := by
    rw [heq, Nat.cast_sum]
    exact (Finset.sum_le_sum (fun y _ => hfiber y)).trans_eq (by simp)
  unfold density
  rw [hcard, Nat.cast_mul]
  have he : (F.card : ℝ) / ((Gx : ℝ) * Fintype.card (Grid G)) * (Gx : ℝ) =
      (F.card : ℝ) / Fintype.card (Grid G) := by
    field_simp [hxp.ne', hpos.ne']
  rw [he]
  apply (div_le_iff₀ hpos).mpr
  simpa [mul_assoc] using hsum

theorem rank_one_entry_le_height (L : IntLat ι 1) (i : ι) :
    |(L.matrix i 0 : ℝ)| ≤ (L.H : ℝ) := by
  have h := Finset.le_sup (s := (univ : Finset (Fin 1 → ι)))
    (f := fun r => (L.matrix.submatrix r id).det.natAbs) (mem_univ (fun _ => i))
  have hn : (L.matrix i 0).natAbs ≤ L.H := by
    simpa [IntLat.H, height, Algebra.VectorInverse.largestMinor,
      Matrix.det_fin_one, Matrix.submatrix] using h
  have hnR : ((L.matrix i 0).natAbs : ℝ) ≤ (L.H : ℝ) := by exact_mod_cast hn
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hnR

theorem rank_one_covariance_le (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι 1) (hG : GridBudget P.toVITData (extend G Gx)) :
    Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) 0 0 ≤
      (L.H : ℝ)^2 * (P.g : ℝ)^2 * P.S / 12 := by
  have htotal : (∑ i, (G i : ℝ)^2) ≤ (P.g : ℝ)^2 * P.S := by
    have h := hG.2.1
    simp only [Fintype.sum_option, extend, Option.elim_none, Option.elim_some] at h
    nlinarith [sq_nonneg (Gx : ℝ)]
  have hb (i : ι) : (L.matrix i 0 : ℝ)^2 ≤ (L.H : ℝ)^2 := by
    have ha := abs_le.mp (rank_one_entry_le_height L i)
    nlinarith
  calc
    _ = ∑ i, (G i : ℝ)^2 / 12 * (L.matrix i 0 : ℝ)^2 := by
      unfold Analysis.gridCovariance
      apply sum_congr rfl
      intro i _
      simp only [Matrix.map_apply, Int.coe_castRingHom]
      ring
    _ ≤ ∑ i, (G i : ℝ)^2 / 12 * (L.H : ℝ)^2 := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hb i) (by positivity)
    _ = (L.H : ℝ)^2 / 12 * ∑ i, (G i : ℝ)^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left htotal
        (show 0 ≤ (L.H : ℝ)^2 / 12 by positivity)
      nlinarith

theorem rank_one_radius_bound (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι 1) (hG : GridBudget P.toVITData (extend G Gx)) :
    12 * P.R * Real.sqrt
      (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) 0 0) ≤
      P.D * (P.g : ℝ) * (L.H : ℝ) := by
  let v := Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) 0 0
  have hv : 0 ≤ v := by
    dsimp [v, Analysis.gridCovariance]
    apply sum_nonneg
    intro i _
    nlinarith [sq_nonneg ((G i : ℝ) * (L.matrix i 0 : ℝ))]
  have hvar := rank_one_covariance_le P G Gx L hG
  change v ≤ _ at hvar
  have hmul := mul_le_mul_of_nonneg_left hvar (sq_nonneg (12 * P.R))
  have hgeom := mul_le_mul_of_nonneg_right P.D_geometry
    (show 0 ≤ (P.g : ℝ)^2 * (L.H : ℝ)^2 by positivity)
  have hroot := Real.sq_sqrt hv
  have hright : 0 ≤ P.D * (P.g : ℝ) * (L.H : ℝ) :=
    mul_nonneg (mul_nonneg P.D_pos.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  nlinarith [sq_nonneg (12 * P.R * Real.sqrt v + P.D * (P.g : ℝ) * (L.H : ℝ))]

end ImageCounting

theorem planar_congruence_count (hpCount : Algebra.Point.PlanarCount)
    {p : ℕ} (hp : p.Prime) (c : Fin 2 → ZMod p) (hc : c ≠ 0)
    (S : Finset (Fin 2 → ℤ)) (a : Fin 2 → ℤ)
    (hcoset : ∀ x ∈ S, congruenceHom c (x - a) = 0)
    (hfull : Algebra.Point.spanDim (S.image (Algebra.Trans.ChartBasis.castCoordinates 2)) = 2) :
    (S.card : ℝ) ≤ 6 * Algebra.Point.volHull
      (S.image (Algebra.Trans.ChartBasis.castCoordinates 2)) / (p : ℝ) := by
  classical
  let H := (congruenceHom c).toIntLinearMap.ker
  have hindex : H.toAddSubgroup.index = p := by
    change Nat.card ((Fin 2 → ℤ) ⧸ (congruenceHom c).ker) = p
    have he := QuotientAddGroup.quotientKerEquivOfSurjective
      (congruenceHom c) (congruenceHom_surjective hp c hc)
    exact (Nat.card_congr he.toEquiv).trans (by simp)
  obtain ⟨L, hL, hdet⟩ := Algebra.Trans.ChartIndex.finite_index_lattice H
    (by rw [hindex]; exact hp.ne_zero)
  have hcos : Algebra.Point.InCoset L (Algebra.Trans.ChartBasis.castCoordinates 2 a)
      (S.image (Algebra.Trans.ChartBasis.castCoordinates 2)) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    rw [hL, ← map_sub]
    exact ⟨x - a, hcoset x hx, rfl⟩
  have hcard : (S.image (Algebra.Trans.ChartBasis.castCoordinates 2)).card = S.card :=
    Finset.card_image_of_injective S (Algebra.Trans.ChartIndex.cast_injective 2)
  have h := hpCount L (Algebra.Trans.ChartBasis.castCoordinates 2 a) _ hcos hfull
  rw [hcard, hdet, hindex] at h
  exact h

theorem planar_hull_le_rectangle (S : Finset (Fin 2 → ℤ))
    (lo hi : Fin 2 → ℝ) (horder : ∀ i, lo i ≤ hi i)
    (hbox : ∀ x ∈ S, ∀ i, lo i ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ hi i) :
    Algebra.Point.volHull (S.image (Algebra.Trans.ChartBasis.castCoordinates 2)) ≤
      (hi 0 - lo 0) * (hi 1 - lo 1) := by
  let K : Set (Algebra.Point.E 2) := WithLp.toLp 2 '' Set.Icc lo hi
  have hcompact : IsCompact K :=
    isCompact_Icc.image (PiLp.continuous_toLp (p := (2 : ENNReal)) (fun _ : Fin 2 => ℝ))
  have hconvex : Convex ℝ K :=
    (convex_Icc lo hi).linear_image (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap
  have hsubset : (S.image (Algebra.Trans.ChartBasis.castCoordinates 2) :
      Set (Algebra.Point.E 2)) ⊆ K := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact ⟨fun i => (x i : ℝ), ⟨fun i => (hbox x hx i).1,
      fun i => (hbox x hx i).2⟩, rfl⟩
  have hmono : Algebra.Point.volHull (S.image (Algebra.Trans.ChartBasis.castCoordinates 2)) ≤
      (MeasureTheory.volume K).toReal :=
    MeasureTheory.measureReal_mono (convexHull_min hsubset hconvex) hcompact.measure_ne_top
  have hvol : MeasureTheory.volume K = MeasureTheory.volume (Set.Icc lo hi) := by
    have he : K = WithLp.ofLp ⁻¹' Set.Icc lo hi :=
      (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.image_eq_preimage_symm _
    rw [he]
    exact (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      measurableSet_Icc.nullMeasurableSet
  rw [hvol, Real.volume_Icc_pi_toReal horder] at hmono
  simpa [Fin.prod_univ_two] using hmono

theorem planar_congruence_rectangle (hpCount : Algebra.Point.PlanarCount)
    {p : ℕ} (hp : p.Prime) (c : Fin 2 → ZMod p) (hc : c ≠ 0)
    (S : Finset (Fin 2 → ℤ)) (a : Fin 2 → ℤ)
    (hcoset : ∀ x ∈ S, congruenceHom c (x - a) = 0)
    (hfull : Algebra.Point.spanDim (S.image (Algebra.Trans.ChartBasis.castCoordinates 2)) = 2)
    (lo hi : Fin 2 → ℝ) (horder : ∀ i, lo i ≤ hi i)
    (hbox : ∀ x ∈ S, ∀ i, lo i ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ hi i) :
    (S.card : ℝ) * (p : ℝ) ≤ 6 * (hi 0 - lo 0) * (hi 1 - lo 1) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h := (le_div_iff₀ hpR).mp
    (planar_congruence_count hpCount hp c hc S a hcoset hfull)
  have harea := planar_hull_le_rectangle S lo hi horder hbox
  nlinarith

theorem mahalanobis_fin_one (S : Matrix (Fin 1) (Fin 1) ℝ) (m x : Fin 1 → ℝ) :
    Analysis.mahalanobisSq S m x = (x 0 - m 0)^2 / S 0 0 := by
  simp [Analysis.mahalanobisSq, Matrix.inv_subsingleton, Matrix.mulVec,
    dotProduct, Ring.inverse_eq_inv, div_eq_mul_inv, pow_two, mul_comm, mul_assoc]

theorem mahalanobis_fin_one_interval (S : Matrix (Fin 1) (Fin 1) ℝ)
    (hS : 0 < S 0 0) (R : ℝ) (hR : 0 ≤ R) (m x : Fin 1 → ℝ)
    (htrim : Analysis.mahalanobisSq S m x ≤ R^2) :
    |x 0 - m 0| ≤ R * Real.sqrt (S 0 0) := by
  rw [mahalanobis_fin_one] at htrim
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hR (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hS.le]
  exact (div_le_iff₀ hS).mp htrim

def planeZ : (Option (Fin 1) → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x none, x (some 0)]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' a x := by ext i; fin_cases i <;> rfl

def planeReal : (Option (Fin 1) → ℝ) →ₗ[ℝ] Algebra.Point.E 2 where
  toFun x := WithLp.toLp 2 ![x none, x (some 0)]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' a x := by ext i; fin_cases i <;> rfl

theorem planeReal_injective : Function.Injective planeReal := by
  intro x y h
  ext i
  cases i with
  | none => exact congrArg (fun z : Algebra.Point.E 2 => z 0) h
  | some j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact congrArg (fun z : Algebra.Point.E 2 => z 1) h

theorem planeZ_injective : Function.Injective planeZ := by
  intro x y h
  ext i
  cases i with
  | none => exact congrFun h 0
  | some j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact congrFun h 1

theorem fullImage_plane_span {A : Type*} [Fintype A] [DecidableEq A]
    (X : A → Option (Fin 1) → ℤ) (F : Finset A)
    (hrank : Analysis.rationalRank (imageDifferences X F) = 2) :
    Algebra.Point.spanDim ((F.image (fun r => planeZ (X r))).image
      (Algebra.Trans.ChartBasis.castCoordinates 2)) = 2 := by
  classical
  let D := imageDifferences X F
  have hex : ∃ (I : Fin 2 → Option (Fin 1)) (J : Fin 2 → F × F),
      ((D.map (Int.castRingHom ℚ)).submatrix I J).det ≠ 0 := by
    have h := Analysis.exists_rank_minor (D.map (Int.castRingHom ℚ))
    change (D.map (Int.castRingHom ℚ)).rank = 2 at hrank
    rwa [hrank] at h
  obtain ⟨I, J, hminor⟩ := hex
  have hInt : (D.submatrix I J).det ≠ 0 := by
    have he : ((D.map (Int.castRingHom ℚ)).submatrix I J).det =
        ((D.submatrix I J).det : ℚ) :=
      ((Int.castRingHom ℚ).map_det (D.submatrix I J)).symm
    rw [he] at hminor
    exact_mod_cast hminor
  let select : (Option (Fin 1) → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
    { toFun := fun x i => x (I i)
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hli : LinearIndependent ℤ (fun j => D.col (J j)) :=
    LinearIndependent.of_comp select (Matrix.linearIndependent_cols_of_det_ne_zero hInt)
  have hliR : LinearIndependent ℝ (fun j i => (D i (J j) : ℝ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)).mpr hli
  have hliP := hliR.map' planeReal (LinearMap.ker_eq_bot.mpr planeReal_injective)
  let S := (F.image (fun r => planeZ (X r))).image
    (Algebra.Trans.ChartBasis.castCoordinates 2)
  let V := vectorSpan ℝ (S : Set (Algebra.Point.E 2))
  have hpoint (r : A) (hr : r ∈ F) :
      planeReal (fun i => (X r i : ℝ)) ∈ (S : Set (Algebra.Point.E 2)) := by
    have he : planeReal (fun i => (X r i : ℝ)) =
        Algebra.Trans.ChartBasis.castCoordinates 2 (planeZ (X r)) := by
      ext i; fin_cases i <;> rfl
    rw [he]
    exact mem_image_of_mem _ (mem_image_of_mem _ hr)
  have hmem (j : Fin 2) : planeReal (fun i => (D i (J j) : ℝ)) ∈ V := by
    have h := vsub_mem_vectorSpan ℝ (hpoint (J j).1.val (J j).1.property)
      (hpoint (J j).2.val (J j).2.property)
    convert h using 1
    ext i
    fin_cases i <;> simp [planeReal, D, imageDifferences]
  have hle : Submodule.span ℝ
      (Set.range (fun j => planeReal (fun i => (D i (J j) : ℝ)))) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hmem j
  have hlow : 2 ≤ Module.finrank ℝ V := by
    have hd : Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun j => planeReal (fun i => (D i (J j) : ℝ))))) = 2 :=
      finrank_span_eq_card hliP
    exact hd.symm.le.trans (Submodule.finrank_mono hle)
  have hhigh : Module.finrank ℝ V ≤ 2 := by
    simpa using Submodule.finrank_le V
  exact Nat.le_antisymm hhigh hlow

theorem rank_one_covariance_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ℕ) (hG : ∀ i, 0 < G i) (L : IntLat ι 1) :
    0 < Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) 0 0 := by
  have hli : LinearIndependent ℤ L.matrix.col :=
    L.basis.linearIndependent.map' L.carrier.subtype (Submodule.ker_subtype L.carrier)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hli.ne_zero (0 : Fin 1))
  have hiR : (L.matrix i 0 : ℝ) ≠ 0 := by exact_mod_cast hi
  have hGi : (0 : ℝ) < G i := by exact_mod_cast hG i
  have he : Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) 0 0 =
      ∑ j, (G j : ℝ)^2 / 12 * (L.matrix j 0 : ℝ)^2 := by
    unfold Analysis.gridCovariance
    apply sum_congr rfl
    intro j _
    simp only [Matrix.map_apply, Int.coe_castRingHom]
    ring
  rw [he]
  exact sum_pos' (fun j _ => by positivity) ⟨i, mem_univ _, by positivity⟩

theorem rank_one_image_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpCount : Algebra.Point.PlanarCount) (P : VITParameters)
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 1)
    (c : Option (Fin 1) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx)))
    (hG : GridBudget P.toVITData (extend G Gx)) (hc : c ≠ 0) (hne : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t)
    (htrim : Trimmed P.toVITData G Gx L.matrix F)
    (hrank : Analysis.rationalRank (imageDifferences (stepImage G Gx L.matrix) F) = 2) :
    ((F.image (stepImage G Gx L.matrix)).card : ℝ) * (P.p : ℝ) ≤
      P.D * (P.g : ℝ) * (L.H : ℝ) * (Gx : ℝ) := by
  classical
  let X := stepImage G Gx L.matrix
  let S := F.image (fun r => planeZ (X r))
  let v := Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) 0 0
  let b := P.R * Real.sqrt v
  let m := imageCenter G L.matrix 0
  let lo : Fin 2 → ℝ := ![0, m - b]
  let hi : Fin 2 → ℝ := ![(Gx : ℝ), m + b]
  let c2 : Fin 2 → ZMod P.p := ![c none, c (some 0)]
  have hgNat : 0 < P.g := lt_of_lt_of_le (Nat.two_pow_pos P.L0) P.g_lower
  have hgOld : ∀ i, 0 < G i := fun i => hgNat.trans_le (hG.1 (some i))
  have hv : 0 < v := rank_one_covariance_pos G hgOld L
  have hR : 0 ≤ P.R := P.R_pos.le
  have hb : 0 ≤ b := mul_nonneg hR (Real.sqrt_nonneg _)
  have hc2 : c2 ≠ 0 := by
    intro hz
    apply hc
    ext i
    cases i with
    | none => exact congrFun hz 0
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact congrFun hz 1
  obtain ⟨a, ha⟩ := hne
  have hcoset (z : Fin 2 → ℤ) (hz : z ∈ S) :
      congruenceHom c2 (z - planeZ (X a)) = 0 := by
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hz
    have hfr := hf r hr
    have hfa := hf a ha
    have he := sub_eq_zero.mpr (hfr.trans hfa.symm)
    convert he using 1
    simp [congruenceHom, c2, planeZ, Fin.sum_univ_two,
      Fintype.sum_option, Int.cast_sub, mul_sub, X]
    ring
  have hfull : Algebra.Point.spanDim (S.image
      (Algebra.Trans.ChartBasis.castCoordinates 2)) = 2 := fullImage_plane_span X F hrank
  have horder (i : Fin 2) : lo i ≤ hi i := by
    fin_cases i
    · change (0 : ℝ) ≤ (Gx : ℝ)
      exact Nat.cast_nonneg _
    · change m - b ≤ m + b
      linarith
  have hbox (z : Fin 2 → ℤ) (hz : z ∈ S) (i : Fin 2) :
      lo i ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ hi i := by
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hz
    fin_cases i
    · have hxr : ((r none : ℕ) : ℝ) ≤ (Gx : ℝ) := by
        exact_mod_cast (r none).isLt.le
      simpa [lo, hi, planeZ, X] using
        (show (0 : ℝ) ≤ ((r none : ℕ) : ℝ) ∧ ((r none : ℕ) : ℝ) ≤ Gx from
          ⟨Nat.cast_nonneg _, hxr⟩)
    · have ht := mahalanobis_fin_one_interval _ hv _ hR _ _ (htrim r hr)
      have ht' : |(X r (some 0) : ℝ) - m| ≤ b := ht
      have hh := abs_le.mp ht'
      change m - b ≤ (X r (some 0) : ℝ) ∧ (X r (some 0) : ℝ) ≤ m + b
      constructor <;> linarith
  have hcount := planar_congruence_rectangle hpCount P.p_prime c2 hc2 S
    (planeZ (X a)) hcoset hfull lo hi horder hbox
  have hcard : S.card = (F.image X).card := by
    change (F.image (planeZ ∘ X)).card = _
    rw [← Finset.image_image]
    exact Finset.card_image_of_injective _ planeZ_injective
  rw [hcard] at hcount
  have hradius := mul_le_mul_of_nonneg_right (rank_one_radius_bound P G Gx L hG)
    (Nat.cast_nonneg Gx : (0 : ℝ) ≤ Gx)
  simp only [lo, hi, Matrix.cons_val_zero, Matrix.cons_val_one] at hcount
  change 12 * P.R * Real.sqrt v * (Gx : ℝ) ≤ _ at hradius
  dsimp only [b] at hcount
  nlinarith

theorem fullImageExclusion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hplanar : Algebra.Point.PlanarCount)
    (_hcb : ∀ n r (B : Matrix (Fin n) (Fin r) ℝ) sigma,
      Algebra.Trans.CauchyBinet3 B sigma)
    (_hesym : ∀ n (w : Fin n → ℝ) total, Algebra.Trans.ESymBounds w total)
    (_htrim : Algebra.Trim.TrimForIntLat)
    (P : VITParameters) (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 1)
    (c : Option (Fin 1) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) : FullImageExclusion 1 P G Gx L c t F := by
  intro _ _ hG hreg hc hne hf htrim hrank
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.two_pow_pos P.L0) P.g_lower
  have hcount := rank_one_image_count hplanar P G Gx L c t F hG hc hne hf htrim hrank
  have hdensity := density_mul_width_le_image_card G Gx L.matrix F
    (fun i => hg.trans_le (hG.1 (some i))) (hg.trans_le (hG.1 none))
  have hd := density_le_wrap_of_count P G Gx L F _ hreg hcount hdensity
    (hg.trans_le (hG.1 none))
  exact ⟨congruenceKernel_card P.p_prime c hc,
    fibre_in_coset _ F c t hne hf, by simpa [wrapFactor, VITData.C] using hd,
    rank_one_wrap_lt P⟩

end Algebra.Mod.Wrap1

end Praxis.Lift
