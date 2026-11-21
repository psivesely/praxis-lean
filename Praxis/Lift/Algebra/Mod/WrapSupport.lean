import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Algebra.Trans.GramBridge
import Mathlib.GroupTheory.QuotientGroup.Basic
import Praxis.Lift.Record
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.GridTrim

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

open Finset Praxis.Algebra.Inverse.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.Wrap3

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Lift.Algebra.Mod.Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def congruenceMap {d p : ℕ} (c : Option (Fin d) → ZMod p) :
    (Option (Fin d) → ℤ) →+ ZMod p where
  toFun x := ∑ i, c i * (x i : ZMod p)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

theorem congruenceMap_ker {d p : ℕ} (c : Option (Fin d) → ZMod p) :
    (congruenceMap c).ker = congruenceKernel p c := by
  ext x
  rfl

theorem congruenceMap_surjective {d p : ℕ} [Fact p.Prime]
    (c : Option (Fin d) → ZMod p) (hc : c ≠ 0) :
    Function.Surjective (congruenceMap c) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    exact hc (funext fun i => by simpa using not_exists.mp h i)
  intro t
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (t / c i)
  refine ⟨Pi.single i a, ?_⟩
  change (∑ j, c j * (((Pi.single i a : Option (Fin d) → ℤ) j : ℤ) : ZMod p)) = t
  simp only [Pi.single_apply, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [ha]
  exact mul_div_cancel₀ t hi

theorem congruenceKernel_card {d p : ℕ} [Fact p.Prime]
    (c : Option (Fin d) → ZMod p) (hc : c ≠ 0) :
    Nat.card ((Option (Fin d) → ℤ) ⧸ congruenceKernel p c) = p := by
  rw [← congruenceMap_ker]
  let e := QuotientAddGroup.quotientKerEquivOfSurjective
    (congruenceMap c) (congruenceMap_surjective c hc)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

theorem fibre_in_coset {A : Type*} [Fintype A] [DecidableEq A] {d p : ℕ}
    (X : A → Option (Fin d) → ℤ) (c : Option (Fin d) → ZMod p)
    (t : ZMod p) (F : Finset A) (hne : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (X r i : ZMod p) = t) :
    ∃ y : Option (Fin d) → ℤ, ∀ r ∈ F, X r - y ∈ congruenceKernel p c := by
  obtain ⟨r₀, hr₀⟩ := hne
  refine ⟨X r₀, ?_⟩
  intro r hr
  change (∑ i, c i * ((X r - X r₀) i : ZMod p)) = 0
  simpa only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib,
    hf r hr, hf r₀ hr₀, sub_self]

theorem index_and_coset {d : ℕ} (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι d) (c : Option (Fin d) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) (hc : c ≠ 0) (hne : F.Nonempty)
    (hf : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t) :
    Nat.card ((Option (Fin d) → ℤ) ⧸ congruenceKernel P.p c) = P.p ∧
    (∃ y : Option (Fin d) → ℤ, ∀ r ∈ F,
      stepImage G Gx L.matrix r - y ∈ congruenceKernel P.p c) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  exact ⟨congruenceKernel_card c hc,
    fibre_in_coset (stepImage G Gx L.matrix) c t F hne hf⟩

theorem wrap3_lt (P : VITParameters) :
    wrapFactor P.toVITData 3 * P.toVITData.C 3 / (P.p : ℝ) < P.toVITData.mu := by
  simpa [wrapFactor, VITData.C] using P.wrap3

theorem rowMinor_sq_le [LinearOrder ι] (B : Matrix ι (Fin 3) ℤ) (I : Finset ι) :
    Algebra.Trans.rowMinor (B.map (Int.castRingHom ℝ)) I ^ 2 ≤ (height B : ℝ)^2 := by
  classical
  unfold Algebra.Trans.rowMinor
  split_ifs with hI
  · let f : Fin 3 → ι := I.orderEmbOfFin hI
    have hb : (B.submatrix f id).det.natAbs ≤ height B :=
      Finset.le_sup (f := fun f : Fin 3 → ι => (B.submatrix f id).det.natAbs)
        (Finset.mem_univ f)
    have ha : |((B.map (Int.castRingHom ℝ)).submatrix f id).det| ≤ (height B : ℝ) := by
      have hcast : ((B.map (Int.castRingHom ℝ)).submatrix f id).det =
          ((B.submatrix f id).det : ℝ) := (Int.cast_det _).symm
      rw [hcast, ← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast hb
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr ha
  · simpa using sq_nonneg (height B : ℝ)

theorem determinant_le [LinearOrder ι] (B : Matrix ι (Fin 3) ℤ) (sigma : ι → ℝ)
    (hcb : Algebra.Trans.CauchyBinet3 (B.map (Int.castRingHom ℝ)) sigma)
    (he : Algebra.Trans.ESymBounds (fun i => sigma i ^ 2) (∑ i, sigma i ^ 2)) :
    (Algebra.Trans.weightedGram (B.map (Int.castRingHom ℝ)) sigma).det ≤
      (height B : ℝ)^2 * (∑ i, sigma i ^ 2)^3 / 6 := by
  rw [hcb (by decide)]
  calc
    _ ≤ ∑ I ∈ Finset.univ.powersetCard 3,
        (height B : ℝ)^2 * ∏ i ∈ I, sigma i ^ 2 := by
      apply Finset.sum_le_sum
      intro I _
      exact mul_le_mul_of_nonneg_right (rowMinor_sq_le B I)
        (Finset.prod_nonneg (fun i _ => sq_nonneg _))
    _ = (height B : ℝ)^2 * Algebra.Trans.elementarySymmetric (fun i => sigma i ^ 2) 3 := by
      rw [Algebra.Trans.elementarySymmetric, Finset.esymm_map_val, Finset.mul_sum]
    _ ≤ (height B : ℝ)^2 * ((∑ i, sigma i ^ 2)^3 / 6) :=
      mul_le_mul_of_nonneg_left (he (fun i => sq_nonneg _) rfl).2 (sq_nonneg _)
    _ = _ := by ring

theorem covariance_determinant_le [LinearOrder ι] (G : ι → ℕ) (B : Matrix ι (Fin 3) ℤ)
    (hcb : Algebra.Trans.CauchyBinet3 (B.map (Int.castRingHom ℝ))
      (fun i => (G i : ℝ) / Real.sqrt 12))
    (he : Algebra.Trans.ESymBounds (fun i => ((G i : ℝ) / Real.sqrt 12)^2)
      (∑ i, ((G i : ℝ) / Real.sqrt 12)^2)) :
    (Analysis.gridCovariance G (B.map (Int.castRingHom ℝ))).det ≤
      (height B : ℝ)^2 * (∑ i, (G i : ℝ)^2)^3 / (12^3 * 6) := by
  have h := determinant_le B (fun i => (G i : ℝ) / Real.sqrt 12) hcb he
  rw [Algebra.Trans.weightedGram_gridSigma] at h
  simp_rw [Algebra.Trans.gridSigma_sq] at h
  rw [← Finset.sum_div] at h
  convert h using 1 <;> ring

theorem stepImage_none {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) :
    stepImage G Gx B r none = ((r none : ℕ) : ℤ) := by
  simp [stepImage, stepMatrix, Matrix.mulVec, dotProduct, Fintype.sum_option]

theorem stepImage_some {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) (j : Fin d) :
    stepImage G Gx B r (some j) = imageZ G B (fun i => r (some i)) j := by
  simp [stepImage, stepMatrix, imageZ, Matrix.mulVec, dotProduct, Fintype.sum_option]

theorem step_grid_card (G : ι → ℕ) (Gx : ℕ) :
    Fintype.card (Grid (extend G Gx)) = Fintype.card (Grid G) * Gx := by
  rw [Fintype.card_congr (Equiv.piOptionEquivProd (β := fun i => Fin (extend G Gx i)))]
  change Fintype.card (Fin Gx × Grid G) = _
  simp [mul_comm]

theorem constant_image_density_le {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι d) (F : Finset (Grid (extend G Gx)))
    (hconstant : ∀ r ∈ F, ∀ s ∈ F,
      stepImage G Gx L.matrix r = stepImage G Gx L.matrix s) :
    density F ≤ L.mZ G / (Gx : ℝ) := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hne
    let old : Grid (extend G Gx) → Grid G := fun r i => r (some i)
    have hi : (F : Set (Grid (extend G Gx))).InjOn old := by
      intro r hr s hs hold
      have he := congrFun (hconstant r hr s hs) none
      rw [stepImage_none, stepImage_none] at he
      have hn : r none = s none := Fin.ext (by exact_mod_cast he)
      funext i
      cases i with
      | none => exact hn
      | some i => exact congrFun hold i
    have hf : F.card ≤ Algebra.FiniteProbability.fibreCount (imageZ G L.matrix)
        (imageZ G L.matrix (old r₀)) := by
      unfold Algebra.FiniteProbability.fibreCount
      apply Finset.card_le_card_of_injOn old
      · intro r hr
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        funext j
        have he := congrFun (hconstant r hr r₀ hr₀) (some j)
        simpa only [stepImage_some] using he
      · exact hi
    have hb := Algebra.FiniteProbability.pointProb_le_mass (imageZ G L.matrix)
      (imageZ G L.matrix (old r₀))
    calc
      density F ≤ Algebra.FiniteProbability.pointProb (imageZ G L.matrix)
          (imageZ G L.matrix (old r₀)) / (Gx : ℝ) := by
        unfold density Algebra.FiniteProbability.pointProb
        rw [step_grid_card, Nat.cast_mul, div_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hf) (by positivity)
      _ ≤ L.mZ G / (Gx : ℝ) :=
        div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    have hm : 0 ≤ L.mZ G := by
      exact (Algebra.FiniteProbability.pointProb_nonneg (imageZ G L.matrix) 0).trans
        (Algebra.FiniteProbability.pointProb_le_mass (imageZ G L.matrix) 0)
    simpa [density] using div_nonneg hm (Nat.cast_nonneg Gx)

theorem density_le_image_card {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι d) (F : Finset (Grid (extend G Gx))) :
    density F ≤ ((F.image (stepImage G Gx L.matrix)).card : ℝ) * L.mZ G / (Gx : ℝ) := by
  classical
  let X := stepImage G Gx L.matrix
  have hcard := Finset.card_eq_sum_card_image X F
  have he : density F = ∑ y ∈ F.image X, density (F.filter (fun r => X r = y)) := by
    unfold density
    rw [hcard, Nat.cast_sum, Finset.sum_div]
  rw [he]
  calc
    _ ≤ ∑ _y ∈ F.image X, L.mZ G / (Gx : ℝ) := by
      apply Finset.sum_le_sum
      intro y _
      apply constant_image_density_le
      intro r hr s hs
      exact (Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hs).2.symm
    _ = _ := by simp; ring

theorem volume_factor_le (P : VITParameters) (H v : ℝ) (hH : 0 ≤ H)
    (hv : 0 ≤ v)
    (hb : v ≤ H^2 * ((P.g : ℝ)^2 * P.S)^3 / (12^3 * 6)) :
    15552 * (4 * Real.pi / 3) * P.R^3 * Real.sqrt v ≤
      P.F * (P.g : ℝ)^3 * H := by
  have hg : (0 : ℝ) ≤ P.g := Nat.cast_nonneg _
  have hR : 0 ≤ P.R := P.R_pos.le
  let a : ℝ := 15552 * (4 * Real.pi / 3) * P.R^3
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h1 := mul_le_mul_of_nonneg_left hb (sq_nonneg a)
  have h2 := mul_le_mul_of_nonneg_right P.F_geometry
    (sq_nonneg ((P.g : ℝ)^3 * H))
  have heq : a^2 * (H^2 * ((P.g : ℝ)^2 * P.S)^3 / (12^3 * 6)) =
      (15552^2 * (4 * Real.pi / 3)^2 * P.R^6 * P.S^3 / (12^3 * 6)) *
        ((P.g : ℝ)^3 * H)^2 := by dsimp [a]; ring
  rw [heq] at h1
  have hs : (a * Real.sqrt v)^2 ≤ (P.F * (P.g : ℝ)^3 * H)^2 := by
    rw [mul_pow, Real.sq_sqrt hv]
    nlinarith only [h1, h2]
  exact (sq_le_sq₀ (mul_nonneg ha (Real.sqrt_nonneg v))
    (mul_nonneg (mul_nonneg P.F_pos.le (pow_nonneg hg _)) hH)).mp hs

theorem density_bound_of_image_count (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι 3) (F : Finset (Grid (extend G Gx)))
    (hGx : 0 < Gx) (hreg : Regular P.toVITData G L)
    (v : ℝ) (hv : 0 ≤ v)
    (hdet : v ≤ (L.H : ℝ)^2 * ((P.g : ℝ)^2 * P.S)^3 / (12^3 * 6))
    (hcount : ((F.image (stepImage G Gx L.matrix)).card : ℝ) ≤
      15552 * (4 * Real.pi / 3) * P.R^3 * (Gx : ℝ) * Real.sqrt v / (P.p : ℝ)) :
    density F ≤ P.F * P.C3 / (P.p : ℝ) := by
  have hp : (0 : ℝ) < P.p := by exact_mod_cast P.p_prime.pos
  have hgN : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hg : (0 : ℝ) < P.g := by exact_mod_cast hgN
  have hx : (0 : ℝ) < Gx := by exact_mod_cast hGx
  have hm : 0 ≤ L.mZ G :=
    (Algebra.FiniteProbability.pointProb_nonneg (imageZ G L.matrix) 0).trans
      (Algebra.FiniteProbability.pointProb_le_mass (imageZ G L.matrix) 0)
  have hvol := volume_factor_le P (L.H : ℝ) v (Nat.cast_nonneg _) hv hdet
  have hregular : L.mZ G * (L.H : ℝ) * (P.g : ℝ)^3 ≤ P.C3 := by
    have h := (le_div_iff₀ (pow_pos hg 3)).mp hreg
    simpa [VITData.C] using h
  calc
    density F ≤ ((F.image (stepImage G Gx L.matrix)).card : ℝ) * L.mZ G / (Gx : ℝ) :=
      density_le_image_card G Gx L F
    _ ≤ (15552 * (4 * Real.pi / 3) * P.R^3 * (Gx : ℝ) * Real.sqrt v /
        (P.p : ℝ)) * L.mZ G / (Gx : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hm) hx.le
    _ = (15552 * (4 * Real.pi / 3) * P.R^3 * Real.sqrt v) * L.mZ G / (P.p : ℝ) := by
      field_simp
      <;> ring
    _ ≤ (P.F * (P.g : ℝ)^3 * (L.H : ℝ)) * L.mZ G / (P.p : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hvol hm) hp.le
    _ ≤ P.F * P.C3 / (P.p : ℝ) := by
      apply div_le_div_of_nonneg_right _ hp.le
      nlinarith only [mul_le_mul_of_nonneg_left hregular P.F_pos.le]

end Algebra.Mod.Wrap3

end Praxis.Lift
