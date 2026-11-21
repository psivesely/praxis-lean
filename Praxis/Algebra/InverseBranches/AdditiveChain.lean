import Praxis.Algebra.InverseBranches.IntegerLift
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Combinatorics.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Praxis.Algebra.InverseBranches.LatticeChain

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.VectorInverse

open Finset Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

open scoped BigOperators Matrix

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [DecidableEq A]

structure AdditiveState (G : ι → ℕ) (y : ι → A) (g M : ℕ) (D : ℝ)
    (S : Finset ι) (H : AddSubgroup A) (T k : ℕ) (ρ : ℝ) : Prop where
  contains : ∀ i ∈ S, y i ∈ H
  indexpos : 0 < H.index
  tpos : 0 < T
  product : H.index * T = M
  bd : FibBd G y S ρ
  merged : ρ ≤ D * correction g ^ k * (1 / (T : ℝ) + 1 / (g : ℝ))
  coarse : ρ ≤ D * (correction g / 2) ^ k

theorem AdditiveState.step {G : ι → ℕ} {y : ι → A} {g M : ℕ} {D : ℝ}
    {S : Finset ι} {H : AddSubgroup A} {T k : ℕ} {ρ : ℝ}
    (st : AdditiveState G y g M D S H T k ρ)
    (hg : 0 < g) (hG : ∀ j, g ≤ G j) (hD : 0 ≤ D)
    {j : ι} (hj : y j ∉ H) :
    ∃ (H' : AddSubgroup A) (v : ℕ),
      AdditiveState G y g M D (insert j S) H' (T * v) (k + 1)
        (ρ * ((((G j + v - 1) / v : ℕ) : ℝ) / G j)) := by
  let H' := H ⊔ AddSubgroup.zmultiples (y j)
  let v := H.relIndex H'
  have hprod : v * H'.index = H.index := AddSubgroup.relIndex_mul_index le_sup_left
  have hv0 : 0 < v := by have := st.indexpos; nlinarith
  have hv1 : v ≠ 1 := by
    intro h
    have hh : H' ≤ H := AddSubgroup.relIndex_eq_one.mp h
    exact hj (hh ((show AddSubgroup.zmultiples (y j) ≤ H' from le_sup_right)
      (AddSubgroup.mem_zmultiples (y j))))
  have hv2 : 2 ≤ v := by omega
  have hH' : 0 < H'.index := by have := st.indexpos; nlinarith
  have hjS : j ∉ S := fun h => hj (st.contains j h)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
  have hvR2 : (2 : ℝ) ≤ v := by exact_mod_cast hv2
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast st.tpos
  have hc0 : 0 ≤ correction g := by unfold correction; positivity
  have hq := ceil_factor_le hg (hG j) hv0
  have hm := merging_reciprocal hg0 hTR hvR
  have hhalf : 1 / (v : ℝ) + 1 / (g : ℝ) ≤ correction g / 2 := by
    have hh : 1 / (v : ℝ) ≤ 1 / (2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hvR2
    calc
      _ ≤ 1 / (2 : ℝ) + 1 / (g : ℝ) := add_le_add hh le_rfl
      _ = _ := by unfold correction; ring
  have hq0 : 0 ≤ ((((G j + v - 1) / v : ℕ) : ℝ) / G j) := by positivity
  refine ⟨H', v, ?_⟩
  exact {
    contains := by
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact (show AddSubgroup.zmultiples (y i) ≤ H' from le_sup_right)
          (AddSubgroup.mem_zmultiples _)
      · exact (show H ≤ H' from le_sup_left) (st.contains i hi)
    indexpos := hH'
    tpos := Nat.mul_pos st.tpos hv0
    product := by rw [← st.product]; dsimp [v] at hprod; nlinarith [hprod]
    bd := quotient_residue_step st.bd H st.contains hjS (lt_of_lt_of_le hg (hG j)) hv0
    merged := by
      calc
        ρ * _ ≤ (D * correction g ^ k * (1 / (T : ℝ) + 1 / (g : ℝ))) *
            (1 / (v : ℝ) + 1 / (g : ℝ)) :=
          mul_le_mul st.merged hq hq0 (by positivity)
        _ ≤ (D * correction g ^ k) *
            ((1 + 2 / (g : ℝ)) * (1 / ((T : ℝ) * v) + 1 / (g : ℝ))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hm (by positivity)
        _ = _ := by rw [pow_succ]; push_cast; unfold correction; ring
    coarse := by
      calc
        ρ * _ ≤ (D * (correction g / 2) ^ k) * (correction g / 2) :=
          mul_le_mul st.coarse (hq.trans hhalf) hq0 (by positivity)
        _ = _ := by rw [pow_succ]; ring }

theorem finish_additive_chain {G : ι → ℕ} {y : ι → A} {g M N : ℕ} {D : ℝ}
    (hg : 0 < g) (hG : ∀ j, g ≤ G j) (hpow : g ≤ 2 ^ N) (hD : 0 ≤ D)
    (hprimitive : AddSubgroup.closure (Set.range y) = ⊤)
    (n : ℕ) {S : Finset ι} {H : AddSubgroup A} {T k : ℕ} {ρ : ℝ}
    (hk : k + n = N) (st : AdditiveState G y g M D S H T k ρ) :
    FibBd G y univ (D * correction g ^ N * (1 / (M : ℝ) + 1 / (g : ℝ))) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hc : 1 ≤ correction g := by unfold correction; linarith [show 0 ≤ 2 / (g : ℝ) by positivity]
  induction n generalizing S H T k ρ with
  | zero =>
    have hkN : k = N := by omega
    have htwo : (g : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hpow
    have hinv : 1 / (2 : ℝ) ^ N ≤ 1 / (g : ℝ) := one_div_le_one_div_of_le hg0 htwo
    apply (st.bd.extend (subset_univ S)).mono
    calc
      ρ ≤ D * (correction g / 2) ^ k := st.coarse
      _ = D * correction g ^ N * (1 / (2 : ℝ) ^ N) := by rw [hkN, div_pow]; ring
      _ ≤ D * correction g ^ N * (1 / (g : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  | succ n ih =>
    by_cases hh : H.index = 1
    · have hT : T = M := by simpa [hh] using st.product
      apply (st.bd.extend (subset_univ S)).mono
      calc
        ρ ≤ D * correction g ^ k * (1 / (T : ℝ) + 1 / (g : ℝ)) := st.merged
        _ ≤ D * correction g ^ N * (1 / (T : ℝ) + 1 / (g : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc (by omega)) hD
        _ = _ := by rw [hT]
    · have hj : ∃ j, y j ∉ H := by
        by_contra! h
        have hle : AddSubgroup.closure (Set.range y) ≤ H :=
          (AddSubgroup.closure_le H).mpr (by rintro _ ⟨j, rfl⟩; exact h j)
        rw [hprimitive] at hle
        exact hh (AddSubgroup.index_eq_one.mpr (top_le_iff.mp hle))
      obtain ⟨j, hj⟩ := hj
      obtain ⟨H', v, hs⟩ := st.step hg hG hD hj
      exact ih (by omega) hs

def PrimitiveRows {d : ℕ} (B : Matrix ι (Fin d) ℤ) : Prop :=
  AddSubgroup.closure (Set.range (fun i => B i)) = ⊤

theorem integer_fibBd_additive {d g N : ℕ} {G : ι → ℕ} {B : Matrix ι (Fin d) ℤ}
    (hg : 0 < g) (hG : ∀ i, g ≤ G i) (hpow : g ≤ 2 ^ N)
    (hprimitive : PrimitiveRows B) (r : Fin d → ι)
    (hdet : (B.submatrix r id).det ≠ 0) :
    FibBd G (fun i => B i) univ ((1 / (g : ℝ)^d) * correction g ^ N *
      (1 / ((B.submatrix r id).det.natAbs : ℝ) + 1 / (g : ℝ))) := by
  let H := PivotGroup B r
  let M := (B.submatrix r id).det.natAbs
  let D : ℝ := 1 / ∏ k : Fin d, (G (r k) : ℝ)
  have hGp : ∀ i, 0 < G i := fun i => lt_of_lt_of_le hg (hG i)
  have hH : H.index = M := pivotGroup_index B r hdet
  have st : AdditiveState G (fun i => B i) g M D (univ.image r) H 1 0 D := {
    contains := pivot_rows_mem B r
    indexpos := by rw [hH]; exact Int.natAbs_pos.mpr hdet
    tpos := one_pos
    product := by rw [hH, mul_one]
    bd := pivot_fibBd G B r hGp hdet
    merged := by
      simp only [pow_zero, mul_one, Nat.cast_one, one_div_one]
      have : 0 ≤ D * (1 / (g : ℝ)) := by dsimp [D]; positivity
      nlinarith
    coarse := by simp }
  have hb := finish_additive_chain hg hG hpow (show 0 ≤ D by dsimp [D]; positivity)
    hprimitive N (by omega) st
  apply hb.mono
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by unfold correction; positivity)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (g : ℝ)^d = ∏ _ : Fin d, (g : ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => hg0.le) (fun i _ => by exact_mod_cast hG (r i))

end Praxis.Algebra.VectorInverse
