import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Praxis.Combinatorics.Mass

open Finset

set_option linter.unusedSectionVars false

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Field K] [DecidableEq K]

abbrev Grid (g : ι → ℕ) := (i : ι) → Fin (g i)

def gval {g : ι → ℕ} (c : ι → K) (k : Grid g) (i : ι) : K := c i + ((k i : ℕ) : K)

def matCount (g : ι → ℕ) (c : ι → K) (A : κ → ι → K) (α : κ → K) : ℕ :=
  #{k : Grid g | ∀ j, ∑ i, A j i * gval c k i = α j}

noncomputable def matProb (g : ι → ℕ) (c : ι → K) (A : κ → ι → K) (α : κ → K) : ℝ :=
  matCount g c A α / ∏ i, (g i : ℝ)

noncomputable def matMass (g : ι → ℕ) (c : ι → K) (A : κ → ι → K) : ℝ := ⨆ α : κ → K, matProb g c A α

def GridInj (K : Type*) [Field K] (g : ι → ℕ) : Prop :=
  ∀ i (a b : Fin (g i)), ((a : ℕ) : K) = ((b : ℕ) : K) → a = b

theorem gridInj_zmod (p : ℕ) [Fact p.Prime] (g : ι → ℕ) (h : ∀ i, g i ≤ p) : GridInj (ZMod p) g := by
  intro i a b hab
  have h1 : (a : ℕ) < p := lt_of_lt_of_le a.isLt (h i)
  have h2 : (b : ℕ) < p := lt_of_lt_of_le b.isLt (h i)
  have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hab
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  exact Fin.ext this

theorem gval_inj {g : ι → ℕ} (hinj : GridInj K g) (c : ι → K) {k k' : Grid g} {i : ι}
    (h : gval c k i = gval c k' i) : k i = k' i :=
  hinj i _ _ (add_left_cancel h)

theorem matCount_mul_prod_le (g : ι → ℕ) (hinj : GridInj K g) (c : ι → K) {A : κ → ι → K} (α : κ → K) (S : Finset ι)
    (hS : ∀ d : ι → K, (∀ i, i ∉ S → d i = 0) → (∀ j, ∑ i, A j i * d i = 0) → ∀ i, d i = 0) :
    matCount g c A α * ∏ i ∈ S, g i ≤ ∏ i, g i := by
  classical
  unfold matCount
  have h1 : ∏ i ∈ S, g i = #(univ : Finset ((i : S) → Fin (g i))) := by
    rw [card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact (prod_coe_sort S g).symm
  have h2 : ∏ i, g i = #(univ : Finset (Grid g)) := by simp [Fintype.card_pi]
  rw [h1, h2, ← card_product]
  refine card_le_card_of_injOn (fun q i => if h : i ∈ S then q.2 ⟨i, h⟩ else q.1 i) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
  rintro ⟨k, s⟩ hq ⟨k', s'⟩ hq' he
  have hk := (mem_product.mp (mem_coe.mp hq)).1
  have hk' := (mem_product.mp (mem_coe.mp hq')).1
  simp only [mem_filter, mem_univ, true_and] at hk hk'
  simp only at he
  have hoff : ∀ i, i ∉ S → k i = k' i := fun i hi => by
    simpa [hi] using congrFun he i
  have hon : ∀ i : S, s i = s' i := fun i => by
    simpa [i.2] using congrFun he i.1
  have hd := hS (fun i => gval c k i - gval c k' i) (fun i hi => by simp only [gval, hoff i hi, sub_self]) (fun j => by
    simp only [mul_sub, sum_sub_distrib, hk j, hk' j, sub_self])
  refine Prod.ext (funext fun i => ?_) (funext hon)
  exact gval_inj hinj c (sub_eq_zero.mp (hd i))

theorem matCount_mul_rank_le (g : ι → ℕ) (hinj : GridInj K g) (gm : ℕ) (hgm : ∀ i, gm ≤ g i) (c : ι → K)
    (A : κ → ι → K) (α : κ → K) : matCount g c A α * gm ^ (Matrix.of A).rank ≤ ∏ i, g i := by
  classical
  let v : ι → (κ → K) := fun i j => A j i
  obtain ⟨s, -, -, hspan, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K v) (Set.empty_subset (Set.univ : Set ι))
  have hsp : Submodule.span K (Set.range (fun i : s => v i)) = Submodule.span K (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have := hspan ⟨j, Set.mem_univ j, rfl⟩
      simpa only [Set.image_eq_range] using this
  have hr : (Matrix.of A).rank = #s.toFinset := by
    rw [Matrix.rank_eq_finrank_span_cols, Set.toFinset_card, ← finrank_span_eq_card hli, hsp]
    rfl
  have hmain := matCount_mul_prod_le (A := A) g hinj c α s.toFinset (fun d hd h0 i => by
    have hsum : ∑ j : s, d j • v j = 0 := by
      have hall : ∑ j : ι, d j • v j = 0 := by
        ext a
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v]
        rw [← h0 a]
        exact sum_congr rfl fun _ _ => mul_comm _ _
      rw [← hall]
      exact (Finset.sum_congr_set s _ _ (fun _ _ => rfl)
        (fun j hj => by simp [hd j (by simpa using hj)])).symm
    by_cases hi : i ∈ s
    · exact Fintype.linearIndependent_iff.mp hli _ hsum ⟨i, hi⟩
    · exact hd i (by simpa using hi))
  have hpow : gm ^ #s.toFinset ≤ ∏ i ∈ s.toFinset, g i := by
    rw [← prod_const]
    exact prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => hgm i
  rw [hr]
  exact (Nat.mul_le_mul_left _ hpow).trans hmain

theorem matProb_le_of_prod (g : ι → ℕ) (hg : ∀ i, 0 < g i) {A : κ → ι → K} {c : ι → K} {α : κ → K} {D : ℕ} (hD : 0 < D)
    (h : matCount g c A α * D ≤ ∏ i, g i) : matProb g c A α ≤ 1 / (D : ℝ) := by
  have hP : (0 : ℝ) < ∏ i, (g i : ℝ) := prod_pos fun i _ => by exact_mod_cast hg i
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold matProb
  rw [div_le_div_iff₀ hP hD', one_mul]
  exact_mod_cast h

end Praxis.Combinatorics.Mass
