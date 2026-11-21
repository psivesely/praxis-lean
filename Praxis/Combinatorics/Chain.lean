import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

namespace Praxis.Combinatorics

open Finset

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Fib

variable {A : Type*} [CommRing A] [DecidableEq A]

def fib (g : ι → ℕ) (y : ι → A) (S : Finset ι) (k₀ : (i : ι) → Fin (g i)) (t : A) : Finset ((i : ι) → Fin (g i)) :=
  {k | (∀ i, i ∉ S → k i = k₀ i) ∧ ∑ i ∈ S, y i * ((k i : ℕ) : A) = t}

theorem mem_fib {g : ι → ℕ} {y : ι → A} {S : Finset ι} {k₀ : (i : ι) → Fin (g i)} {t : A} {k : (i : ι) → Fin (g i)} :
    k ∈ fib g y S k₀ t ↔ (∀ i, i ∉ S → k i = k₀ i) ∧ ∑ i ∈ S, y i * ((k i : ℕ) : A) = t := by
  simp [fib]

def FibBd (g : ι → ℕ) (y : ι → A) (S : Finset ι) (ρ : ℝ) : Prop :=
  ∀ k₀ t, (#(fib g y S k₀ t) : ℝ) ≤ (∏ j ∈ S, (g j : ℝ)) * ρ

theorem card_fib_insert_le {g : ι → ℕ} {y : ι → A} {S : Finset ι} {j : ι} (hj : j ∉ S) {C : ℝ}
    (hC : ∀ k₀ t, (#(fib g y S k₀ t) : ℝ) ≤ C) (k₀ : (i : ι) → Fin (g i)) (t : A) (R : Finset (Fin (g j)))
    (hR : ∀ k ∈ fib g y (insert j S) k₀ t, k j ∈ R) :
    (#(fib g y (insert j S) k₀ t) : ℝ) ≤ #R * C := by
  have h1 := card_eq_sum_card_fiberwise (f := fun k : (i : ι) → Fin (g i) => k j)
    (s := fib g y (insert j S) k₀ t) (t := R) (fun k hk => hR k (by simpa using hk))
  have h2 : ∀ a ∈ R, ((#{k ∈ fib g y (insert j S) k₀ t | k j = a} : ℕ) : ℝ) ≤ C := by
    intro a _
    refine le_trans ?_ (hC (Function.update k₀ j a) (t - y j * ((a : ℕ) : A)))
    refine Nat.cast_le.mpr (card_le_card fun k hk => ?_)
    obtain ⟨hk1, hka⟩ := mem_filter.mp hk
    obtain ⟨hoff, hsum⟩ := mem_fib.mp hk1
    refine mem_fib.mpr ⟨fun i hi => ?_, ?_⟩
    · by_cases hij : i = j
      · subst hij; simpa using hka
      · rw [Function.update_of_ne hij]
        exact hoff i (by simp [hij, hi])
    · rw [sum_insert hj, hka] at hsum
      rw [← hsum]; ring
  rw [h1]
  push_cast
  calc ∑ a ∈ R, ((#{k ∈ fib g y (insert j S) k₀ t | k j = a} : ℕ) : ℝ) ≤ #R • C := sum_le_card_nsmul _ _ _ h2
    _ = #R * C := by simp

theorem FibBd.mono {g : ι → ℕ} {y : ι → A} {S : Finset ι} {ρ ρ' : ℝ} (h : FibBd g y S ρ) (hρ : ρ ≤ ρ') : FibBd g y S ρ' :=
  fun k₀ t => le_trans (h k₀ t) (mul_le_mul_of_nonneg_left hρ (prod_nonneg fun _ _ => Nat.cast_nonneg _))

theorem FibBd.nonneg {g : ι → ℕ} {y : ι → A} {S : Finset ι} {ρ : ℝ} (h : FibBd g y S ρ) (k₀ : (i : ι) → Fin (g i)) :
    0 ≤ (∏ j ∈ S, (g j : ℝ)) * ρ :=
  le_trans (Nat.cast_nonneg _) (h k₀ 0)

theorem fibBd_insert {g : ι → ℕ} {y : ι → A} {S : Finset ι} {ρ : ℝ} {j : ι} (hj : j ∉ S) (h : FibBd g y S ρ) :
    FibBd g y (insert j S) ρ := by
  intro k₀ t
  have := card_fib_insert_le hj h k₀ t univ (fun _ _ => mem_univ _)
  rw [prod_insert hj]
  simpa [mul_assoc] using this

theorem FibBd.extend {g : ι → ℕ} {y : ι → A} {S S₀ : Finset ι} {ρ : ℝ} (h : FibBd g y S ρ) (hS : S ⊆ S₀) : FibBd g y S₀ ρ := by
  have key : ∀ D : Finset ι, FibBd g y (D ∪ S) ρ := by
    intro D
    induction D using Finset.induction_on with
    | empty => simpa using h
    | insert j D _ ih =>
      by_cases hj : j ∈ D ∪ S
      · rwa [insert_union, insert_eq_of_mem hj]
      · rw [insert_union]; exact fibBd_insert hj ih
  have := key S₀
  rwa [union_eq_left.mpr hS] at this

theorem fib_univ (g : ι → ℕ) (y : ι → A) (k₀ : (i : ι) → Fin (g i)) (t : A) :
    fib g y univ k₀ t = ({k : (i : ι) → Fin (g i) | ∑ i, y i * ((k i : ℕ) : A) = t} : Finset _) := by
  ext k; simp [fib]

end Fib

theorem card_le_ceil {g v : ℕ} (hv : 0 < v) (R : Finset (Fin g)) (hR : ∀ a ∈ R, ∀ a' ∈ R, (a : ℕ) ≡ a' [MOD v]) :
    #R ≤ (g + v - 1) / v := by
  have : #R ≤ #(range ((g + v - 1) / v)) := by
    refine card_le_card_of_injOn (fun a => (a : ℕ) / v) (fun a _ => ?_) ?_
    · refine mem_coe.mpr (mem_range.mpr ?_)
      have h1 : ((a : ℕ) + v) / v ≤ (g + v - 1) / v := Nat.div_le_div_right (by have := a.isLt; omega)
      rw [Nat.add_div_right _ hv] at h1
      exact h1
    · intro a ha a' ha' he
      have h1 : (a : ℕ) % v = a' % v := hR a ha a' ha'
      have he' : (a : ℕ) / v = a' / v := he
      apply Fin.ext
      rw [← Nat.mod_add_div (a : ℕ) v, ← Nat.mod_add_div (a' : ℕ) v, h1, he']
  simpa using this

end Praxis.Combinatorics
