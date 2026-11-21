import Praxis.Combinatorics.Mass

set_option autoImplicit false

set_option linter.style.haveILetI false

namespace Praxis.Algebra.FiniteProbability

open Finset

open scoped BigOperators

variable {Ω T Q X Y : Type*} [Fintype Ω]

noncomputable def fibreCount (f : Ω → T) (t : T) : ℕ := by
  classical
  exact #{x | f x = t}

noncomputable def pointProb (f : Ω → T) (t : T) : ℝ :=
  fibreCount f t / (Fintype.card Ω : ℝ)

noncomputable def atomMass (f : Ω → T) : ℝ := ⨆ t, pointProb f t

theorem pointProb_nonneg (f : Ω → T) (t : T) : 0 ≤ pointProb f t := by
  unfold pointProb
  positivity

theorem pointProb_le_one (f : Ω → T) (t : T) : pointProb f t ≤ 1 := by
  classical
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast (card_filter_le (univ : Finset Ω) (fun x => f x = t))

theorem pointProb_le_mass (f : Ω → T) (t : T) : pointProb f t ≤ atomMass f := by
  apply le_ciSup
  exact ⟨1, by rintro _ ⟨t, rfl⟩; exact pointProb_le_one f t⟩

theorem atomMass_le [Nonempty T] (f : Ω → T) {b : ℝ} (h : ∀ t, pointProb f t ≤ b) :
    atomMass f ≤ b := ciSup_le h

theorem atomMass_nonneg [Nonempty Ω] (f : Ω → T) : 0 ≤ atomMass f := by
  let x : Ω := Classical.choice inferInstance
  exact (pointProb_nonneg f (f x)).trans (pointProb_le_mass f (f x))

theorem pointProb_eq_sum [DecidableEq T] (f : Ω → T) (t : T) :
    pointProb f t = (∑ x : Ω, if f x = t then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  unfold pointProb fibreCount
  congr 1
  rw [card_eq_sum_ones]
  simp only [Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro x _
  split_ifs <;> norm_num

theorem pointProb_prod [Fintype X] [Fintype Y] (f : X × Y → T) (t : T) :
    pointProb f t = (∑ x : X, pointProb (fun y => f (x,y)) t) / Fintype.card X := by
  classical
  simp only [pointProb_eq_sum, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← sum_div]
  ring

theorem pointProb_mono (f : Ω → T) (g : Ω → Q) (t : T) (q : Q)
    (h : ∀ x, f x = t → g x = q) : pointProb f t ≤ pointProb g q := by
  classical
  unfold pointProb fibreCount
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (card_le_card (by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact h x hx))

theorem atomMass_comp_le [Nonempty Ω] (f : Ω → T) (φ : T → Q)
    (hφ : ∀ x y, φ (f x) = φ (f y) → f x = f y) :
    atomMass (φ ∘ f) ≤ atomMass f := by
  classical
  letI : Nonempty Q := ⟨φ (f (Classical.choice inferInstance))⟩
  apply atomMass_le
  intro t
  by_cases ht : ∃ x, φ (f x) = t
  · obtain ⟨x, hx⟩ := ht
    exact (pointProb_mono (φ ∘ f) f t (f x)
      (fun y hy => hφ y x (hy.trans hx.symm))).trans (pointProb_le_mass f (f x))
  · have hn : ∀ x, φ (f x) ≠ t := by simpa only [not_exists] using ht
    have hz : pointProb (φ ∘ f) t = 0 := by
      simp [pointProb_eq_sum, Function.comp_def, hn]
    rw [hz]
    exact atomMass_nonneg f

end Praxis.Algebra.FiniteProbability
