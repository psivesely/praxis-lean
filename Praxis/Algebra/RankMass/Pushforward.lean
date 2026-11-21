import Praxis.Algebra.Stmt.RankMass
import Praxis.Algebra.Definitions.Sampler

set_option autoImplicit false

namespace Praxis.Algebra.RankMass

open Finset Matrix

open scoped BigOperators

section FiniteLaw

variable {X Y Z : Type*} [Fintype X]

theorem atom_nonneg (f : X → Y) (y : Y) : 0 ≤ atom f y := by
  classical
  rw [atom_eq_count]
  positivity

theorem atom_le_one (f : X → Y) (y : Y) : atom f y ≤ 1 := by
  classical
  rw [atom_eq_count]
  by_cases h : Fintype.card X = 0
  · simp [h]
  · apply (div_le_one₀ (by exact_mod_cast Nat.pos_of_ne_zero h)).2
    exact_mod_cast (card_filter_le (s := (univ : Finset X)) (p := fun x => f x = y))

theorem atoms_bddAbove (f : X → Y) : BddAbove (Set.range (atom f)) :=
  ⟨1, by rintro _ ⟨y, rfl⟩; exact atom_le_one f y⟩

theorem atom_le_maxAtom_general (f : X → Y) (y : Y) : atom f y ≤ maxAtom f :=
  le_ciSup (atoms_bddAbove f) y

theorem maxAtom_nonneg [Nonempty Y] (f : X → Y) : 0 ≤ maxAtom f :=
  (atom_nonneg f (Classical.arbitrary Y)).trans
    (atom_le_maxAtom_general f (Classical.arbitrary Y))

theorem atom_le_of_fibre_subset (f : X → Y) (h : X → Z) (y : Y) (z : Z)
    (hsub : ∀ x, f x = y → h x = z) : atom f y ≤ atom h z := by
  classical
  rw [atom_eq_count, atom_eq_count]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (show univ.filter (fun x => f x = y) ⊆
    univ.filter (fun x => h x = z) from fun x hx => by
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hsub x hx)

theorem maxAtom_le_of_fibre_refinement [Nonempty Y] [Nonempty Z]
    (f : X → Y) (h : X → Z)
    (href : ∀ x x', f x = f x' → h x = h x') : maxAtom f ≤ maxAtom h := by
  classical
  apply ciSup_le
  intro y
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, hx⟩ := hy
    exact (atom_le_of_fibre_subset f h y (h x)
      (fun x' hx' => href x' x (hx'.trans hx.symm))).trans
      (atom_le_maxAtom_general h (h x))
  · have hempty : univ.filter (fun x => f x = y) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hy ⟨x, hx⟩
    rw [atom_eq_count, hempty, card_empty, Nat.cast_zero, zero_div]
    exact maxAtom_nonneg h

end FiniteLaw

section Span

variable {I J F : Type*} [Fintype I] [CommSemiring F]

theorem dotProduct_eq_of_mem_span (V : J → I → F) {z : I → F}
    (hz : z ∈ Submodule.span F (Set.range V)) (a b : I → F)
    (h : ∀ j, V j ⬝ᵥ a = V j ⬝ᵥ b) : z ⬝ᵥ a = z ⬝ᵥ b := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    exact h j
  | zero => simp
  | add x y _ _ hx hy => simp only [add_dotProduct, hx, hy]
  | smul c x _ hx => simp only [smul_dotProduct, hx]

theorem maxAtom_readout_le_scalar {X : Type*} [Fintype X]
    (R : X → I → F) (V : J → I → F) (z : I → F)
    (hz : z ∈ Submodule.span F (Set.range V)) :
    maxAtom (fun x j => V j ⬝ᵥ R x) ≤ maxAtom (fun x => z ⬝ᵥ R x) := by
  apply maxAtom_le_of_fibre_refinement
  intro x x' hx
  exact dotProduct_eq_of_mem_span V hz (R x) (R x') (fun j => congrFun hx j)

end Span

end Praxis.Algebra.RankMass
