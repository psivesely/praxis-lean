import Praxis.Algebra.Probe.SZ
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Praxis.Algebra.Stmt.ProbeSZ

noncomputable section

namespace Praxis.Algebra.ProbeSZ

open scoped BigOperators Classical

theorem uniformProb_eq_sum {Ω : Type} [Fintype Ω] (E : Ω → Prop) :
    uniformProb E = (∑ x : Ω, if E x then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  simp [uniformProb, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole]

theorem uniformProb_or_le {Ω : Type} [Fintype Ω] (E G : Ω → Prop) :
    uniformProb (fun x => E x ∨ G x) ≤ uniformProb E + uniformProb G := by
  classical
  simp only [uniformProb_eq_sum, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> simp_all

theorem uniformProb_prod {X Y : Type} [Fintype X] [Fintype Y] (E : X → Y → Prop) :
    uniformProb (fun z : X × Y => E z.1 z.2) =
      (∑ x, uniformProb (E x)) / Fintype.card X := by
  classical
  simp only [uniformProb_eq_sum, Fintype.sum_prod_type, Fintype.card_prod,
    Nat.cast_mul, Finset.sum_div, div_div]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem uniformProb_prod_le {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y]
    (E : X → Y → Prop) (ε : ℝ) (h : ∀ x, uniformProb (E x) ≤ ε) :
    uniformProb (fun z : X × Y => E z.1 z.2) ≤ ε := by
  rw [uniformProb_prod]
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  calc
    (∑ x, uniformProb (E x)) / Fintype.card X ≤
        (∑ _ : X, ε) / Fintype.card X :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) hc.le
    _ = ε := by simp [hc.ne']

theorem uniformProb_prod_left {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y]
    (E : X → Prop) : uniformProb (fun z : X × Y => E z.1) = uniformProb E := by
  classical
  have hc : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hconst (x : X) : uniformProb (fun _ : Y => E x) = if E x then (1 : ℝ) else 0 := by
    by_cases hx : E x <;> simp [uniformProb, hx, Nat.card_eq_fintype_card, hc]
  rw [uniformProb_prod (fun (x : X) (_ : Y) => E x)]
  simp_rw [hconst]
  exact (uniformProb_eq_sum E).symm

def threeCoinsEquiv (Ω : Type) : (Fin 3 → Ω) ≃ Ω × Ω × Ω where
  toFun c := (c 0, c 1, c 2)
  invFun c := ![c.1, c.2.1, c.2.2]
  left_inv c := by funext i; fin_cases i <;> rfl
  right_inv c := by rcases c with ⟨a, b, c⟩; rfl

def growSpan {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (U : Submodule F V) (v : V) : Submodule F V := U ⊔ Submodule.span F {v}

theorem lt_growSpan {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (U : Submodule F V) (v : V) (hv : v ∉ U) : U < growSpan U v := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  apply hv
  rw [heq]
  exact Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem triple_span_eq {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (v : Fin 3 → V) :
    Submodule.span F (Set.range v) =
      growSpan (growSpan (growSpan (⊥ : Submodule F V) (v 0)) (v 1)) (v 2) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.subset_span (by simp))))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
  · simp only [growSpan, sup_le_iff, bot_le, true_and]
    exact ⟨⟨Submodule.span_le.mpr (by simpa using
      (show v 0 ∈ Submodule.span F (Set.range v) from Submodule.subset_span ⟨0, rfl⟩)),
      Submodule.span_le.mpr (by simpa using
      (show v 1 ∈ Submodule.span F (Set.range v) from Submodule.subset_span ⟨1, rfl⟩))⟩,
      Submodule.span_le.mpr (by simpa using
      (show v 2 ∈ Submodule.span F (Set.range v) from Submodule.subset_span ⟨2, rfl⟩))⟩

theorem triple_failure_step {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (W : Submodule F V) [FiniteDimensional F W] (v : Fin 3 → V)
    (hv : ∀ i, v i ∈ W) (hr : Module.finrank F W ≤ 3)
    (hfail : Submodule.span F (Set.range v) ≠ W) :
    ((⊥ : Submodule F V) < W ∧ v 0 ∈ (⊥ : Submodule F V)) ∨
    (growSpan ⊥ (v 0) < W ∧ v 1 ∈ growSpan (F := F) ⊥ (v 0)) ∨
    (growSpan (growSpan ⊥ (v 0)) (v 1) < W ∧
      v 2 ∈ growSpan (F := F) (growSpan ⊥ (v 0)) (v 1)) := by
  let U₀ : Submodule F V := ⊥
  let U₁ := growSpan U₀ (v 0)
  let U₂ := growSpan U₁ (v 1)
  let U₃ := growSpan U₂ (v 2)
  have hg (U : Submodule F V) (i : Fin 3) (hU : U ≤ W) : growSpan U (v i) ≤ W :=
    sup_le hU (Submodule.span_le.mpr (by simpa using hv i))
  have h01 : U₀ ≤ U₁ := le_sup_left
  have h12 : U₁ ≤ U₂ := le_sup_left
  have h23 : U₂ ≤ U₃ := le_sup_left
  have h3 : U₃ < W := lt_of_le_of_ne (hg _ 2 (hg _ 1 (hg _ 0 bot_le)))
    (by simpa only [triple_span_eq] using hfail)
  have h2 : U₂ < W := lt_of_le_of_lt h23 h3
  have h1 : U₁ < W := lt_of_le_of_lt h12 h2
  have h0 : U₀ < W := lt_of_le_of_lt h01 h1
  by_contra h
  have hn0 : v 0 ∉ U₀ := fun hh => h (Or.inl ⟨h0, hh⟩)
  have hn1 : v 1 ∉ U₁ := fun hh => h (Or.inr (Or.inl ⟨h1, hh⟩))
  have hn2 : v 2 ∉ U₂ := fun hh => h (Or.inr (Or.inr ⟨h2, hh⟩))
  have : FiniteDimensional F U₁ := Submodule.finiteDimensional_of_le h1.le
  have : FiniteDimensional F U₂ := Submodule.finiteDimensional_of_le h2.le
  have : FiniteDimensional F U₃ := Submodule.finiteDimensional_of_le h3.le
  have hd01 := Submodule.finrank_lt_finrank_of_lt (lt_growSpan U₀ (v 0) hn0)
  have hd12 := Submodule.finrank_lt_finrank_of_lt (lt_growSpan U₁ (v 1) hn1)
  have hd23 := Submodule.finrank_lt_finrank_of_lt (lt_growSpan U₂ (v 2) hn2)
  have hd3 := Submodule.finrank_lt_finrank_of_lt h3
  change Module.finrank F U₀ < Module.finrank F U₁ at hd01
  change Module.finrank F U₁ < Module.finrank F U₂ at hd12
  change Module.finrank F U₂ < Module.finrank F U₃ at hd23
  omega

theorem uniformProb_triple_span {F V Ω : Type} [Field F] [AddCommGroup V] [Module F V]
    [Fintype Ω] [Nonempty Ω] (W : Submodule F V) [FiniteDimensional F W]
    (f : Ω → V) (hf : ∀ c, f c ∈ W) (hr : Module.finrank F W ≤ 3)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ U : Submodule F V, U < W → uniformProb (fun c => f c ∈ U) ≤ ε) :
    uniformProb (fun cs : Fin 3 → Ω => Submodule.span F (Set.range (f ∘ cs)) ≠ W) ≤
      3 * ε := by
  classical
  let E (U : Submodule F V) (c : Ω) := U < W ∧ f c ∈ U
  have hb (U : Submodule F V) : uniformProb (E U) ≤ ε := by
    by_cases hU : U < W
    · simpa only [E, hU, true_and] using hbound U hU
    · simpa [E, hU, uniformProb] using hε
  let A (z : Ω × Ω × Ω) := E ⊥ z.1
  let B (z : Ω × Ω × Ω) := E (growSpan ⊥ (f z.1)) z.2.1
  let C (z : Ω × Ω × Ω) := E (growSpan (growSpan ⊥ (f z.1)) (f z.2.1)) z.2.2
  have hA : uniformProb A ≤ ε := by
    dsimp [A]
    rw [uniformProb_prod_left]
    exact hb ⊥
  have hB : uniformProb B ≤ ε := by
    exact uniformProb_prod_le (fun (a : Ω) (yz : Ω × Ω) => E (growSpan ⊥ (f a)) yz.1) ε
      (fun a => (uniformProb_prod_left _).le.trans (hb _))
  have hC : uniformProb C ≤ ε := by
    exact uniformProb_prod_le
      (fun (a : Ω) (yz : Ω × Ω) => E (growSpan (growSpan ⊥ (f a)) (f yz.1)) yz.2) ε
      (fun a => uniformProb_prod_le
        (fun (b c : Ω) => E (growSpan (growSpan ⊥ (f a)) (f b)) c) ε (fun b => hb _))
  have hmono : uniformProb (fun cs : Fin 3 → Ω =>
      Submodule.span F (Set.range (f ∘ cs)) ≠ W) ≤
      uniformProb (fun cs => A (threeCoinsEquiv Ω cs) ∨
        B (threeCoinsEquiv Ω cs) ∨ C (threeCoinsEquiv Ω cs)) := by
    apply uniformProb_mono
    intro cs hcs
    exact triple_failure_step W (f ∘ cs) (fun i => hf (cs i)) hr hcs
  have heq := uniformProb_equiv (threeCoinsEquiv Ω) (fun z => A z ∨ B z ∨ C z)
  have hu := uniformProb_or_le A (fun z => B z ∨ C z)
  have hv := uniformProb_or_le B C
  calc
    _ ≤ _ := hmono
    _ = _ := heq
    _ ≤ uniformProb A + uniformProb (fun z => B z ∨ C z) := hu
    _ ≤ uniformProb A + (uniformProb B + uniformProb C) := add_le_add le_rfl hv
    _ ≤ ε + (ε + ε) := add_le_add hA (add_le_add hB hC)
    _ = 3 * ε := by ring

end Praxis.Algebra.ProbeSZ
