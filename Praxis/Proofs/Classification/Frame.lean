import Praxis.Proofs.Classification.Coordinates
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Data.Fintype.EquivFin

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {k : Type*} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    (V : Submodule k (I → k))

def evalAt (i : I) : Module.Dual k V := (LinearMap.proj i) ∘ₗ V.subtype

@[simp] theorem evalAt_apply (i : I) (x : V) : evalAt V i x = x.val i := rfl

theorem coordinate_dual_span : Submodule.span k (Set.range (evalAt V)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro x hx
  have hne : ∃ i, x.val i ≠ 0 := by
    by_contra! h
    apply hx
    apply Subtype.ext
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hne
  exact ⟨evalAt V i, ⟨i, rfl⟩, hi⟩

theorem exists_coordinate_dual_basis (i₀ : I) (h₀ : evalAt V i₀ ≠ 0) :
    ∃ (J : Set (Module.Dual k V)) (_ : Fintype J) (b : Module.Basis J k (Module.Dual k V))
      (j₀ : J) (idx : J → I),
      idx j₀ = i₀ ∧ (∀ j, b j = evalAt V (idx j)) := by
  classical
  let hs : LinearIndepOn k id {evalAt V i₀} :=
    (linearIndepOn_singleton_iff k).mpr h₀
  have hsub : ({evalAt V i₀} : Set (Module.Dual k V)) ⊆ Set.range (evalAt V) := by
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    exact ⟨i₀, rfl⟩
  let b := Module.Basis.extendLe hs hsub (coordinate_dual_span V).ge
  let J := hs.extend hsub
  letI : Fintype J := Fintype.ofFinite J
  have hmem : evalAt V i₀ ∈ Set.range b :=
    Module.Basis.subset_extendLe hs hsub (coordinate_dual_span V).ge (Set.mem_singleton _)
  obtain ⟨j₀, hj₀⟩ := hmem
  have hb : ∀ j : J, ∃ i, b j = evalAt V i := by
    intro j
    obtain ⟨i, hi⟩ := Module.Basis.extendLe_subset hs hsub (coordinate_dual_span V).ge ⟨j, rfl⟩
    exact ⟨i, hi.symm⟩
  let idx : J → I := fun j => if j = j₀ then i₀ else Classical.choose (hb j)
  refine ⟨J, inferInstance, b, j₀, idx, ?_, ?_⟩
  · simp [idx]
  · intro j
    dsimp [idx]
    split_ifs with hj
    · subst j
      exact hj₀
    · exact Classical.choose_spec (hb j)

end

end

end Praxis.Proofs.Classification
