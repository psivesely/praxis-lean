import Praxis.Proofs.Basic

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {k X M S : Type*} [Field k] [AddCommGroup M] [Module k M] [Fintype S]

theorem indexed_to_finset (p : S → X) (r : S → k) (H : X → M) (P : X → Prop)
    (hp : ∀ s, r s ≠ 0 → P (p s)) :
    ∃ (xs : Finset X) (ρ : X → k), (∀ x ∈ xs, P x) ∧
      (∑ s, r s • H (p s)) = ∑ x ∈ xs, ρ x • H x := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : DecidableEq k := Classical.decEq k
  letI : DecidableEq S := Classical.decEq S
  let t : Finset S := Finset.univ.filter (fun s => r s ≠ 0)
  let xs : Finset X := t.image p
  let ρ := fun x => ∑ s ∈ t.filter (fun s => p s = x), r s
  refine ⟨xs, ρ, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact hp s (Finset.mem_filter.mp hs).2
  · have hgroup : (∑ x ∈ xs, ρ x • H x) = ∑ s ∈ t, r s • H (p s) := by
      change (∑ x ∈ t.image p, ρ x • H x) = _
      apply Finset.sum_image' (fun s => r s • H (p s))
      intro s hs
      simp only [ρ, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    rw [hgroup]
    symm
    change (∑ s ∈ Finset.univ.filter (fun s => r s ≠ 0), r s • H (p s)) = _
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    have hr : r s = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hs, hn⟩)
    rw [hr, zero_smul]

end

end

end Praxis.Proofs.Classification
