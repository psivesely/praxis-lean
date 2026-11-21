import Praxis.Algebra.Point.Definitions

noncomputable section

open MeasureTheory

namespace Praxis.Algebra.Point

theorem countDim0 : CountDim0 := by
  intro n S hS hdim
  have hspan : vectorSpan ℝ (S : Set (E n)) = ⊥ :=
    Submodule.finrank_eq_zero.mp hdim
  have hsub : (S : Set (E n)).Subsingleton :=
    (vectorSpan_eq_bot_iff_subsingleton ℝ).mp hspan
  obtain ⟨x, hx⟩ := hS
  apply Finset.card_eq_one.mpr
  refine ⟨x, ?_⟩
  ext y
  simp only [Finset.mem_singleton]
  exact ⟨fun hy => hsub hy hx, fun h => h ▸ hx⟩

end Praxis.Algebra.Point
