import Praxis.Algebra.Point.Definitions
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

namespace Praxis.Algebra.Point

theorem exposedPoint : ExposedPoint := by
  classical
  intro e S hS
  obtain ⟨v, hv, hmax⟩ := S.exists_max_image (fun x => inner ℝ x x) hS
  refine ⟨v, hv, (innerSL ℝ v).toLinearMap, ?_⟩
  intro w hw hne
  have hle := hmax w hw
  have hpos : 0 < inner ℝ (w - v) (w - v) :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  rw [inner_sub_left, inner_sub_right, inner_sub_right] at hpos
  change inner ℝ v w < inner ℝ v v
  linarith [real_inner_comm w v]

end Praxis.Algebra.Point
