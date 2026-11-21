import Praxis.Algebra.Point.Definitions
import Mathlib.Tactic.Linarith

namespace Praxis.Algebra.Point

theorem three_le_card_of_spanDim_eq_two (S : Finset (E 2)) (hspan : spanDim S = 2) :
    3 ≤ S.card := by
  have hnonempty : S.Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    subst S
    unfold spanDim at hspan
    rw [Finset.coe_empty, vectorSpan_empty] at hspan
    simp at hspan
  have hpos : 0 < S.card := Finset.card_pos.mpr hnonempty
  have hdim := finrank_vectorSpan_image_finset_le ℝ (id : E 2 → E 2) S
    (n := S.card - 1) (by omega)
  have hdim' : spanDim S ≤ S.card - 1 := by
    unfold spanDim
    rw [Finset.image_id] at hdim
    exact hdim
  omega

theorem planarCount_of_simplexCount (hcount : SimplexCount 2) : PlanarCount := by
  intro L a S hcoset hspan
  have hcard : (3 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast three_le_card_of_spanDim_eq_two S hspan
  have hbound : (S.card : ℝ) ≤ 2 * (volHull S / L.det) + 2 := by
    simpa only [show (2 : ℕ).factorial = 2 from rfl, Nat.cast_ofNat, mul_div_assoc]
      using hcount (by decide) (by decide) L a S hcoset hspan
  have harea : (1 : ℝ) / 2 ≤ volHull S / L.det := by linarith
  rw [mul_div_assoc]
  linarith

end Praxis.Algebra.Point
