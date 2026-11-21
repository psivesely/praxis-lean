import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

namespace Praxis.Algebra.Prefix

open Finset

open Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Prefix.Definitions

open scoped BigOperators Matrix

variable {d n k : ℕ}

theorem old_row_mem (P : PivotFirstStep d n k) (i : Fin k) :
    P.next.matrix i.castSucc ∈ P.old.rows := by
  have he : P.next.matrix i.castSucc = P.old.matrix i := by
    unfold PivotFirstPrefix.matrix PivotFirstPrefix.coord
    rw [P.same_original, P.same_order]
    rfl
  rw [he, P.old.rows_eq]
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

theorem last_row_eq (P : PivotFirstStep d n k) :
    P.next.matrix (Fin.last k) = P.old.original.matrix P.newCoord := by
  unfold PivotFirstPrefix.matrix PivotFirstPrefix.coord PivotFirstStep.newCoord
  rw [P.same_original, P.same_order]
  rfl

theorem image_quotient (P : PivotFirstStep d n k)
    (r : Grid (P.next.grids P.grids)) :
    QuotientAddGroup.mk' P.old.rows
        (imageZ (P.next.grids P.grids) P.next.matrix r) =
      (r (Fin.last k) : ℕ) •
        QuotientAddGroup.mk' P.old.rows (P.old.original.matrix P.newCoord) := by
  let q := QuotientAddGroup.mk' P.old.rows
  have himage : imageZ (P.next.grids P.grids) P.next.matrix r =
      ∑ i : Fin (k + 1), (r i : ℕ) • P.next.matrix i := by
    ext j
    simp [imageZ, Finset.sum_apply, nsmul_eq_mul, mul_comm]
  have hsum : ∑ i : Fin k, q ((r i.castSucc : ℕ) • P.next.matrix i.castSucc) = 0 := by
    apply sum_eq_zero
    intro i _
    rw [map_nsmul]
    have hz : q (P.next.matrix i.castSucc) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (old_row_mem P i)
    rw [hz, nsmul_zero]
  change q _ = _
  rw [himage, Fin.sum_univ_castSucc, map_add, map_sum, hsum, zero_add,
    map_nsmul, last_row_eq]

theorem jump_pair (P : PivotFirstStep d n k)
    (hjump : P.grids P.newCoord ≤ P.residueOrder)
    (r s : Grid (P.next.grids P.grids))
    (he : imageZ (P.next.grids P.grids) P.next.matrix r =
      imageZ (P.next.grids P.grids) P.next.matrix s) :
    r (Fin.last k) = s (Fin.last k) := by
  have hwidth : P.next.grids P.grids (Fin.last k) = P.grids P.newCoord := by
    unfold PivotFirstPrefix.grids PivotFirstPrefix.coord PivotFirstStep.newCoord
    rw [P.same_order]
    rfl
  have hquot := congrArg (QuotientAddGroup.mk' P.old.rows) he
  rw [image_quotient, image_quotient] at hquot
  have horder : P.residueOrder =
      addOrderOf (QuotientAddGroup.mk' P.old.rows (P.old.original.matrix P.newCoord)) :=
    P.quotient_order
  have hr : (r (Fin.last k) : ℕ) <
      addOrderOf (QuotientAddGroup.mk' P.old.rows (P.old.original.matrix P.newCoord)) := by
    rw [← horder]
    exact lt_of_lt_of_le (by simpa only [hwidth] using (r (Fin.last k)).isLt) hjump
  have hs : (s (Fin.last k) : ℕ) <
      addOrderOf (QuotientAddGroup.mk' P.old.rows (P.old.original.matrix P.newCoord)) := by
    rw [← horder]
    exact lt_of_lt_of_le (by simpa only [hwidth] using (s (Fin.last k)).isLt) hjump
  apply Fin.ext
  exact nsmul_injOn_Iio_addOrderOf hr hs hquot

theorem jump_fixes_coordinate (P : PivotFirstStep d n k) : JumpFixesCoordinate P := by
  intro F hF hf hjump
  obtain ⟨r, hr⟩ := hF
  refine ⟨r (Fin.last k), ?_⟩
  intro s hs
  exact jump_pair P hjump s r (hf s hs r hr)

end Praxis.Algebra.Prefix
