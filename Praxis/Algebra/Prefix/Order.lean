import Praxis.Algebra.Prefix.Definitions
import Mathlib.LinearAlgebra.FreeModule.Int
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.IntegerLift
import Praxis.Algebra.InverseBranches.LatticeChain

set_option autoImplicit false

namespace Praxis.Algebra.Prefix.Order

open Finset Module

open Praxis.Algebra.Prefix.Definitions

open scoped BigOperators Matrix

variable {ι : Type*} {d : ℕ}

theorem pivotGroup_le_rows (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι) :
    Algebra.VectorInverse.PivotGroup B r ≤ AddSubgroup.closure (Set.range B) := by
  rintro x ⟨a, rfl⟩
  have he : (B.submatrix r id).transpose.mulVecLin a =
      ∑ i, a i • B (r i) := by
    ext j
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [he]
  apply AddSubgroup.sum_mem
  intro i _
  have hb : B (r i) ∈ AddSubgroup.closure (Set.range B) :=
    AddSubgroup.subset_closure ⟨r i, rfl⟩
  exact AddSubgroup.zsmul_mem _ hb _

variable [Fintype ι]

theorem dvd_det_of_mem_rows (B : Matrix ι (Fin d) ℤ) (a : ℕ)
    (ha : ∀ r : Fin d → ι, a ∣ (B.submatrix r id).det.natAbs)
    (A : Matrix (Fin d) (Fin d) ℤ)
    (hA : ∀ i, A i ∈ AddSubgroup.closure (Set.range B)) :
    a ∣ A.det.natAbs := by
  have hs (i : Fin d) : A i ∈ Submodule.span ℤ (Set.range B) := by
    rw [← AddSubgroup.toIntSubmodule_closure]
    exact hA i
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hs i)
  have he : A = fun i => ∑ j, c i j • B j := by
    funext i
    exact (hc i).symm
  apply Int.natCast_dvd.mp
  rw [he]
  change (a : ℤ) ∣ Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ j, c i j • B j)
  rw [MultilinearMap.map_sum]
  apply Finset.dvd_sum
  intro r _
  rw [MultilinearMap.map_smul_univ]
  exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr (ha r)) _

theorem rows_index_eq_gcd (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι)
    (hr : (B.submatrix r id).det ≠ 0) :
    (AddSubgroup.closure (Set.range B)).index =
      univ.gcd (fun s : Fin d → ι => (B.submatrix s id).det.natAbs) := by
  classical
  let H := AddSubgroup.closure (Set.range B)
  let D := univ.gcd (fun s : Fin d → ι => (B.submatrix s id).det.natAbs)
  have hi : H.index ≠ 0 := by
    apply ne_zero_of_dvd_ne_zero (Int.natAbs_ne_zero.mpr hr)
    rw [← Algebra.VectorInverse.pivotGroup_index B r hr]
    exact AddSubgroup.index_dvd_of_le (pivotGroup_le_rows B r)
  have hi' : H.toIntSubmodule.toAddSubgroup.index ≠ 0 := hi
  obtain ⟨e⟩ := Int.submodule_toAddSubgroup_index_ne_zero_iff.mp hi'
  let b : Basis (Fin d) ℤ H := (Pi.basisFun ℤ (Fin d)).map e.symm
  have hb : H.index = (Matrix.of (fun i => (b i : Fin d → ℤ))).det.natAbs := by
    simpa only [Pi.basisFun_det_apply] using
      AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d)) H b
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro s _
    by_cases hz : (B.submatrix s id).det = 0
    · simp [hz]
    · rw [← Algebra.VectorInverse.pivotGroup_index B s hz]
      exact AddSubgroup.index_dvd_of_le (pivotGroup_le_rows B s)
  · rw [hb]
    exact dvd_det_of_mem_rows B D
      (fun s => Finset.gcd_dvd (mem_univ s)) _ (fun i => (b i).property)

variable {n k : ℕ}

theorem rows_eq_matrix (P : PivotFirstPrefix d n k) :
    P.rows = AddSubgroup.closure (Set.range P.matrix) := P.rows_eq

theorem prefix_index_eq_divisor (P : PivotFirstPrefix d n k) :
    P.rows.index = P.divisor := by
  let r : Fin d → Fin k := fun i => ⟨i.val, lt_of_lt_of_le i.isLt P.rank_le_prefix⟩
  have hp : (P.matrix.submatrix r id).det.natAbs = P.original.H := P.maximal_pivot
  have hn : (P.matrix.submatrix r id).det ≠ 0 := by
    intro hz
    have hpos := P.pivot_nonzero
    rw [← hp, hz, Int.natAbs_zero] at hpos
    omega
  rw [rows_eq_matrix]
  exact rows_index_eq_gcd P.matrix r hn

theorem closure_range_succ {A : Type*} [AddCommGroup A] (f : Fin (k+1) → A) :
    AddSubgroup.closure (Set.range f) =
      AddSubgroup.closure (Set.range (fun i : Fin k => f i.castSucc)) ⊔
        AddSubgroup.zmultiples (f (Fin.last k)) := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · apply (show AddSubgroup.closure (Set.range (fun i : Fin k => f i.castSucc)) ≤ _
        from le_sup_left)
      exact AddSubgroup.subset_closure ⟨j, rfl⟩
    · apply (show AddSubgroup.zmultiples (f (Fin.last k)) ≤ _ from le_sup_right)
      exact AddSubgroup.mem_zmultiples _
  · apply sup_le
    · apply (AddSubgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      exact AddSubgroup.subset_closure ⟨i.castSucc, rfl⟩
    · apply AddSubgroup.zmultiples_le.mpr
      exact AddSubgroup.subset_closure ⟨Fin.last k, rfl⟩

theorem next_rows (P : PivotFirstStep d n k) :
    P.next.rows = P.old.rows ⊔
      AddSubgroup.zmultiples (P.old.original.matrix P.newCoord) := by
  have hc : (fun i : Fin k => P.next.matrix i.castSucc) = P.old.matrix := by
    funext i j
    change P.next.original.matrix (P.next.coord i.castSucc) j =
      P.old.original.matrix (P.old.coord i) j
    simp only [PivotFirstPrefix.coord, P.same_original, P.same_order]
    rfl
  have hl : P.next.matrix (Fin.last k) = P.old.original.matrix P.newCoord := by
    change P.next.original.matrix (P.next.coord (Fin.last k)) =
      P.old.original.matrix P.newCoord
    simp only [PivotFirstPrefix.coord, PivotFirstStep.newCoord, P.same_original, P.same_order]
    rfl
  calc
    P.next.rows = AddSubgroup.closure (Set.range P.next.matrix) := rows_eq_matrix _
    _ = _ := closure_range_succ (fun i => P.next.matrix i)
    _ = _ := by rw [hc, hl, ← rows_eq_matrix]

theorem residueOrder_eq_relIndex (P : PivotFirstStep d n k) :
    P.residueOrder = P.old.rows.relIndex P.next.rows := by
  rw [next_rows, Algebra.VectorInverse.adjoin_relIndex]
  exact P.quotient_order

theorem prefix_order (P : PivotFirstStep d n k) : PrefixOrder P := by
  unfold PrefixOrder
  rw [← prefix_index_eq_divisor, ← prefix_index_eq_divisor, residueOrder_eq_relIndex]
  apply (AddSubgroup.relIndex_mul_index _).symm
  rw [next_rows]
  exact le_sup_left

end Praxis.Algebra.Prefix.Order
