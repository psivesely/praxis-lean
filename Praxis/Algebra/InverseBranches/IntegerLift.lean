import Praxis.Algebra.InverseBranches.LatticeChain
import Praxis.Combinatorics.Mass
import Praxis.Combinatorics.Chain

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.VectorInverse

open Finset Module Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def PivotGroup {d : ℕ} (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι) : AddSubgroup (Fin d → ℤ) :=
  (B.submatrix r id).transpose.mulVecLin.range.toAddSubgroup

theorem pivot_injective {d : ℕ} (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι)
    (hdet : (B.submatrix r id).det ≠ 0) : Function.Injective r := by
  intro i j hij
  by_contra hne
  apply hdet
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [Matrix.submatrix, hij])

theorem matrix_range_index {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (hdet : A.det ≠ 0) :
    A.mulVecLin.range.toAddSubgroup.index = A.det.natAbs := by
  let f := A.mulVecLin
  let e := LinearEquiv.ofInjective f (Matrix.mulVec_injective_of_det_ne_zero hdet)
  have h := Submodule.natAbs_det_equiv f.range e.toAddEquiv
  have hc : f.range.subtype ∘ₗ AddMonoidHom.toIntLinearMap
      (e.toAddEquiv : (Fin d → ℤ) →+ f.range) = f := by ext x i; rfl
  rw [hc] at h
  change (LinearMap.det (Matrix.toLin' A)).natAbs = _ at h
  rw [LinearMap.det_toLin'] at h
  exact h.symm

theorem pivotGroup_index {d : ℕ} (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι)
    (hdet : (B.submatrix r id).det ≠ 0) : (PivotGroup B r).index = (B.submatrix r id).det.natAbs := by
  unfold PivotGroup
  rw [matrix_range_index _ (by rwa [Matrix.det_transpose]), Matrix.det_transpose]

theorem pivot_fibBd {d : ℕ} (G : ι → ℕ) (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι)
    (hG : ∀ i, 0 < G i) (hdet : (B.submatrix r id).det ≠ 0) :
    FibBd G (fun i => B i) (univ.image r) (1 / ∏ k : Fin d, (G (r k) : ℝ)) := by
  have hr := pivot_injective B r hdet
  intro k₀ t
  have hp : (∏ i ∈ univ.image r, (G i : ℝ)) = ∏ k : Fin d, (G (r k) : ℝ) :=
    prod_image (fun _ _ _ _ h => hr h)
  have hp0 : (∏ k : Fin d, (G (r k) : ℝ)) ≠ 0 :=
    ne_of_gt (prod_pos fun k _ => by exact_mod_cast hG (r k))
  rw [hp, mul_one_div_cancel hp0]
  have hcount : #(fib G (fun i => B i) (univ.image r) k₀ t) ≤ 1 := by
    apply card_le_one.mpr
    intro k hk k' hk'
    obtain ⟨hoff, hs⟩ := mem_fib.mp hk
    obtain ⟨hoff', hs'⟩ := mem_fib.mp hk'
    have he : (B.submatrix r id).transpose *ᵥ (fun j => ((k (r j) : ℕ) : ℤ)) =
        (B.submatrix r id).transpose *ᵥ (fun j => ((k' (r j) : ℕ) : ℤ)) := by
      have hes := hs.trans hs'.symm
      rw [sum_image (fun _ _ _ _ h => hr h), sum_image (fun _ _ _ _ h => hr h)] at hes
      funext j
      have hh := congrFun hes j
      simpa only [Matrix.mulVec, Matrix.transpose_apply, Matrix.submatrix_apply,
        id_eq, dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply] using hh
    have hi := Matrix.mulVec_injective_of_det_ne_zero
      (show (B.submatrix r id).transpose.det ≠ 0 by rwa [Matrix.det_transpose]) he
    funext i
    by_cases him : i ∈ univ.image r
    · obtain ⟨j, _, rfl⟩ := mem_image.mp him
      exact Fin.ext (by exact_mod_cast congrFun hi j)
    · rw [hoff i him, hoff' i him]
  exact_mod_cast hcount

theorem pivot_rows_mem {d : ℕ} (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι) :
    ∀ i ∈ univ.image r, B i ∈ PivotGroup B r := by
  intro i hi
  obtain ⟨k, _, rfl⟩ := mem_image.mp hi
  refine ⟨Pi.single k 1, ?_⟩
  ext j
  simp [Matrix.submatrix]

end Praxis.Algebra.VectorInverse
