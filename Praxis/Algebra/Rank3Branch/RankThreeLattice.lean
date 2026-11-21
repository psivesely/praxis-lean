import Praxis.Algebra.Rank3Branch.QuotientChain
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Praxis.Combinatorics.Chain
import Praxis.Algebra.ChainLemma.UnequalChain

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.RankThree

open Finset Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev rowVector (B : Matrix ι (Fin 3) ℤ) (i : ι) : Fin 3 → ℤ := B i

def PrimitiveRows (B : Matrix ι (Fin 3) ℤ) : Prop :=
  AddSubgroup.closure (Set.range (rowVector B)) = ⊤

theorem pivot_injective (B : Matrix ι (Fin 3) ℤ) (r : Fin 3 → ι)
    (hdet : (B.submatrix r id).det ≠ 0) : Function.Injective r := by
  intro i j hij
  by_contra hne
  apply hdet
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [Matrix.submatrix, hij])

theorem matrix_range_index (A : Matrix (Fin 3) (Fin 3) ℤ) (hdet : A.det ≠ 0) :
    A.mulVecLin.range.toAddSubgroup.index = A.det.natAbs := by
  let f := A.mulVecLin
  let e := LinearEquiv.ofInjective f (Matrix.mulVec_injective_of_det_ne_zero hdet)
  have h := Submodule.natAbs_det_equiv f.range e.toAddEquiv
  have hc : f.range.subtype ∘ₗ AddMonoidHom.toIntLinearMap
      (e.toAddEquiv : (Fin 3 → ℤ) →+ f.range) = f := by ext x i; rfl
  rw [hc] at h
  change (LinearMap.det (Matrix.toLin' A)).natAbs = _ at h
  rw [LinearMap.det_toLin'] at h
  exact h.symm

theorem pivot_fibBd (G : ι → ℕ) (B : Matrix ι (Fin 3) ℤ) (r : Fin 3 → ι)
    (hG : ∀ i, 0 < G i) (hdet : (B.submatrix r id).det ≠ 0) :
    FibBd G (rowVector B) (univ.image r) (1 / ∏ k : Fin 3, (G (r k) : ℝ)) := by
  have hr := pivot_injective B r hdet
  intro k₀ t
  have hp : (∏ i ∈ univ.image r, (G i : ℝ)) = ∏ k : Fin 3, (G (r k) : ℝ) :=
    prod_image (fun _ _ _ _ h => hr h)
  have hp0 : (∏ k : Fin 3, (G (r k) : ℝ)) ≠ 0 :=
    ne_of_gt (prod_pos fun k _ => by exact_mod_cast hG (r k))
  rw [hp, mul_one_div_cancel hp0]
  have hcount : #(fib G (rowVector B) (univ.image r) k₀ t) ≤ 1 := by
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
        id_eq, dotProduct, rowVector, Finset.sum_apply, Pi.mul_apply,
        Pi.natCast_apply] using hh
    have hi := Matrix.mulVec_injective_of_det_ne_zero
      (show (B.submatrix r id).transpose.det ≠ 0 by rwa [Matrix.det_transpose]) he
    funext i
    by_cases him : i ∈ univ.image r
    · obtain ⟨j, _, rfl⟩ := mem_image.mp him
      exact Fin.ext (by exact_mod_cast congrFun hi j)
    · rw [hoff i him, hoff' i him]
  exact_mod_cast hcount

theorem integer_fibBd {G : ι → ℕ} {B : Matrix ι (Fin 3) ℤ} {g N : ℕ}
    (hg : 0 < g) (hG : ∀ i, g ≤ G i) (hpow : g ≤ 2 ^ N)
    (hprimitive : PrimitiveRows B) (r : Fin 3 → ι)
    (hdet : (B.submatrix r id).det ≠ 0) :
    FibBd G (rowVector B) univ
      ((1 / (g : ℝ) ^ 3) * correction g ^ N *
        (1 / ((B.submatrix r id).det.natAbs : ℝ) + 1 / (g : ℝ))) := by
  let A := (B.submatrix r id).transpose
  let H := A.mulVecLin.range.toAddSubgroup
  let M := (B.submatrix r id).det.natAbs
  let D : ℝ := 1 / ∏ k : Fin 3, (G (r k) : ℝ)
  have hGp : ∀ i, 0 < G i := fun i => lt_of_lt_of_le hg (hG i)
  have hH : H.index = M := by
    dsimp [H, A, M]
    rw [matrix_range_index _ (by rwa [Matrix.det_transpose]), Matrix.det_transpose]
  have hmem (i : Fin 3) : rowVector B (r i) ∈ H := by
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    simp [A, Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.transpose_apply,
      rowVector, Pi.single_apply]
  have st : ChainState G (rowVector B) g M D (univ.image r) H 1 0 D := {
    contains := by rintro i hi; obtain ⟨j, _, rfl⟩ := mem_image.mp hi; exact hmem j
    indexpos := by rw [hH]; exact Int.natAbs_pos.mpr hdet
    tpos := one_pos
    product := by rw [hH, mul_one]
    bd := pivot_fibBd G B r hGp hdet
    merged := by
      simp only [pow_zero, mul_one, Nat.cast_one, one_div_one]
      have : 0 ≤ D * (1 / (g : ℝ)) := by dsimp [D]; positivity
      nlinarith
    coarse := by simp }
  have hb := finish_chain hg hG hpow (show 0 ≤ D by dsimp [D]; positivity)
    hprimitive N (by omega) st
  apply hb.mono
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by unfold correction; positivity)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (g : ℝ) ^ 3 = ∏ _ : Fin 3, (g : ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => hg0.le) (fun i _ => by exact_mod_cast hG (r i))

end Praxis.Algebra.RankThree
