import Praxis.Algebra.Basis.ElementaryModel
import Praxis.Algebra.Basis.Definitions
import Praxis.Algebra.Conversion.L1Minkowski
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

noncomputable section

namespace Praxis.Algebra.Basis

universe u

open Praxis.Algebra.Basis.ElementaryModel Praxis.Algebra.Inverse.Definitions

open scoped BigOperators Matrix

theorem columnL1_sq_le_three_dot (C : ZMatrix 3) (j : Fin 3) :
    (columnL1 C j : ℚ) ^ 2 ≤ 3 * dotQ (columnQ C j) (columnQ C j) := by
  have h01 := sq_nonneg (|(C 0 j : ℚ)| - |(C 1 j : ℚ)|)
  have h02 := sq_nonneg (|(C 0 j : ℚ)| - |(C 2 j : ℚ)|)
  have h12 := sq_nonneg (|(C 1 j : ℚ)| - |(C 2 j : ℚ)|)
  simp [columnL1, dotQ, columnQ, Fin.sum_univ_succ, Nat.cast_natAbs,
    Int.cast_abs]
  nlinarith [sq_abs (C 0 j : ℚ), sq_abs (C 1 j : ℚ), sq_abs (C 2 j : ℚ)]

theorem rank3_scalar_bound {t₁ t₂ t₃ n₁ n₂ n₃ h : ℚ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hn₃ : 0 ≤ n₃) (hh : 0 ≤ h)
    (h12 : 3 * t₁ ≤ 4 * t₂) (h23 : 3 * t₂ ≤ 4 * t₃)
    (hb₁ : n₁ ^ 2 ≤ 3 * t₁)
    (hb₂ : n₂ ^ 2 ≤ 3 * (t₂ + t₁ / 4))
    (hb₃ : n₃ ^ 2 ≤ 3 * (t₃ + t₂ / 4 + t₁ / 4))
    (hdet : t₁ * t₂ * t₃ = h ^ 2) :
    n₁ * n₂ * n₃ ≤ 8 * h := by
  have hb₂' : n₂ ^ 2 ≤ 4 * t₂ := by linarith
  have hb₃' : n₃ ^ 2 ≤ (16 / 3 : ℚ) * t₃ := by linarith
  have hp12 : n₁ ^ 2 * n₂ ^ 2 ≤ (3 * t₁) * (4 * t₂) :=
    mul_le_mul hb₁ hb₂' (sq_nonneg _) (by positivity)
  have hp123 : (n₁ ^ 2 * n₂ ^ 2) * n₃ ^ 2 ≤
      ((3 * t₁) * (4 * t₂)) * ((16 / 3 : ℚ) * t₃) :=
    mul_le_mul hp12 hb₃' (sq_nonneg _) (by positivity)
  have heq : ((3 * t₁) * (4 * t₂)) * ((16 / 3 : ℚ) * t₃) = 64 * h ^ 2 := by
    calc
      _ = 64 * (t₁ * t₂ * t₃) := by ring
      _ = _ := by rw [hdet]
  rw [heq] at hp123
  have hp : (n₁ * n₂ * n₃) ^ 2 ≤ (8 * h) ^ 2 := by nlinarith [hp123]
  exact (sq_le_sq₀ (mul_nonneg (mul_nonneg hn₁ hn₂) hn₃) (by positivity)).mp hp

theorem half_abs_sq {x : ℚ} (hx : |x| ≤ (1 / 2 : ℚ)) : x ^ 2 ≤ 1 / 4 := by
  have h := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℚ) ≤ 1 / 2)).2 hx
  norm_num only [sq_abs] at h
  norm_num at h ⊢
  exact h

theorem reduced_columnL1Product_le (C : ZMatrix 3) (g : Gram3Facts C)
    (hs : SizeBounds3 C) (h12 : 3 * t1 C ≤ 4 * t2 C)
    (h23 : 3 * t2 C ≤ 4 * t3 C) :
    columnL1Product C ≤ 8 * C.det.natAbs := by
  have ht₁ := g.positive.2.2.1.le
  have ht₂ := g.positive.2.2.2.1.le
  have hm21 := mul_le_mul_of_nonneg_right (half_abs_sq hs.1) ht₁
  have hm31 := mul_le_mul_of_nonneg_right (half_abs_sq hs.2.1) ht₁
  have hm32 := mul_le_mul_of_nonneg_right (half_abs_sq hs.2.2) ht₂
  have hb₁ := columnL1_sq_le_three_dot C 0
  have hb₂ := columnL1_sq_le_three_dot C 1
  have hb₃ := columnL1_sq_le_three_dot C 2
  rw [g.norms.1] at hb₁
  rw [g.norms.2.1] at hb₂
  rw [g.norms.2.2] at hb₃
  have hdet : t1 C * t2 C * t3 C = (C.det.natAbs : ℚ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    exact g.determinant.2
  have hp := rank3_scalar_bound ht₁ ht₂
    (Nat.cast_nonneg (columnL1 C 0)) (Nat.cast_nonneg (columnL1 C 1))
    (Nat.cast_nonneg (columnL1 C 2)) (Nat.cast_nonneg C.det.natAbs)
    h12 h23 hb₁ (by linarith) (by linarith) hdet
  have hn : columnL1 C 0 * columnL1 C 1 * columnL1 C 2 ≤ 8 * C.det.natAbs := by
    exact_mod_cast hp
  simpa [columnL1Product, Fin.prod_univ_succ, mul_assoc] using hn

theorem columnL1Core3 (hgram : Gram3Identities) (hred : ReducedPotential3) :
    ColumnL1Core3 := by
  intro C hC
  obtain ⟨U, hU, hs, _hmin, h12, h23⟩ := hred C hC
  have hCU : (C * U).det ≠ 0 := by
    rw [Matrix.det_mul]
    rcases hU with hU | hU <;> simp [hU, hC]
  refine ⟨U, hU, ?_⟩
  have hb := reduced_columnL1Product_le (C * U) (hgram _ hCU) hs h12 h23
  have habs : (C * U).det.natAbs = C.det.natAbs := by
    rw [Matrix.det_mul, Int.natAbs_mul]
    rcases hU with hU | hU <;> simp [hU]
  simpa only [habs] using hb

def unimodularBasis {d : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin d) ℤ M) (U : ZMatrix d) (hU : Unimodular U) :
    Module.Basis (Fin d) ℤ M :=
  b.map (Matrix.toLinearEquiv b U (by
    rcases hU with hU | hU <;> simp [hU]))

theorem unimodularBasis_apply {d : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin d) ℤ M) (U : ZMatrix d) (hU : Unimodular U) (j : Fin d) :
    unimodularBasis b U hU j = ∑ k, U k j • b k := by
  rw [unimodularBasis, Module.Basis.map_apply, Matrix.toLinearEquiv_apply]
  rw [Matrix.toLin_self]
  apply Finset.sum_congr rfl
  intro k _
  exact int_smul_eq_zsmul _ _ _

theorem cast_mul_column {ι : Type*} [Fintype ι] {d : ℕ}
    (B : Matrix ι (Fin d) ℤ) (U : ZMatrix d) (j : Fin d) :
    (fun i => ((B * U) i j : ℝ)) =
      (B.map (fun z => (z : ℝ))) *ᵥ (fun k => (U k j : ℝ)) := by
  ext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem maxAbs_mul_column_le {ι : Type u} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (hpivot : PivotProjectionBound.{u}) (B : Matrix ι (Fin d) ℤ)
    (P : Fin d → ι) (hP : MaximalPivot B P) (U : ZMatrix d) (j : Fin d) :
    maxAbs (fun i => (B * U) i j) ≤ columnL1 ((B.submatrix P id) * U) j := by
  have hp := hpivot B P hP (fun k => (U k j : ℝ))
  rw [← cast_mul_column, ← cast_mul_column] at hp
  have hl : HeavyStack.l1 (fun i => (((B.submatrix P id) * U) i j : ℝ)) =
      (columnL1 ((B.submatrix P id) * U) j : ℝ) := by
    simp [HeavyStack.l1, columnL1, Nat.cast_natAbs, Int.cast_abs]
  rw [hl] at hp
  change Finset.univ.sup (fun i => ((B * U) i j).natAbs) ≤ _
  apply Finset.sup_le
  intro i _
  have hi := (norm_le_pi_norm (fun r => ((B * U) r j : ℝ)) i).trans hp
  have heq : ‖((B * U) i j : ℝ)‖ = (((B * U) i j).natAbs : ℝ) := by
    simp [Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]
  rw [heq] at hi
  exact_mod_cast hi

theorem exists_original_maximalPivot {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (L : IntLat ι d) : ∃ P, MaximalPivot L.matrix P ∧
      (L.matrix.submatrix P id).det.natAbs = L.H := by
  classical
  obtain ⟨P, hdet, hmax⟩ :=
    Algebra.VectorInverse.exists_maximal_basis_minor L.carrier L.saturated L.basis
  have hdet' : (L.matrix.submatrix P id).det ≠ 0 := hdet
  have hmax' : ∀ Q, (L.matrix.submatrix Q id).det.natAbs ≤
      (L.matrix.submatrix P id).det.natAbs := hmax
  refine ⟨P, ⟨?_, hdet', hmax'⟩, ?_⟩
  · intro i j hij
    by_contra hne
    apply hdet'
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [Matrix.submatrix, hij])
  · exact (Algebra.VectorInverse.largestMinor_eq_pivot L.matrix P hmax').symm

theorem controlledBasis3_of_core (hcore : ColumnL1Core3) (hpivot : PivotProjectionBound.{u}) :
    ControlledBasis.{u} 3 := by
  intro ι _ _ L _ _
  classical
  obtain ⟨P, hP, hH⟩ := exists_original_maximalPivot L
  obtain ⟨U, hU, hbound⟩ := hcore (L.matrix.submatrix P id) hP.2.1
  let b := unimodularBasis L.basis U hU
  have hb (j : Fin 3) : (b j : ι → ℤ) = fun i => (L.matrix * U) i j := by
    ext i
    simp [b, unimodularBasis_apply, Matrix.mul_apply, IntLat.matrix, mul_comm]
  refine ⟨b, ?_⟩
  have hprod : (∏ j, maxAbs (b j : ι → ℤ)) ≤
      columnL1Product ((L.matrix.submatrix P id) * U) := by
    apply Finset.prod_le_prod'
    intro j _
    rw [hb j]
    exact maxAbs_mul_column_le hpivot L.matrix P hP U j
  have hnat : (∏ j, maxAbs (b j : ι → ℤ)) ≤ 9 * L.H := by
    rw [hH] at hbound
    exact hprod.trans (hbound.trans (by omega))
  have hreal : (∏ j, (maxAbs (b j : ι → ℤ) : ℝ)) ≤ (9 : ℝ) * (L.H : ℝ) := by
    exact_mod_cast hnat
  simpa [J] using hreal

theorem controlledBasis3 (hgram : Gram3Identities) (hred : ReducedPotential3)
    (hpivot : PivotProjectionBound.{u}) : ControlledBasis.{u} 3 :=
  controlledBasis3_of_core (columnL1Core3 hgram hred) hpivot

end Praxis.Algebra.Basis
