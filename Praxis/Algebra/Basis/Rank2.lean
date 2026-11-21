import Praxis.Algebra.Basis.Definitions
import Praxis.Algebra.Conversion.L1Minkowski
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

noncomputable section

universe u

open Module Matrix

open scoped BigOperators

namespace Praxis.Algebra.Basis.Rank2

private def sup2 (x y : ℝ) : ℝ := max |x| |y|

private theorem square_right {a s b t : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hab : a ≤ b)
    (ht : |t| ≤ b) (hred : b ≤ max |b-a| |t-s|) : a*b ≤ |a*t-s*b| := by
  have hba : |b-a| < b := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hd : b ≤ |t-s| := (le_max_iff.mp hred).resolve_left (not_le.mpr hba)
  have htt := abs_le.mp ht
  by_cases hts : 0 ≤ t-s
  · rw [abs_of_nonneg hts] at hd
    have hs0 : s = 0 := by linarith
    have htb : t = b := by linarith
    simp only [hs0, htb, zero_mul, sub_zero]
    exact le_abs_self _
  · rw [abs_of_nonpos (le_of_not_ge hts)] at hd
    have hh : a*t-s*b ≤ -(a*b) := by
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hab)]
    exact (by linarith : a*b ≤ -(a*t-s*b)).trans (neg_le_abs _)

private theorem square_top {a s b t : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a ≤ b)
    (ht : |t| ≤ b) (hred : b ≤ max |t-a| |b-s|) : a*b ≤ |a*b-s*t| := by
  by_cases hs0 : s = 0
  · simp only [hs0, zero_mul, sub_zero]
    exact le_abs_self _
  have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hbs : |b-s| < b := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hd : b ≤ |t-a| := (le_max_iff.mp hred).resolve_right (not_le.mpr hbs)
  have htt := abs_le.mp ht
  have hta : t-a ≤ 0 := by
    by_contra h
    rw [abs_of_nonneg (le_of_not_ge h)] at hd
    linarith
  rw [abs_of_nonpos hta] at hd
  have ht0 : t ≤ 0 := by linarith
  exact (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hs ht0] : a*b ≤ a*b-s*t).trans
    (le_abs_self _)

private theorem square_normalized {a s z w : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a ≤ sup2 z w)
    (hp : sup2 z w ≤ sup2 (z+a) (w+s))
    (hm : sup2 z w ≤ sup2 (z-a) (w-s)) : a * sup2 z w ≤ |a*w-s*z| := by
  rcases le_total |w| |z| with hz | hw
  · have he : sup2 z w = |z| := max_eq_left hz
    rw [he] at hab hp hm ⊢
    by_cases hz0 : 0 ≤ z
    · rw [abs_of_nonneg hz0] at hab hp hm ⊢
      exact square_right ha hs hab (hz.trans_eq (abs_of_nonneg hz0)) hm
    · have hz0 := le_of_not_ge hz0
      have h := square_right (a := a) (s := s) (b := -z) (t := -w)
        ha hs (by simpa [abs_of_nonpos hz0] using hab)
        (by simpa [abs_of_nonpos hz0] using hz)
        (by simpa only [sup2, abs_of_nonpos hz0, neg_sub_left, abs_neg, add_comm] using hp)
      have hd : a * -w - s * -z = -(a*w-s*z) := by ring
      rw [hd, abs_neg] at h
      simpa only [abs_of_nonpos hz0] using h
  · have he : sup2 z w = |w| := max_eq_right hw
    rw [he] at hab hp hm ⊢
    by_cases hw0 : 0 ≤ w
    · rw [abs_of_nonneg hw0] at hab hp hm ⊢
      exact square_top ha hs hsa hab (hw.trans_eq (abs_of_nonneg hw0)) hm
    · have hw0 := le_of_not_ge hw0
      have h := square_top (a := a) (s := s) (b := -w) (t := -z)
        ha hs hsa (by simpa [abs_of_nonpos hw0] using hab)
        (by simpa [abs_of_nonpos hw0] using hw)
        (by simpa only [sup2, abs_of_nonpos hw0, neg_sub_left, abs_neg, add_comm] using hp)
      have hd : a * -w - s * -z = -(a*w-s*z) := by ring
      rw [hd, abs_neg] at h
      simpa only [abs_of_nonpos hw0] using h

private theorem square_active {x y z w : ℝ}
    (hxy : |y| ≤ |x|) (hx : 0 < |x|) (hab : |x| ≤ sup2 z w)
    (hp : sup2 z w ≤ sup2 (z+x) (w+y))
    (hm : sup2 z w ≤ sup2 (z-x) (w-y)) : |x| * sup2 z w ≤ |x*w-y*z| := by
  have first : ∀ a s z w : ℝ, 0 < a → |s| ≤ a → a ≤ sup2 z w →
      sup2 z w ≤ sup2 (z+a) (w+s) → sup2 z w ≤ sup2 (z-a) (w-s) →
      a * sup2 z w ≤ |a*w-s*z| := by
    intro a s z w ha hs hab hp hm
    by_cases hs0 : 0 ≤ s
    · exact square_normalized ha hs0 ((abs_of_nonneg hs0) ▸ hs) hab hp hm
    · have hs0 := le_of_not_ge hs0
      have h := square_normalized (a := a) (s := -s) (z := z) (w := -w)
        ha (neg_nonneg.mpr hs0) (by simpa [abs_of_nonpos hs0] using hs)
        (by simpa [sup2] using hab)
        (by simpa only [sup2, ← neg_add, abs_neg] using hp)
        (by simpa only [sup2, neg_sub_neg, neg_add_eq_sub, abs_sub_comm, abs_neg] using hm)
      have hd : a * -w - -s * z = -(a*w-s*z) := by ring
      rw [hd, abs_neg] at h
      simpa only [sup2, abs_neg] using h
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0] at hxy hx hab ⊢
    exact first x y z w hx hxy hab hp hm
  · have hx0 := le_of_not_ge hx0
    have h := first (-x) y (-z) w
      (by simpa [abs_of_nonpos hx0] using hx)
      (by simpa [abs_of_nonpos hx0] using hxy)
      (by simpa [sup2, abs_of_nonpos hx0] using hab)
      (by simpa only [sup2, ← neg_add, abs_neg] using hp)
      (by simpa only [sup2, neg_sub_neg, neg_add_eq_sub, abs_sub_comm, abs_neg] using hm)
    have hd : -x * w - y * -z = -(x*w-y*z) := by ring
    rw [hd, abs_neg] at h
    simpa only [sup2, abs_neg, abs_of_nonpos hx0] using h

private theorem square_bound {x y z w : ℝ}
    (hu : 0 < sup2 x y) (hab : sup2 x y ≤ sup2 z w)
    (hp : sup2 z w ≤ sup2 (z+x) (w+y))
    (hm : sup2 z w ≤ sup2 (z-x) (w-y)) : sup2 x y * sup2 z w ≤ |x*w-y*z| := by
  rcases le_total |y| |x| with hxy | hyx
  · have he : sup2 x y = |x| := max_eq_left hxy
    exact he ▸ square_active hxy (he ▸ hu) (he ▸ hab) hp hm
  · have he : sup2 x y = |y| := max_eq_right hyx
    rw [he] at hu hab ⊢
    have h := square_active (x := y) (y := x) (z := w) (w := z)
      hyx hu (by simpa [sup2, max_comm] using hab)
      (by simpa [sup2, max_comm] using hp) (by simpa [sup2, max_comm] using hm)
    simpa only [sup2, max_comm, abs_sub_comm] using h

private theorem diamond_square (x y : ℝ) : sup2 (x+y) (x-y) = |x|+|y| := by
  simp only [sup2, abs_eq_max_neg, max_def]
  split_ifs <;> linarith

theorem planar_reduced {a b c d : ℝ}
    (hu : 0 < |a|+|b|) (hab : |a|+|b| ≤ |c|+|d|)
    (hp : |c|+|d| ≤ |c+a|+|d+b|)
    (hm : |c|+|d| ≤ |c-a|+|d-b|) :
    (|a|+|b|) * (|c|+|d|) ≤ 2 * |a*d-b*c| := by
  have h := square_bound (x := a+b) (y := a-b) (z := c+d) (w := c-d)
    (by simpa [diamond_square] using hu) (by simpa [diamond_square] using hab)
    (by
      rw [show c+d+(a+b) = (c+a)+(d+b) by ring,
        show c-d+(a-b) = (c+a)-(d+b) by ring, diamond_square, diamond_square]
      exact hp)
    (by
      rw [show c+d-(a+b) = (c-a)+(d-b) by ring,
        show c-d-(a-b) = (c-a)-(d-b) by ring, diamond_square, diamond_square]
      exact hm)
  rw [diamond_square, diamond_square] at h
  have he : (a+b)*(c-d)-(a-b)*(c+d) = -(2*(a*d-b*c)) := by ring
  simpa [he, abs_mul] using h

def columnL1 (C : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin 2) : ℕ :=
  (C 0 j).natAbs + (C 1 j).natAbs

private theorem columnL1_cast (C : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin 2) :
    (columnL1 C j : ℝ) = |(C 0 j : ℝ)| + |(C 1 j : ℝ)| := by
  simp [columnL1]

private theorem columnL1_pos (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0)
    (j : Fin 2) : 0 < columnL1 C j := by
  by_contra hn
  have hz : columnL1 C j = 0 := Nat.eq_zero_of_not_pos hn
  obtain ⟨h0, h1⟩ := Nat.add_eq_zero_iff.mp hz
  have h0 := Int.natAbs_eq_zero.mp h0
  have h1 := Int.natAbs_eq_zero.mp h1
  apply hC
  fin_cases j <;> dsimp at h0 h1 <;> simp [Matrix.det_fin_two, h0, h1]

private def shear (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, k; 0, 1]

private def lowerShear (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; k, 1]

private theorem shear_det (k : ℤ) : (shear k).det = 1 := by
  simp [shear, Matrix.det_fin_two]

private theorem lowerShear_det (k : ℤ) : (lowerShear k).det = 1 := by
  simp [lowerShear, Matrix.det_fin_two]

private theorem mul_shear (M : Matrix (Fin 2) (Fin 2) ℤ) (k : ℤ) :
    M*shear k = !![M 0 0, M 0 1+k*M 0 0; M 1 0, M 1 1+k*M 1 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem mul_lowerShear (M : Matrix (Fin 2) (Fin 2) ℤ) (k : ℤ) :
    M*lowerShear k = !![M 0 0+k*M 0 1, M 0 1; M 1 0+k*M 1 1, M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShear, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem column_l1_core (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧
      columnL1 (C*U) 0 * columnL1 (C*U) 1 ≤ 2 * C.det.natAbs := by
  classical
  let T := {U : Matrix (Fin 2) (Fin 2) ℤ // IsUnit U.det}
  let : Nonempty T := ⟨⟨1, by simp⟩⟩
  let f : T → ℕ := fun U => columnL1 (C*U.val) 0 * columnL1 (C*U.val) 1
  let U : T := Function.argmin f
  let M := C*U.val
  have hM : M.det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hC U.property.ne_zero
  have h0 := columnL1_pos M hM 0
  have h1 := columnL1_pos M hM 1
  have hmin (V : Matrix (Fin 2) (Fin 2) ℤ) (hV : IsUnit V.det) :
      columnL1 M 0 * columnL1 M 1 ≤ columnL1 (M*V) 0 * columnL1 (M*V) 1 := by
    have hUV : IsUnit (U.val*V).det := by
      rw [Matrix.det_mul]
      exact U.property.mul hV
    simpa only [f, M, Matrix.mul_assoc] using Function.argmin_le f (⟨U.val*V, hUV⟩ : T)
  have right (k : ℤ) : columnL1 M 1 ≤
      (M 0 1 + k*M 0 0).natAbs + (M 1 1 + k*M 1 0).natAbs := by
    have h := hmin (shear k) (by rw [shear_det]; exact isUnit_one)
    have he0 : columnL1 (M*shear k) 0 = columnL1 M 0 := by
      simp [columnL1, mul_shear]
    have he1 : columnL1 (M*shear k) 1 =
        (M 0 1 + k*M 0 0).natAbs + (M 1 1 + k*M 1 0).natAbs := by
      simp [columnL1, mul_shear]
    rw [he0, he1] at h
    nlinarith
  have left (k : ℤ) : columnL1 M 0 ≤
      (M 0 0 + k*M 0 1).natAbs + (M 1 0 + k*M 1 1).natAbs := by
    have h := hmin (lowerShear k) (by rw [lowerShear_det]; exact isUnit_one)
    have he1 : columnL1 (M*lowerShear k) 1 = columnL1 M 1 := by
      simp [columnL1, mul_lowerShear]
    have he0 : columnL1 (M*lowerShear k) 0 =
        (M 0 0 + k*M 0 1).natAbs + (M 1 0 + k*M 1 1).natAbs := by
      simp [columnL1, mul_lowerShear]
    rw [he0, he1] at h
    nlinarith
  have real_right (k : ℤ) :
      |(M 0 1 : ℝ)| + |(M 1 1 : ℝ)| ≤
        |(M 0 1 : ℝ) + (k : ℝ)*(M 0 0 : ℝ)| +
        |(M 1 1 : ℝ) + (k : ℝ)*(M 1 0 : ℝ)| := by
    have h := right k
    have hz : (columnL1 M 1 : ℤ) ≤
        ((M 0 1 + k*M 0 0).natAbs : ℤ) + ((M 1 1 + k*M 1 0).natAbs : ℤ) := by
      exact_mod_cast h
    simp only [columnL1, Nat.cast_add, Int.natCast_natAbs] at hz
    exact_mod_cast hz
  have real_left (k : ℤ) :
      |(M 0 0 : ℝ)| + |(M 1 0 : ℝ)| ≤
        |(M 0 0 : ℝ) + (k : ℝ)*(M 0 1 : ℝ)| +
        |(M 1 0 : ℝ) + (k : ℝ)*(M 1 1 : ℝ)| := by
    have h := left k
    have hz : (columnL1 M 0 : ℤ) ≤
        ((M 0 0 + k*M 0 1).natAbs : ℤ) + ((M 1 0 + k*M 1 1).natAbs : ℤ) := by
      exact_mod_cast h
    simp only [columnL1, Nat.cast_add, Int.natCast_natAbs] at hz
    exact_mod_cast hz
  have bound : (columnL1 M 0 : ℝ) * (columnL1 M 1 : ℝ) ≤ 2*|(M.det : ℝ)| := by
    rcases le_total (columnL1 M 0) (columnL1 M 1) with hab | hab
    · have hp := real_right 1
      have hm := real_right (-1)
      have hu : 0 < |(M 0 0 : ℝ)| + |(M 1 0 : ℝ)| := by
        rw [← columnL1_cast]; exact_mod_cast h0
      have hab' : |(M 0 0 : ℝ)| + |(M 1 0 : ℝ)| ≤
          |(M 0 1 : ℝ)| + |(M 1 1 : ℝ)| := by
        rw [← columnL1_cast, ← columnL1_cast]; exact_mod_cast hab
      have hh := planar_reduced hu hab'
        (by simpa using hp) (by simpa [sub_eq_add_neg] using hm)
      have hd : (M.det : ℝ) =
          (M 0 0 : ℝ)*(M 1 1 : ℝ)-(M 1 0 : ℝ)*(M 0 1 : ℝ) := by
        simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul]
        ring
      rw [columnL1_cast, columnL1_cast, hd]
      exact hh
    · have hp := real_left 1
      have hm := real_left (-1)
      have hu : 0 < |(M 0 1 : ℝ)| + |(M 1 1 : ℝ)| := by
        rw [← columnL1_cast]; exact_mod_cast h1
      have hab' : |(M 0 1 : ℝ)| + |(M 1 1 : ℝ)| ≤
          |(M 0 0 : ℝ)| + |(M 1 0 : ℝ)| := by
        rw [← columnL1_cast, ← columnL1_cast]; exact_mod_cast hab
      have hh := planar_reduced hu hab'
        (by simpa using hp) (by simpa [sub_eq_add_neg] using hm)
      have hd : (M 0 1 : ℝ)*(M 1 0 : ℝ)-(M 1 1 : ℝ)*(M 0 0 : ℝ) =
          -((M 0 0 : ℝ)*(M 1 1 : ℝ)-(M 0 1 : ℝ)*(M 1 0 : ℝ)) := by ring
      rw [hd, abs_neg] at hh
      rw [columnL1_cast, columnL1_cast, mul_comm]
      simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul] using hh
  have hd : M.det.natAbs = C.det.natAbs := by
    simp only [M, Matrix.det_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.mp U.property,
      mul_one]
  refine ⟨U.val, U.property, ?_⟩
  rw [← hd]
  apply (Nat.cast_le (α := ℝ)).mp
  simpa using bound

open Praxis.Algebra.Inverse.Definitions

private theorem maxAbs_le_norm {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℤ) : (maxAbs w : ℝ) ≤ ‖fun i => (w i : ℝ)‖ := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => (w i).natAbs) Finset.univ_nonempty
  have he : maxAbs w = (w i).natAbs := by
    apply le_antisymm
    · exact Finset.sup_le fun j _ => hi j (Finset.mem_univ j)
    · exact Finset.le_sup (f := fun j => (w j).natAbs) (Finset.mem_univ i)
  rw [he]
  simpa using norm_le_pi_norm (fun i => (w i : ℝ)) i

theorem controlledBasis2_of_pivot (hpivot : PivotProjectionBound.{u}) : ControlledBasis.{u} 2 := by
  classical
  intro ι _ _ L _ _
  obtain ⟨P, hdet, hmax⟩ := Algebra.VectorInverse.exists_maximal_basis_minor
    L.carrier L.saturated L.basis
  change (L.matrix.submatrix P id).det ≠ 0 at hdet
  change ∀ Q, (L.matrix.submatrix Q id).det.natAbs ≤
    (L.matrix.submatrix P id).det.natAbs at hmax
  have hP : MaximalPivot L.matrix P := by
    refine ⟨?_, hdet, hmax⟩
    intro i j hij
    by_contra hne
    exact hdet (Matrix.det_zero_of_row_eq hne (by
      funext k
      change L.matrix (P i) k = L.matrix (P j) k
      rw [hij]))
  let C := L.matrix.submatrix P id
  obtain ⟨U, hU, hbound⟩ := column_l1_core C hdet
  let e := Matrix.toLinearEquiv L.basis U hU
  let b := L.basis.map e
  have hb (i : ι) (j : Fin 2) : (b j : ι → ℤ) i = (L.matrix*U) i j := by
    change ((Matrix.toLinearEquiv L.basis U hU) (L.basis j) : ι → ℤ) i = _
    rw [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mul_apply, IntLat.matrix]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  let : Nonempty ι := ⟨P 0⟩
  have hn (j : Fin 2) : (maxAbs (b j : ι → ℤ) : ℝ) ≤ (columnL1 (C*U) j : ℝ) := by
    let y : Fin 2 → ℝ := fun k => (U k j : ℝ)
    have h := hpivot L.matrix P hP y
    have hamb : (L.matrix.map (fun z => (z : ℝ))) *ᵥ y =
        fun i => ((b j : ι → ℤ) i : ℝ) := by
      ext i
      rw [hb]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, y]
    have hproj : (C.map (fun z => (z : ℝ))) *ᵥ y =
        fun i => ((C*U) i j : ℝ) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, y]
    change ‖(L.matrix.map (fun z => (z : ℝ))) *ᵥ y‖ ≤
      HeavyStack.l1 ((C.map (fun z => (z : ℝ))) *ᵥ y) at h
    rw [hamb, hproj] at h
    have hl : HeavyStack.l1 (fun i => ((C*U) i j : ℝ)) = (columnL1 (C*U) j : ℝ) := by
      simp [HeavyStack.l1, Fin.sum_univ_two, columnL1_cast]
    rw [hl] at h
    exact (maxAbs_le_norm _).trans h
  have height_eq : L.H = C.det.natAbs :=
    Algebra.VectorInverse.largestMinor_eq_pivot L.matrix P hmax
  refine ⟨b, ?_⟩
  have hprod := mul_le_mul (hn 0) (hn 1) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hc : (columnL1 (C*U) 0 : ℝ) * (columnL1 (C*U) 1 : ℝ) ≤
      2*(C.det.natAbs : ℝ) := by exact_mod_cast hbound
  simpa [Fin.prod_univ_two, J, height_eq] using hprod.trans hc

end Praxis.Algebra.Basis.Rank2
