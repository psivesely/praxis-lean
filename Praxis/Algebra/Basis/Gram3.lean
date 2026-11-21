import Praxis.Algebra.Basis.ElementaryModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Praxis.Algebra.Basis.Gram3

open Praxis.Algebra.Basis.ElementaryModel

lemma dot_symm (x y : Fin 3 → ℚ) : dotQ x y = dotQ y x := by
  unfold dotQ
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma dot_sub_left (x y z : Fin 3 → ℚ) :
    dotQ (fun i => x i - y i) z = dotQ x z - dotQ y z := by
  simp [dotQ, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (a : ℚ) (x y : Fin 3 → ℚ) :
    dotQ (fun i => a * x i) y = a * dotQ x y := by
  simp [dotQ, mul_assoc, Finset.mul_sum]

lemma dot_sub_right (x y z : Fin 3 → ℚ) :
    dotQ x (fun i => y i - z i) = dotQ x y - dotQ x z := by
  rw [dot_symm, dot_sub_left, dot_symm y x, dot_symm z x]

lemma dot_smul_right (a : ℚ) (x y : Fin 3 → ℚ) :
    dotQ x (fun i => a * y i) = a * dotQ x y := by
  rw [dot_symm, dot_smul_left, dot_symm]

lemma dot_nonneg (x : Fin 3 → ℚ) : 0 ≤ dotQ x x := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma D1_formula (C : ZMatrix 3) :
    D1 C = C 0 0 ^ 2 + C 1 0 ^ 2 + C 2 0 ^ 2 := by
  unfold D1 prefixGram
  erw [Matrix.det_fin_one]
  simp [Fin.sum_univ_three]
  ring

lemma D2_formula (C : ZMatrix 3) :
    D2 C =
      (C 0 0 ^ 2 + C 1 0 ^ 2 + C 2 0 ^ 2) *
        (C 0 1 ^ 2 + C 1 1 ^ 2 + C 2 1 ^ 2) -
      (C 0 0 * C 0 1 + C 1 0 * C 1 1 + C 2 0 * C 2 1) ^ 2 := by
  unfold D2 prefixGram
  erw [Matrix.det_fin_two]
  simp [Fin.sum_univ_three]
  ring

lemma minors (C : ZMatrix 3) :
    D2 C = (C 0 0 * C 1 1 - C 1 0 * C 0 1) ^ 2 +
      (C 0 0 * C 2 1 - C 2 0 * C 0 1) ^ 2 +
      (C 1 0 * C 2 1 - C 2 0 * C 1 1) ^ 2 := by
  rw [D2_formula]
  ring

lemma D1_cast (C : ZMatrix 3) : (D1 C : ℚ) = t1 C := by
  rw [D1_formula]
  simp [t1, dotQ, q1, columnQ, Fin.sum_univ_three]
  ring

lemma D2_cast (C : ZMatrix 3) :
    (D2 C : ℚ) = t1 C * dotQ (columnQ C 1) (columnQ C 1) -
      dotQ (columnQ C 1) (q1 C) ^ 2 := by
  rw [D2_formula]
  push_cast
  simp [t1, dotQ, q1, columnQ, Fin.sum_univ_three]
  ring

lemma D1_pos (C : ZMatrix 3) (hC : C.det ≠ 0) : 0 < D1 C := by
  rw [D1_formula]
  have h0 := sq_nonneg (C 0 0)
  have h1 := sq_nonneg (C 1 0)
  have h2 := sq_nonneg (C 2 0)
  by_contra h
  have ha : C 0 0 = 0 := by nlinarith
  have hb : C 1 0 = 0 := by nlinarith
  have hc : C 2 0 = 0 := by nlinarith
  apply hC
  simp [Matrix.det_fin_three, ha, hb, hc]

lemma D2_pos (C : ZMatrix 3) (hC : C.det ≠ 0) : 0 < D2 C := by
  rw [minors]
  have h0 := sq_nonneg (C 0 0 * C 1 1 - C 1 0 * C 0 1)
  have h1 := sq_nonneg (C 0 0 * C 2 1 - C 2 0 * C 0 1)
  have h2 := sq_nonneg (C 1 0 * C 2 1 - C 2 0 * C 1 1)
  by_contra h
  have ha : C 0 0 * C 1 1 - C 1 0 * C 0 1 = 0 := by nlinarith
  have hb : C 0 0 * C 2 1 - C 2 0 * C 0 1 = 0 := by nlinarith
  have hc : C 1 0 * C 2 1 - C 2 0 * C 1 1 = 0 := by nlinarith
  apply hC
  rw [Matrix.det_fin_three]
  linear_combination C 2 2 * ha - C 1 2 * hb + C 0 2 * hc

lemma m21_mul (C : ZMatrix 3) (h1 : t1 C ≠ 0) :
    m21 C * t1 C = dotQ (columnQ C 1) (q1 C) := by
  exact div_mul_cancel₀ _ h1

lemma m31_mul (C : ZMatrix 3) (h1 : t1 C ≠ 0) :
    m31 C * t1 C = dotQ (columnQ C 2) (q1 C) := by
  exact div_mul_cancel₀ _ h1

lemma m32_mul (C : ZMatrix 3) (h2 : t2 C ≠ 0) :
    m32 C * t2 C = dotQ (columnQ C 2) (q2 C) := by
  exact div_mul_cancel₀ _ h2

lemma orth12 (C : ZMatrix 3) (h1 : t1 C ≠ 0) :
    dotQ (q1 C) (q2 C) = 0 := by
  unfold q2
  rw [dot_sub_right, dot_smul_right, ← t1, dot_symm (q1 C), ← m21_mul C h1]
  ring

lemma x2_q2 (C : ZMatrix 3) (h1 : t1 C ≠ 0) :
    dotQ (columnQ C 1) (q2 C) = t2 C := by
  unfold t2
  conv_rhs => lhs; unfold q2
  rw [dot_sub_left, dot_smul_left, orth12 C h1]
  ring

lemma prefix_values (C : ZMatrix 3) (h1 : t1 C ≠ 0) :
    (D1 C : ℚ) = t1 C ∧ (D2 C : ℚ) = t1 C * t2 C := by
  refine ⟨D1_cast C, ?_⟩
  rw [D2_cast]
  have hm := m21_mul C h1
  have ht : t2 C = dotQ (columnQ C 1) (columnQ C 1) - m21 C ^ 2 * t1 C := by
    unfold t2
    unfold q2
    rw [dot_sub_left, dot_smul_left, dot_sub_right, dot_smul_right,
      dot_sub_right, dot_smul_right, ← t1, dot_symm (q1 C)]
    linear_combination 2 * m21 C * hm
  rw [ht, ← hm]
  ring

lemma orthogonal (C : ZMatrix 3) (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    dotQ (q1 C) (q2 C) = 0 ∧ dotQ (q1 C) (q3 C) = 0 ∧
    dotQ (q2 C) (q3 C) = 0 := by
  have ho := orth12 C h1
  refine ⟨ho, ?_, ?_⟩
  · unfold q3
    rw [dot_sub_right, dot_sub_right, dot_smul_right, dot_smul_right,
      ho, ← t1, dot_symm (q1 C), ← m31_mul C h1]
    ring
  · unfold q3
    rw [dot_sub_right, dot_sub_right, dot_smul_right, dot_smul_right,
      dot_symm (q2 C) (q1 C), ho, ← t2, dot_symm (q2 C), ← m32_mul C h2]
    ring

lemma orthogonal_det (C : ZMatrix 3) :
    (orthogonalMatrix C).det = (C.det : ℚ) := by
  simp [orthogonalMatrix, Matrix.det_fin_three, q3, q2, q1, columnQ]
  ring

lemma gram_det (Q : Matrix (Fin 3) (Fin 3) ℚ)
    (h01 : dotQ (fun i => Q i 0) (fun i => Q i 1) = 0)
    (h02 : dotQ (fun i => Q i 0) (fun i => Q i 2) = 0)
    (h12 : dotQ (fun i => Q i 1) (fun i => Q i 2) = 0) :
    dotQ (fun i => Q i 0) (fun i => Q i 0) *
      dotQ (fun i => Q i 1) (fun i => Q i 1) *
      dotQ (fun i => Q i 2) (fun i => Q i 2) = Q.det ^ 2 := by
  simp only [dotQ, Fin.sum_univ_three] at *
  rw [Matrix.det_fin_three]
  linear_combination
    (Q 0 0 * Q 0 1 + Q 1 0 * Q 1 1 + Q 2 0 * Q 2 1) *
      (Q 0 2 ^ 2 + Q 1 2 ^ 2 + Q 2 2 ^ 2) * h01 +
    (Q 0 0 * Q 0 2 + Q 1 0 * Q 1 2 + Q 2 0 * Q 2 2) *
      (Q 0 1 ^ 2 + Q 1 1 ^ 2 + Q 2 1 ^ 2) * h02 +
    ((Q 0 1 * Q 0 2 + Q 1 1 * Q 1 2 + Q 2 1 * Q 2 2) *
      (Q 0 0 ^ 2 + Q 1 0 ^ 2 + Q 2 0 ^ 2) -
      2 * (Q 0 0 * Q 0 1 + Q 1 0 * Q 1 1 + Q 2 0 * Q 2 1) *
        (Q 0 0 * Q 0 2 + Q 1 0 * Q 1 2 + Q 2 0 * Q 2 2)) * h12

lemma determinant (C : ZMatrix 3) (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    t1 C * t2 C * t3 C = (C.det : ℚ) ^ 2 := by
  obtain ⟨h12, h13, h23⟩ := orthogonal C h1 h2
  have hg := gram_det (orthogonalMatrix C)
    (by simpa [orthogonalMatrix] using h12)
    (by simpa [orthogonalMatrix] using h13)
    (by simpa [orthogonalMatrix] using h23)
  change t1 C * t2 C * t3 C = (orthogonalMatrix C).det ^ 2 at hg
  rw [orthogonal_det] at hg
  exact hg

lemma positive (C : ZMatrix 3) (hC : C.det ≠ 0) :
    0 < D1 C ∧ 0 < D2 C ∧ 0 < t1 C ∧ 0 < t2 C ∧ 0 < t3 C := by
  have hd1 := D1_pos C hC
  have hd2 := D2_pos C hC
  have ht1 : 0 < t1 C := by rw [← D1_cast]; exact_mod_cast hd1
  have hp := (prefix_values C (ne_of_gt ht1)).2
  have hd2q : (0 : ℚ) < D2 C := by exact_mod_cast hd2
  have ht2 : 0 < t2 C := by nlinarith
  have hdet := determinant C (ne_of_gt ht1) (ne_of_gt ht2)
  have hdetq : (C.det : ℚ) ≠ 0 := by exact_mod_cast hC
  have ht3 : 0 < t3 C := by
    have hs := sq_pos_of_ne_zero hdetq
    have hn := dot_nonneg (q3 C)
    change 0 ≤ t3 C at hn
    by_contra h
    have hz : t3 C = 0 := le_antisymm (le_of_not_gt h) hn
    rw [hz] at hdet
    nlinarith
  exact ⟨hd1, hd2, ht1, ht2, ht3⟩

lemma norms (C : ZMatrix 3) (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    dotQ (columnQ C 0) (columnQ C 0) = t1 C ∧
    dotQ (columnQ C 1) (columnQ C 1) = t2 C + m21 C ^ 2 * t1 C ∧
    dotQ (columnQ C 2) (columnQ C 2) =
      t3 C + m32 C ^ 2 * t2 C + m31 C ^ 2 * t1 C := by
  refine ⟨rfl, ?_, ?_⟩
  · have hm := m21_mul C h1
    have he : t2 C = dotQ (q2 C) (q2 C) := rfl
    unfold q2 at he
    simp only [dot_sub_left, dot_smul_left, dot_sub_right, dot_smul_right] at he
    rw [dot_symm (q1 C)] at he
    change t2 C = dotQ (columnQ C 1) (columnQ C 1) -
      m21 C * dotQ (columnQ C 1) (q1 C) -
      m21 C * (dotQ (columnQ C 1) (q1 C) - m21 C * t1 C) at he
    linear_combination -he - 2 * m21 C * hm
  · have hm1 := m31_mul C h1
    have hm2 := m32_mul C h2
    have ho := orth12 C h1
    have he : t3 C = dotQ (q3 C) (q3 C) := rfl
    unfold q3 at he
    simp only [dot_sub_left, dot_smul_left, dot_sub_right, dot_smul_right] at he
    rw [dot_symm (q1 C) (columnQ C 2), dot_symm (q2 C) (columnQ C 2),
      dot_symm (q2 C) (q1 C), ho] at he
    change t3 C = dotQ (columnQ C 2) (columnQ C 2) -
      m31 C * dotQ (columnQ C 2) (q1 C) -
      m32 C * dotQ (columnQ C 2) (q2 C) -
      m31 C * (dotQ (columnQ C 2) (q1 C) - m31 C * t1 C - m32 C * 0) -
      m32 C * (dotQ (columnQ C 2) (q2 C) - m31 C * 0 - m32 C * t2 C) at he
    linear_combination -he - 2 * m31 C * hm1 - 2 * m32 C * hm2

structure UpperFacts (C B : ZMatrix 3) (a b c : ℚ) : Prop where
  det : B.det = C.det
  first : D1 B = D1 C
  second : D2 B = D2 C
  pot : potential B = potential C
  one : q1 B = q1 C
  two : q2 B = q2 C
  three : q3 B = q3 C
  coeff21 : m21 B = m21 C - a
  coeff31 : m31 B = m31 C - b - c * m21 C
  coeff32 : m32 B = m32 C - c

lemma upper_facts (C B : ZMatrix 3) (a b c : ℚ)
    (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0)
    (hb0 : columnQ B 0 = columnQ C 0)
    (hb1 : columnQ B 1 = fun i => columnQ C 1 i - a * q1 C i)
    (hb2 : columnQ B 2 = fun i => columnQ C 2 i - b * q1 C i - c * columnQ C 1 i) :
    UpperFacts C B a b c := by
  have hq1 : q1 B = q1 C := hb0
  have ht1 : t1 B = t1 C := by simp only [t1, hq1]
  have hm21 : m21 B = m21 C - a := by
    rw [m21, hb1, hq1, ht1, dot_sub_left, dot_smul_left, ← t1]
    unfold m21
    field_simp [h1]
  have hq2 : q2 B = q2 C := by
    funext i
    simp only [q2, hb1, hm21, hq1]
    ring
  have ht2 : t2 B = t2 C := by simp only [t2, hq2]
  have hm31 : m31 B = m31 C - b - c * m21 C := by
    rw [m31, hb2, hq1, ht1, dot_sub_left, dot_sub_left,
      dot_smul_left, dot_smul_left, ← t1]
    unfold m31 m21
    field_simp [h1]
  have hm32 : m32 B = m32 C - c := by
    rw [m32, hb2, hq2, ht2, dot_sub_left, dot_sub_left,
      dot_smul_left, dot_smul_left, orth12 C h1, x2_q2 C h1]
    unfold m32
    field_simp [h2]
    ring
  have hq3 : q3 B = q3 C := by
    funext i
    simp only [q3, hb2, hm31, hm32, hq1, hq2]
    simp only [q2]
    ring
  have hd1 : D1 B = D1 C := by
    have he : (D1 B : ℚ) = D1 C := by rw [D1_cast, D1_cast, ht1]
    exact_mod_cast he
  have hd2 : D2 B = D2 C := by
    have he : (D2 B : ℚ) = D2 C := by
      rw [(prefix_values B (by simpa [ht1] using h1)).2,
        (prefix_values C h1).2, ht1, ht2]
    exact_mod_cast he
  have hdet : B.det = C.det := by
    have hQ : orthogonalMatrix B = orthogonalMatrix C := by
      funext i j
      simp only [orthogonalMatrix, hq1, hq2, hq3]
    have he : (B.det : ℚ) = C.det := by
      rw [← orthogonal_det B, ← orthogonal_det C, hQ]
    exact_mod_cast he
  exact ⟨hdet, hd1, hd2, by simp [potential, hd1, hd2], hq1, hq2, hq3,
    hm21, hm31, hm32⟩

lemma shear_det (i j : Fin 3) (k : ℤ) (h : i ≠ j) :
    (shear i j k).det = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [shear, Matrix.det_fin_three]

lemma shear_column (C : ZMatrix 3) (i j s : Fin 3) (k : ℤ) :
    columnQ (C * shear i j k) s =
      fun r => columnQ C s r - if s = j then (k : ℚ) * columnQ C i r else 0 := by
  funext r
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp [columnQ, Matrix.mul_apply, shear, Fin.sum_univ_three] <;> ring

lemma swap_column (C : ZMatrix 3) (i j s : Fin 3) :
    columnQ (C * swapChange i j) s = columnQ C ((Equiv.swap i j) s) := by
  funext r
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp [columnQ, Matrix.mul_apply, swapChange, Equiv.swap_apply_def]

lemma shear21_facts (C : ZMatrix 3) (k : ℤ)
    (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    UpperFacts C (C * shear 0 1 k) k 0 0 := by
  apply upper_facts C _ _ _ _ h1 h2
  · simpa using shear_column C 0 1 0 k
  · simpa [q1] using shear_column C 0 1 1 k
  · simpa using shear_column C 0 1 2 k

lemma shear32_facts (C : ZMatrix 3) (k : ℤ)
    (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    UpperFacts C (C * shear 1 2 k) 0 0 k := by
  apply upper_facts C _ _ _ _ h1 h2
  · simpa using shear_column C 1 2 0 k
  · simpa using shear_column C 1 2 1 k
  · simpa using shear_column C 1 2 2 k

lemma shear31_facts (C : ZMatrix 3) (k : ℤ)
    (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    UpperFacts C (C * shear 0 2 k) 0 k 0 := by
  apply upper_facts C _ _ _ _ h1 h2
  · simpa using shear_column C 0 2 0 k
  · simpa using shear_column C 0 2 1 k
  · simpa [q1] using shear_column C 0 2 2 k

lemma swap12_det : (swapChange (0 : Fin 3) 1).det = -1 := by
  simp [swapChange, Matrix.det_fin_three, Equiv.swap_apply_def]

lemma swap23_det : (swapChange (1 : Fin 3) 2).det = -1 := by
  simp [swapChange, Matrix.det_fin_three, Equiv.swap_apply_def]

lemma swap12_facts (C : ZMatrix 3) (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    let B := C * swapChange 0 1
    B.det = -C.det ∧ D2 B = D2 C ∧
      (D1 B : ℚ) = t2 C + m21 C ^ 2 * t1 C := by
  dsimp only
  have hb0 : columnQ (C * swapChange 0 1) 0 = columnQ C 1 := by
    simpa using swap_column C 0 1 0
  have hb1 : columnQ (C * swapChange 0 1) 1 = columnQ C 0 := by
    simpa using swap_column C 0 1 1
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, swap12_det]
    ring
  · have he : (D2 (C * swapChange 0 1) : ℚ) = D2 C := by
      rw [D2_cast, D2_cast]
      simp only [t1, q1, hb0, hb1]
      rw [dot_symm (columnQ C 0) (columnQ C 1)]
      ring
    exact_mod_cast he
  · rw [D1_cast]
    change dotQ (columnQ (C * swapChange 0 1) 0)
      (columnQ (C * swapChange 0 1) 0) = _
    rw [hb0]
    exact (norms C h1 h2).2.1

lemma swap23_facts (C : ZMatrix 3) (h1 : t1 C ≠ 0) (h2 : t2 C ≠ 0) :
    let B := C * swapChange 1 2
    B.det = -C.det ∧ D1 B = D1 C ∧
      (D2 B : ℚ) = t1 C * (t3 C + m32 C ^ 2 * t2 C) := by
  dsimp only
  have hb0 : columnQ (C * swapChange 1 2) 0 = columnQ C 0 := by
    simpa [Equiv.swap_apply_def] using swap_column C 1 2 0
  have hb1 : columnQ (C * swapChange 1 2) 1 = columnQ C 2 := by
    simpa using swap_column C 1 2 1
  have hq1 : q1 (C * swapChange 1 2) = q1 C := hb0
  have ht1 : t1 (C * swapChange 1 2) = t1 C := by simp only [t1, hq1]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, swap23_det]
    ring
  · have he : (D1 (C * swapChange 1 2) : ℚ) = D1 C := by
      rw [D1_cast, D1_cast, ht1]
    exact_mod_cast he
  · rw [D2_cast, ht1, hq1, hb1, (norms C h1 h2).2.2, ← m31_mul C h1]
    ring

lemma potential_cast (C : ZMatrix 3) (hC : C.det ≠ 0) :
    (potential C : ℚ) = t1 C * (t1 C * t2 C) := by
  have hp := positive C hC
  have ha : ((D1 C).natAbs : ℚ) = (D1 C : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_pos hp.1]
  have hb : ((D2 C).natAbs : ℚ) = (D2 C : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_pos hp.2.1]
  simp only [potential, Nat.cast_mul, ha, hb,
    (prefix_values C (ne_of_gt hp.2.2.1)).1,
    (prefix_values C (ne_of_gt hp.2.2.1)).2]

theorem gram3Identities : Gram3Identities := by
  intro C hC
  have hp := positive C hC
  have h1 := ne_of_gt hp.2.2.1
  have h2 := ne_of_gt hp.2.2.2.1
  refine
    { positive := hp
      minors := minors C
      orthogonal := orthogonal C h1 h2
      prefix_values := prefix_values C h1
      potential_cast := potential_cast C hC
      determinant := ⟨orthogonal_det C, determinant C h1 h2⟩
      norms := norms C h1 h2
      shear_det := shear_det
      shear21 := ?_
      shear32 := ?_
      shear31 := ?_
      swap12 := ⟨swap12_det, swap12_facts C h1 h2⟩
      swap23 := ⟨swap23_det, swap23_facts C h1 h2⟩ }
  · intro k
    have h := shear21_facts C k h1 h2
    exact ⟨h.det, h.first, h.second, h.pot, h.one, h.two, h.three, h.coeff21,
      by simpa using h.coeff31, by simpa using h.coeff32⟩
  · intro k
    have h := shear32_facts C k h1 h2
    exact ⟨h.det, h.first, h.second, h.pot, h.one, h.two, h.three,
      by simpa using h.coeff21, by simpa using h.coeff31, h.coeff32⟩
  · intro k
    have h := shear31_facts C k h1 h2
    exact ⟨h.det, h.first, h.second, h.pot, h.one, h.two, h.three,
      by simpa using h.coeff21, by simpa using h.coeff31, by simpa using h.coeff32⟩

end Praxis.Algebra.Basis.Gram3
