import Praxis.Algebra.Basis.ElementaryModel
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith

namespace Praxis.Algebra.Basis.MinPotential3

open Praxis.Algebra.Basis.ElementaryModel

theorem unimodular_mul {d : ℕ} {U V : ZMatrix d}
    (hU : Unimodular U) (hV : Unimodular V) : Unimodular (U * V) := by
  rcases hU with hU | hU <;> rcases hV with hV | hV <;>
    simp [Unimodular, Matrix.det_mul, hU, hV]

theorem det_mul_ne_zero {d : ℕ} {C U : ZMatrix d}
    (hC : C.det ≠ 0) (hU : Unimodular U) : (C * U).det ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero hC (by rcases hU with hU | hU <;> simp [hU])

theorem exists_minimum (C : ZMatrix 3) :
    ∃ U : ZMatrix 3, Unimodular U ∧
      ∀ V : ZMatrix 3, Unimodular V → potential (C * U) ≤ potential (C * V) := by
  classical
  let : Nonempty {U : ZMatrix 3 // Unimodular U} :=
    ⟨⟨1, Or.inl (Matrix.det_one)⟩⟩
  let f : {U : ZMatrix 3 // Unimodular U} → ℕ := fun U => potential (C * U.val)
  let U := Function.argmin f
  exact ⟨U.val, U.property, fun V hV => Function.argmin_le f ⟨V, hV⟩⟩

theorem potential_cast_prefix {C : ZMatrix 3} (g : Gram3Facts C) :
    (potential C : ℚ) = (D1 C : ℚ) * (D2 C : ℚ) := by
  rw [g.prefix_values.1, g.prefix_values.2]
  exact g.potential_cast

private theorem ratio_of_comparison {a b μ : ℚ} (ha : 0 < a)
    (hμ : |μ| ≤ (1 / 2 : ℚ)) (h : a ≤ b + μ ^ 2 * a) :
    3 * a ≤ 4 * b := by
  have hsq : μ ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg μ) (by norm_num)).2 hμ
  nlinarith [mul_le_mul_of_nonneg_right hsq ha.le]

theorem adjacent_ratios (hGram : Gram3Identities)
    {C U : ZMatrix 3} (hC : C.det ≠ 0) (hU : Unimodular U)
    (hsize : SizeBounds3 (C * U))
    (hmin : ∀ V : ZMatrix 3, Unimodular V → potential (C * U) ≤ potential (C * V)) :
    3 * t1 (C * U) ≤ 4 * t2 (C * U) ∧
    3 * t2 (C * U) ≤ 4 * t3 (C * U) := by
  let B := C * U
  have hB : B.det ≠ 0 := det_mul_ne_zero hC hU
  have g := hGram B hB
  have ht1 : 0 < t1 B := g.positive.2.2.1
  have ht2 : 0 < t2 B := g.positive.2.2.2.1
  rcases g.swap12 with ⟨hs12, hd12, hD2, hD1⟩
  rcases g.swap23 with ⟨hs23, hd23, hD1', hD2'⟩
  have g12 := hGram (B * swapChange 0 1) (by rw [hd12]; exact neg_ne_zero.mpr hB)
  have g23 := hGram (B * swapChange 1 2) (by rw [hd23]; exact neg_ne_zero.mpr hB)
  have h12 : potential B ≤ potential (B * swapChange 0 1) := by
    simpa only [B, Matrix.mul_assoc] using
      hmin (U * swapChange 0 1) (unimodular_mul hU (Or.inr hs12))
  have h23 : potential B ≤ potential (B * swapChange 1 2) := by
    simpa only [B, Matrix.mul_assoc] using
      hmin (U * swapChange 1 2) (unimodular_mul hU (Or.inr hs23))
  have h12Q : (potential B : ℚ) ≤ (potential (B * swapChange 0 1) : ℚ) := by
    exact_mod_cast h12
  have h23Q : (potential B : ℚ) ≤ (potential (B * swapChange 1 2) : ℚ) := by
    exact_mod_cast h23
  rw [potential_cast_prefix g, potential_cast_prefix g12,
    hD2, hD1, g.prefix_values.1] at h12Q
  have hD2pos : (0 : ℚ) < D2 B := by exact_mod_cast g.positive.2.1
  have hlen12 : t1 B ≤ t2 B + m21 B ^ 2 * t1 B :=
    (mul_le_mul_iff_left₀ hD2pos).mp h12Q
  rw [potential_cast_prefix g, potential_cast_prefix g23,
    hD1', hD2', g.prefix_values.1, g.prefix_values.2] at h23Q
  have hlen23 : t2 B ≤ t3 B + m32 B ^ 2 * t2 B :=
    (mul_le_mul_iff_right₀ ht1).mp ((mul_le_mul_iff_right₀ ht1).mp h23Q)
  exact ⟨ratio_of_comparison ht1 hsize.1 hlen12,
    ratio_of_comparison ht2 hsize.2.2 hlen23⟩

theorem reducedPotential3 (hGram : Gram3Identities) (hReduce : SizeReduce3) :
    ReducedPotential3 := by
  intro C hC
  obtain ⟨U, hU, hmin⟩ := exists_minimum C
  obtain ⟨hR, hpot, hsize⟩ := hReduce (C * U) (det_mul_ne_zero hC hU)
  let V := U * sizeReduceChange (C * U)
  have hV : Unimodular V := unimodular_mul hU hR
  have hpotV : potential (C * V) = potential (C * U) := by
    simpa only [V, Matrix.mul_assoc] using hpot
  have hsizeV : SizeBounds3 (C * V) := by
    simpa only [V, Matrix.mul_assoc] using hsize
  have hminV : ∀ W : ZMatrix 3, Unimodular W → potential (C * V) ≤ potential (C * W) := by
    intro W hW
    rw [hpotV]
    exact hmin W hW
  exact ⟨V, hV, hsizeV, hminV, adjacent_ratios hGram hC hV hsizeV hminV⟩

end Praxis.Algebra.Basis.MinPotential3
