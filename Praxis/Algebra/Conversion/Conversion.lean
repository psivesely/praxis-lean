import Praxis.Algebra.Conversion.ConversionExtraction
import Praxis.Algebra.Conversion.L1Minkowski
import Praxis.Algebra.Conversion.ConversionAlgebra
import Praxis.Algebra.Conversion.ConversionStatement

open Matrix

namespace HeavyStack

theorem conversion_with_radius {p n d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (B : Matrix (Fin n) (Fin d) ℤ) (r : Fin d → Fin n) (M : ℕ)
    (hM : (B.submatrix r id).det.natAbs = M) (hMpos : 0 < M)
    (hmax : ∀ s : Fin d → Fin n, (B.submatrix s id).det.natAbs ≤ M)
    (z : Fin n → ZMod p) (hz : z ≠ 0)
    (hcspan : ∃ c : Fin d → ZMod p, ∀ i, z i = ∑ j, (B i j : ZMod p) * c j)
    (R : ℝ) (hR : 0 ≤ R)
    (hRpow : R ^ d = (Nat.factorial d : ℝ) * M * (p : ℝ) ^ (d - 1)) :
    ∃ (w : Fin n → ℤ) (a : ZMod p),
      w ≠ 0 ∧ a ≠ 0 ∧ (∀ i, (w i : ZMod p) = a * z i) ∧
      ∀ i, |(w i : ℝ)| ≤ R := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hwide : (p : ℝ) / 2 ≤ R
  · obtain ⟨w, hw, hwcast, hwbound⟩ := exists_centered_lift z hz
    exact ⟨w, 1, hw, one_ne_zero, by simpa using hwcast,
      fun i => (hwbound i).trans hwide⟩
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hRp : R < (p : ℝ) := by
    have h := lt_of_not_ge hwide
    linarith
  obtain ⟨c, hc⟩ := hcspan
  have hcne : ∃ j, c j ≠ 0 := by
    by_contra! h
    apply hz
    funext i
    simp [hc i, h]
  obtain ⟨j, hj⟩ := hcne
  obtain ⟨T, hTdet, hTline⟩ := exists_lineMatrix c j hj
  let A := B.submatrix r id
  let C := A * T
  have hAdet : A.det ≠ 0 := by
    intro h
    have : M = 0 := by simpa [A, h] using hM.symm
    omega
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hCdet : C.det ≠ 0 := by
    rw [show C.det = A.det * T.det from Matrix.det_mul A T, hTdet]
    exact mul_ne_zero hAdet (pow_ne_zero _ hp0)
  have hMabs : |(A.det : ℝ)| = (M : ℝ) := by
    calc
      _ = (A.det.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
      _ = _ := by exact_mod_cast hM
  have hCabs : |(C.det : ℝ)| = (M : ℝ) * (p : ℝ) ^ (d - 1) := by
    rw [show C.det = A.det * T.det from Matrix.det_mul A T, hTdet]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, abs_mul, abs_pow,
      abs_of_nonneg (show 0 ≤ (p : ℝ) from Nat.cast_nonneg p), hMabs]
  have hCb : (Nat.factorial d : ℝ) * |(C.det : ℝ)| ≤ R ^ d := by
    rw [hCabs, hRpow]
    apply le_of_eq
    ring
  obtain ⟨t, ht0, ht⟩ := exists_int_mulVec_l1_le hd C hCdet hR hCb
  let w := B *ᵥ (T *ᵥ t)
  have hproj : C *ᵥ t = fun k => w (r k) := by
    dsimp [C, A, w]
    rw [Matrix.mulVec_mulVec]
    rfl
  have hw : w ≠ 0 := by
    intro h
    apply ht0
    rw [hproj, h]
    rfl
  have hpiv : (∑ k, |(w (r k) : ℝ)|) ≤ R := by
    simpa only [l1, hproj] using ht
  let B' : Matrix (Fin n) (Fin d) ℝ := B.map fun x => (x : ℝ)
  have hcastminor (s : Fin d → Fin n) :
      (B'.submatrix s id).det = ((B.submatrix s id).det : ℝ) :=
    (Int.cast_det _).symm
  have hdetR : (B'.submatrix r id).det ≠ 0 := by
    rw [hcastminor]
    exact_mod_cast hAdet
  have hmaxR (s : Fin d → Fin n) :
      |(B'.submatrix s id).det| ≤ |(B'.submatrix r id).det| := by
    rw [hcastminor s, hcastminor r]
    change |((B.submatrix s id).det : ℝ)| ≤ |(A.det : ℝ)|
    rw [hMabs]
    have h : ((B.submatrix s id).det.natAbs : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hmax s
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hwbound (i : Fin n) : |(w i : ℝ)| ≤ R := by
    have h := maximalMinor_coordinate_bound B' r hdetR hmaxR
      (fun k => ((T *ᵥ t) k : ℝ)) i
    have h' : |(w i : ℝ)| ≤ ∑ k, |(w (r k) : ℝ)| := by
      simpa only [B', w, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul] using h
    exact h'.trans hpiv
  obtain ⟨a, ha⟩ := hTline t
  have hcong (i : Fin n) : (w i : ZMod p) = a * z i := by
    change ((B *ᵥ (T *ᵥ t)) i : ZMod p) = _
    rw [Matrix.mulVec, dotProduct, Int.cast_sum]
    simp only [Int.cast_mul, ha]
    rw [hc i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hane : a ≠ 0 := scalar_ne_zero_of_short_congruence w hw
    (fun i => (hwbound i).trans_lt hRp) z a hcong
  exact ⟨w, a, hw, hane, hcong, hwbound⟩

theorem conversion_root {p n d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (B : Matrix (Fin n) (Fin d) ℤ) (r : Fin d → Fin n) (M : ℕ)
    (hM : (B.submatrix r id).det.natAbs = M) (hMpos : 0 < M)
    (hmax : ∀ s : Fin d → Fin n, (B.submatrix s id).det.natAbs ≤ M)
    (z : Fin n → ZMod p) (hz : z ≠ 0)
    (hcspan : ∃ c : Fin d → ZMod p, ∀ i, z i = ∑ j, (B i j : ZMod p) * c j) :
    ∃ (w : Fin n → ℤ) (a : ZMod p),
      w ≠ 0 ∧ a ≠ 0 ∧ (∀ i, (w i : ZMod p) = a * z i) ∧
      ∀ i, |(w i : ℝ)| ≤
        ((Nat.factorial d : ℝ) * M * (p : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹) := by
  apply conversion_with_radius hp hd B r M hM hMpos hmax z hz hcspan
  · positivity
  · exact Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hd)

theorem conversion_general {d : ℕ} (hd : 0 < d) : ConversionClaim d := by
  intro p n hp B r M hM hMpos _hMp hmax z hz hcspan
  obtain ⟨w, a, hw, ha, hcong, hbound⟩ :=
    conversion_root hp hd B r M hM hMpos hmax z hz hcspan
  refine ⟨w, a, hw, ha, hcong, ?_⟩
  intro i
  calc
    |(w i : ℝ)| ^ d ≤
        (((Nat.factorial d : ℝ) * M * (p : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹)) ^ d := by
      gcongr
      exact hbound i
    _ = _ := Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hd)

theorem conversion_rank_two : ConversionClaim 2 := conversion_general (by decide)

theorem conversion_rank_three : ConversionClaim 3 := conversion_general (by decide)

end HeavyStack
