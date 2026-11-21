import Praxis.Algebra.Trans.ChartModel
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Praxis.Algebra.Trans.Definitions

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace Praxis.Algebra.Trans.ChartGram

open Matrix

theorem block_identity {p d : Type*} [Fintype p] [Fintype d]
    [DecidableEq p] [DecidableEq d]
    (P : Matrix p p ℝ) (F : Matrix d p ℝ)
    (S : Matrix (p ⊕ d) (p ⊕ d) ℝ) (hP : P.det ≠ 0) (hS : S.PosDef) :
    let U := fromRows P F
    let A := fromRows (-(P.transpose⁻¹ * F.transpose)) (1 : Matrix d d ℝ)
    P.det^2 * S.det * (A.transpose * S⁻¹ * A).det =
      (U.transpose * S * U).det := by
  dsimp only
  let U := fromRows P F
  let A := fromRows (-(P.transpose⁻¹ * F.transpose)) (1 : Matrix d d ℝ)
  let J : Matrix d (p ⊕ d) ℝ := fromCols 0 1
  let G := U.transpose * S * U
  let C := A.transpose * S⁻¹ * A
  let T := fromCols (S * U) A
  let N := fromRows U.transpose J
  have hp : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hpt : IsUnit P.transpose.det := by simpa using hp
  have hs : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS.isUnit
  have hsym : S.transpose = S := by simpa using hS.1.eq
  have horth : U.transpose * A = 0 := by
    dsimp [U, A]
    rw [transpose_fromRows, fromCols_mul_fromRows]
    simp [Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hpt]
  have horth' : A.transpose * U = 0 := by
    have h := congrArg Matrix.transpose horth
    simpa using h
  have hja : J * A = 1 := by
    simp [J, A, fromCols_mul_fromRows]
  have hN : N = fromBlocks P.transpose F.transpose 0 1 := by
    simp [N, U, J, transpose_fromRows, fromRows_fromCols_eq_fromBlocks]

  let W := fromBlocks (1 : Matrix p p ℝ) (-(P.transpose⁻¹ * F.transpose))
    (0 : Matrix d p ℝ) (1 : Matrix d d ℝ)
  have hW : W.det = 1 := by
    simp [W]
  have hNW : N * W = fromBlocks P.transpose 0 0 (1 : Matrix d d ℝ) := by
    rw [hN]
    simp [W, fromBlocks_multiply, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hpt]
  have hdetN : N.det = P.det := by
    have h := congrArg Matrix.det hNW
    simpa [det_mul, hW, det_fromBlocks_zero₂₁] using h
  have hNT : N * T = fromBlocks G 0 (J * (S * U)) 1 := by
    simp [N, T, ← Matrix.mul_assoc, G, horth, hja]
  have hdetT : P.det * T.det = G.det := by
    have h := congrArg Matrix.det hNT
    simpa [det_mul, hdetN, det_fromBlocks_zero₁₂] using h
  have hST : (S * U).transpose * S⁻¹ = U.transpose := by
    rw [transpose_mul, hsym, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hs,
      Matrix.mul_one]
  have hQT : S⁻¹ * (S * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hs, Matrix.one_mul]
  have hgram : T.transpose * S⁻¹ * T = fromBlocks G 0 0 C := by
    simp only [T, transpose_fromCols, fromRows_mul, mul_fromCols,
      fromCols_fromRows_eq_fromBlocks]
    rw [hST, horth]
    rw [← Matrix.mul_assoc U.transpose S U]
    change fromBlocks G 0 (A.transpose * S⁻¹ * (S * U)) C = _
    rw [Matrix.mul_assoc, hQT, horth']
  have hdetgram : T.det^2 * S⁻¹.det = G.det * C.det := by
    have h := congrArg Matrix.det hgram
    simpa [det_mul, det_transpose, det_fromBlocks_zero₂₁, pow_two, mul_assoc,
      mul_left_comm, mul_comm] using h
  have hU : Function.Injective U.mulVec := by
    intro x y hxy
    apply (Matrix.mulVec_injective_of_isUnit (P.isUnit_iff_isUnit_det.mpr hp))
    funext i
    exact congrFun hxy (Sum.inl i)
  have hG : G.det ≠ 0 := by
    have hpos : G.PosDef := by
      simpa [G] using hS.conjTranspose_mul_mul_same hU
    exact (G.isUnit_iff_isUnit_det.mp hpos.isUnit).ne_zero
  have hcancel : G.det * (P.det^2 * S.det * C.det - G.det) = 0 := by
    have hsq : P.det^2 * T.det^2 = G.det^2 := by rw [← mul_pow, hdetT]
    have hi := Matrix.det_nonsing_inv_mul_det S hs
    linear_combination -P.det^2 * S.det * hdetgram + hsq +
      P.det^2 * T.det^2 * hi
  have heq := (mul_eq_zero.mp hcancel).resolve_left hG
  exact sub_eq_zero.mp heq

theorem pivot_det {r q : ℕ} (B : ChartBasis r q) :
    B.pivotReal.det = (B.a : ℝ) := by
  simpa [ChartBasis.pivotReal, ChartBasis.a, realMatrix, Matrix.map,
    Matrix.submatrix] using ((Int.castRingHom ℝ).map_det
      (B.U.submatrix B.pivot id)).symm

theorem ordered_A {r q : ℕ} (B : ChartBasis r q) :
    B.A.submatrix B.rows id =
      fromRows (-(B.pivotReal.transpose⁻¹ * B.freeReal.transpose))
        (1 : Matrix (Fin (r-q)) (Fin (r-q)) ℝ) := by
  ext i j
  rcases i with i | i <;> simp [ChartBasis.A, Matrix.one_apply]

theorem ordered_U {r q : ℕ} (B : ChartBasis r q) :
    (realMatrix B.U).submatrix B.rows id = fromRows B.pivotReal B.freeReal := by
  ext i j
  rcases i with i | i <;> rfl

theorem chart_identity {r q : ℕ} (B : ChartBasis r q)
    (Sigma : Matrix (Fin r) (Fin r) ℝ) (hB : B.HasPivot) (hSigma : Sigma.PosDef) :
    (B.a : ℝ)^2 * Sigma.det * (B.C Sigma).det = (B.normalGram Sigma).det := by
  have hp : B.pivotReal.det ≠ 0 := by
    rw [pivot_det]
    exact_mod_cast hB
  have h := block_identity B.pivotReal B.freeReal
    (Sigma.submatrix B.rows B.rows) hp (hSigma.submatrix B.rows.injective)
  dsimp only at h
  rw [← ordered_A B, ← ordered_U B, pivot_det,
    det_submatrix_equiv_self, inv_submatrix_equiv] at h
  have hc :
      (B.A.submatrix B.rows id).transpose * Sigma⁻¹.submatrix B.rows B.rows *
        B.A.submatrix B.rows id = B.C Sigma := by
    change B.A.transpose.submatrix id B.rows * Sigma⁻¹.submatrix B.rows B.rows *
      B.A.submatrix B.rows id = _
    simp only [submatrix_mul_equiv, Matrix.submatrix_id_id, ChartBasis.C]
  have hg :
      ((realMatrix B.U).submatrix B.rows id).transpose * Sigma.submatrix B.rows B.rows *
        (realMatrix B.U).submatrix B.rows id = B.normalGram Sigma := by
    change (realMatrix B.U).transpose.submatrix id B.rows * Sigma.submatrix B.rows B.rows *
      (realMatrix B.U).submatrix B.rows id = _
    simp only [submatrix_mul_equiv, Matrix.submatrix_id_id, ChartBasis.normalGram]
  rwa [hc, hg] at h

theorem complementaryGram : ComplementaryGram := by
  intro r q B Sigma _ hB hSigma
  exact chart_identity B Sigma hB hSigma

end Praxis.Algebra.Trans.ChartGram
