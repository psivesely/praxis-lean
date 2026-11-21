import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open Polynomial

namespace Praxis.Proofs.Classification

theorem roots_bound_of_independent {K E : Type*} [Field K] [Fintype K]
    [Field E] [Algebra K E] {d : ℕ} (a : Fin d → E)
    (ha : LinearIndependent K a) (L : E →ₗ[K] E) (p : E[X])
    (hp : p ≠ 0) (hL : ∀ x, p.eval x = L x)
    (hz : ∀ i, L (a i) = 0) : Fintype.card K ^ d ≤ p.natDegree := by
  classical
  let f : (Fin d → K) → E := fun c => ∑ i, c i • a i
  have hf : Function.Injective f := by
    intro c c' h
    apply ha.fintypeLinearCombination_injective
    simpa [f, Fintype.linearCombination_apply] using h
  let S : Finset E := Finset.univ.image f
  have hcard : S.card = Fintype.card K ^ d := by
    simp [S, Finset.card_image_of_injective _ hf]
  have hroot : ∀ x ∈ S, p.eval x = 0 := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
    rw [hL]
    simp [f, hz]
  rw [← hcard]
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  rw [Polynomial.mem_roots hp]
  exact hroot x hx

theorem moore_det {K E : Type*} [Field K] [Fintype K]
    [Field E] [Algebra K E] {d : ℕ} (a : Fin d → E)
    (ha : LinearIndependent K a) :
    IsUnit (Matrix.of fun i j : Fin d => a i ^ (Fintype.card K ^ j.val)).det := by
  classical
  apply isUnit_iff_ne_zero.mpr
  intro hdet
  obtain ⟨c, hc, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hci : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hc
    funext i
    simpa using not_exists.mp h i
  obtain ⟨k, hk⟩ := hci
  let q := Fintype.card K
  have hq : 1 < q := Fintype.one_lt_card
  let p : E[X] := ∑ i : Fin d, monomial (q ^ i.val) (c i)
  have hpcoeff (i : Fin d) : p.coeff (q ^ i.val) = c i := by
    dsimp [p]
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hne : q ^ j.val ≠ q ^ i.val := by
        intro he
        have hv : j.val = i.val := (Nat.pow_right_injective hq) he
        exact hji (Fin.ext hv)
      simp [Polynomial.coeff_monomial, hne]
    · simp
  have hp : p ≠ 0 := by
    intro h
    have := hpcoeff k
    simp [h] at this
    exact hk this.symm
  let L : E →ₗ[K] E := ∑ i : Fin d, c i • ((FiniteField.frobeniusAlgHom K E) ^ i.val).toLinearMap
  have hL : ∀ x, p.eval x = L x := by
    intro x
    simp only [p, L, q, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, AlgHom.toLinearMap_apply,
      AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
  have hz : ∀ i, L (a i) = 0 := by
    intro i
    have hi := congrFun hzero i
    rw [← hL]
    simpa [p, q, Polynomial.eval_finsetSum, Matrix.mulVec, dotProduct,
      Matrix.of_apply, mul_comm] using hi
  have hbound := roots_bound_of_independent a ha L p hp hL hz
  have hpdeg : p.natDegree ≤ q ^ (d - 1) := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.pow_le_pow_right (by omega) (by have := i.isLt; omega))
  have hd : 0 < d := by have := k.isLt; omega
  have hlt : q ^ (d - 1) < q ^ d := Nat.pow_lt_pow_right hq (by omega)
  exact (not_le_of_gt hlt) (hpdeg.trans' hbound)

end Praxis.Proofs.Classification
