import Praxis.Algebra.ViewMixing.CosetAveraging
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open Classical

namespace ViewInterpolation

variable {F G I : Type*} [Field F] [Fintype G] {v : ℕ} {mu : F}

def meanPolynomial (v : ℕ) (mu : F) (p : Polynomial F) : Polynomial F :=
  ∑ j : Fin v, p.comp (Polynomial.C (mu ^ j.val) * Polynomial.X)

theorem mean_coefficient (hmu : IsPrimitiveRoot mu v) (p : Polynomial F) (e : ℕ) :
    (meanPolynomial v mu p).coeff e = if v ∣ e then (v : F) * p.coeff e else 0 := by
  have hp : ∀ j : Fin v, (mu ^ j.val) ^ e = (mu ^ e) ^ j.val := by
    intro j; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [meanPolynomial, Polynomial.finsetSum_coeff, Polynomial.comp_C_mul_X_coeff, hp]
  rw [← Finset.mul_sum]
  by_cases he : v ∣ e
  · rw [if_pos he, (hmu.pow_eq_one_iff_dvd e).mpr he]
    simp [mul_comm]
  · rw [if_neg he, ViewCosets.power_sum_zero hmu e he, mul_zero]

theorem mean_degree_lt (hmu : IsPrimitiveRoot mu v) (p : Polynomial F) (n : ℕ)
    (hp : p.degree < n) : (meanPolynomial v mu p).degree < n := by
  rw [Polynomial.degree_lt_iff_coeff_zero] at hp ⊢
  intro e he
  rw [mean_coefficient hmu, hp e he]
  split_ifs <;> simp

theorem mean_eval (p : Polynomial F) (c : F) :
    (meanPolynomial v mu p).eval c = ∑ j : Fin v, p.eval (c * mu ^ j.val) := by
  simp [meanPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_comp, mul_comm]

theorem mean_coset_invariant (hmu : IsPrimitiveRoot mu v) (p : Polynomial F)
    (c : F) (j : Fin v) :
    (meanPolynomial v mu p).eval (c * mu ^ j.val) = (meanPolynomial v mu p).eval c := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_congr rfl
  intro e he
  have hne := Polynomial.mem_support_iff.mp he
  have hd : v ∣ e := by
    by_contra hd
    rw [mean_coefficient hmu p e, if_neg hd] at hne
    exact hne rfl
  have hp : (mu ^ j.val) ^ e = 1 := by
    rw [← pow_mul, Nat.mul_comm j.val e, pow_mul, (hmu.pow_eq_one_iff_dvd e).mpr hd, one_pow]
  rw [mul_pow, hp, mul_one]

theorem exists_supported_remainder (hmu : IsPrimitiveRoot mu v) (hv : (v : F) ≠ 0)
    (c : G → F)
    (hNodes : Function.Injective (fun x : G × Fin v => c x.1 * mu ^ x.2.val))
    (values : G × Fin v → F) (hSum : ∀ g, (∑ j : Fin v, values (g,j)) = 0) :
    ∃ rem : Polynomial F, rem.degree < (v * Fintype.card G : ℕ) ∧
      ViewCosets.RemainderSupported v rem ∧
      ∀ x : G × Fin v, rem.eval (c x.1 * mu ^ x.2.val) = values x := by
  let nodes : G × Fin v → F := fun x => c x.1 * mu ^ x.2.val
  let rem := Lagrange.interpolate Finset.univ nodes values
  have hEval : ∀ x, rem.eval (nodes x) = values x := by
    intro x
    exact Lagrange.eval_interpolate_at_node values hNodes.injOn (Finset.mem_univ x)
  have hDeg : rem.degree < (v * Fintype.card G : ℕ) := by
    simpa [rem, Fintype.card_prod, Nat.mul_comm] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) (v := nodes) values hNodes.injOn
  have hMean : meanPolynomial v mu rem = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Finset.univ)
      hNodes.injOn
    · simpa [Fintype.card_prod, Nat.mul_comm] using mean_degree_lt hmu rem _ hDeg
    · intro x _
      rw [mean_coset_invariant hmu rem (c x.1) x.2, mean_eval]
      change (∑ j : Fin v, rem.eval (nodes (x.1,j))) = 0
      simp_rw [hEval]
      exact hSum x.1
  refine ⟨rem, hDeg, ?_, hEval⟩
  intro e he hd
  have hh := congrArg (fun p : Polynomial F => p.coeff e) hMean
  rw [mean_coefficient hmu, if_pos hd, Polynomial.coeff_zero] at hh
  exact (Polynomial.mem_support_iff.mp he) ((mul_eq_zero.mp hh).resolve_left hv)

theorem product_linear_dvd (t : Finset I) (nodes : I → F) (hNodes : Function.Injective nodes)
    (p : Polynomial F) (hEval : ∀ i ∈ t, p.eval (nodes i) = 0) :
    (∏ i ∈ t, (Polynomial.X - Polynomial.C (nodes i))) ∣ p := by
  induction t using Finset.induction_on generalizing p with
  | empty => simp
  | @insert i t hi ih =>
    have hpi : p.eval (nodes i) = 0 := hEval i (Finset.mem_insert_self _ _)
    obtain ⟨q,hq⟩ := (Polynomial.dvd_iff_isRoot.mpr hpi)
    have hqEval : ∀ j ∈ t, q.eval (nodes j) = 0 := by
      intro j hj
      have hh := hEval j (Finset.mem_insert_of_mem hj)
      rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hh
      have hne : nodes j - nodes i ≠ 0 := by
        intro he
        have he := hNodes (sub_eq_zero.mp he)
        exact hi (he ▸ hj)
      exact (mul_eq_zero.mp hh).resolve_left hne
    obtain ⟨r,hr⟩ := ih q hqEval
    refine ⟨r, ?_⟩
    rw [Finset.prod_insert hi, hq, hr]
    ring

end ViewInterpolation
