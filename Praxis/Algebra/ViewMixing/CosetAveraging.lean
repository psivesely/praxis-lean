import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open Classical

namespace ViewCosets

variable {F : Type*} [Field F] {v : ℕ} {mu : F}

def RemainderSupported (v : ℕ) (rem : Polynomial F) : Prop :=
  ∀ e ∈ rem.support, ¬ v ∣ e

theorem power_sum_zero (hmu : IsPrimitiveRoot mu v) (e : ℕ) (he : ¬ v ∣ e) :
    (∑ p : Fin v, (mu ^ e) ^ p.val) = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hx : (mu ^ e) ^ v = 1 := by
    rw [← pow_mul, Nat.mul_comm e v, pow_mul, hmu.pow_eq_one, one_pow]
  have hh := geom_sum_mul (mu ^ e) v
  rw [hx, sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_right
    (sub_ne_zero.mpr ((hmu.pow_eq_one_iff_dvd e).not.mpr he))

theorem sum_monomial_values (a c : F) (e : ℕ) :
    (∑ p : Fin v, a * (c * mu ^ p.val) ^ e) =
      a * c ^ e * ∑ p : Fin v, (mu ^ e) ^ p.val := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hp : (mu ^ p.val) ^ e = (mu ^ e) ^ p.val := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [mul_pow, hp]
  ring

theorem remainder_coset_sum_zero (hmu : IsPrimitiveRoot mu v)
    (rem : Polynomial F) (hs : RemainderSupported v rem) (c : F) :
    (∑ p : Fin v, rem.eval (c * mu ^ p.val)) = 0 := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  rw [sum_monomial_values, power_sum_zero hmu e (hs e he), mul_zero]

end ViewCosets
