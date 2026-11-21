import Praxis.Kummer
import Praxis.Encryption.BN254
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Finite.Basic
import Praxis.Constants
import Praxis.Params

set_option maxRecDepth 2048

namespace Praxis

namespace KummerIrr

open Polynomial IntermediateField

theorem q_prime : Nat.Prime Constants.q :=
  Encryption.BN254.r_prime

instance : Fact (Nat.Prime Constants.q) := ⟨q_prime⟩

private lemma norm_gen_binomial {K E : Type*} [Field K] [Field E] [Algebra K E]
    {a : K} {m : ℕ} (hm : m ≠ 0) (x : E)
    (hx : minpoly K x = X ^ m - C a) :
    Algebra.norm K (AdjoinSimple.gen K x) = (-1) ^ m * -a := by
  have hi : IsIntegral K x := not_not.mp fun h ↦ by
    simpa only [degree_zero, degree_X_pow_sub_C (Nat.pos_of_ne_zero hm),
      WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
  rw [← adjoin.powerBasis_gen hi, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  simp [minpoly_gen, hx, Ne.symm hm]

private theorem irreducible_two_pow {K : Type*} [Field K] {a i : K}
    (ha : ∀ b : K, b ^ 2 ≠ a) (hi : i ^ 2 = -1) (k : ℕ) :
    Irreducible (X ^ (2 ^ (k + 1)) - C a) := by
  induction k with
  | zero =>
    simpa using X_pow_sub_C_irreducible_of_prime Nat.prime_two ha
  | succ k ih =>
    rw [pow_succ, mul_comm]
    apply X_pow_mul_sub_C_irreducible ih
    intro E _ _ x hx
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    have hn := norm_gen_binomial (by positivity : 2 ^ (k + 1) ≠ 0) x hx
    have he : Even (2 ^ (k + 1)) := even_two.pow_of_ne_zero (by omega)
    rw [he.neg_one_pow, one_mul] at hn
    have hnorm : (Algebra.norm K b) ^ 2 = -a := by
      rw [← map_pow, hb, hn]
    apply ha (i * Algebra.norm K b)
    rw [mul_pow, hi, hnorm]
    ring

private lemma modpow_cast (a e r : ℕ)
    (he : e < 2 ^ 254)
    (h : Encryption.BN254.modularPower Constants.q 254 a e 1 = r) :
    (a : ZMod Constants.q) ^ e = (r : ZMod Constants.q) := by
  have := Encryption.BN254.modularPower_correct Constants.q 254 a e 1 he
  simpa only [h, Nat.cast_one, one_mul] using this.symm

theorem c0_pow_half : (Constants.c0 : ZMod Constants.q) ^ ((Constants.q - 1) / 2) = -1 := by
  have h := modpow_cast Constants.c0 ((Constants.q - 1) / 2) (Constants.q - 1)
    (by decide) (by decide +kernel)
  rw [h]
  rw [Nat.cast_sub (by decide : 1 ≤ Constants.q), Nat.cast_one, ZMod.natCast_self, zero_sub]

def cubeResidue : ℕ := 4407920970296243842393367215006156084916469457145843978461

theorem c0_pow_third : (Constants.c0 : ZMod Constants.q) ^ ((Constants.q - 1) / 3) =
    (cubeResidue : ZMod Constants.q) := by
  apply modpow_cast
  · decide
  · decide +kernel

theorem beta_def : (Constants.beta : ZMod Constants.q) =
    (Constants.c0 : ZMod Constants.q) ^ ((Constants.q - 1) / Constants.n) := by
  symm
  apply modpow_cast
  · decide
  · decide +kernel

private lemma not_power_of_witness {p : ℕ} (hp : 0 < p)
    (hd : p ∣ Constants.q - 1)
    (hw : (Constants.c0 : ZMod Constants.q) ^ ((Constants.q - 1) / p) ≠ 1) :
    ∀ b : ZMod Constants.q, b ^ p ≠ (Constants.c0 : ZMod Constants.q) := by
  intro b hb
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_zero_of_lt hp)] at hb
    have hc : (Constants.c0 : ZMod Constants.q) ≠ 0 := by decide
    exact hc hb.symm
  apply hw
  rw [← hb, ← pow_mul, Nat.mul_div_cancel' hd]
  exact ZMod.pow_card_sub_one_eq_one hb0

theorem c0_not_square : ∀ b : ZMod Constants.q, b ^ 2 ≠ (Constants.c0 : ZMod Constants.q) := by
  apply not_power_of_witness (by decide) (by decide)
  rw [c0_pow_half]
  decide

theorem c0_not_cube : ∀ b : ZMod Constants.q, b ^ 3 ≠ (Constants.c0 : ZMod Constants.q) := by
  apply not_power_of_witness (by decide) (by decide)
  rw [c0_pow_third]
  decide

theorem sqrt_neg_one :
    ((Constants.c0 : ZMod Constants.q) ^ ((Constants.q - 1) / 4)) ^ 2 = -1 := by
  rw [← pow_mul]
  have he : (Constants.q - 1) / 4 * 2 = (Constants.q - 1) / 2 := by decide
  rw [he, c0_pow_half]

theorem irreducible_two_part :
    Irreducible ((X : Polynomial (ZMod Constants.q)) ^ (2 ^ 9) - C (Constants.c0 : ZMod Constants.q)) := by
  have h := irreducible_two_pow (i := (Constants.c0 : ZMod Constants.q) ^ ((Constants.q - 1) / 4))
    c0_not_square sqrt_neg_one 8
  simpa only [show 8 + 1 = 9 by decide] using h

theorem main : KummerIrreducible Params.main := by
  unfold KummerIrreducible KummerPoly c0F
  dsimp only [Params.main]
  have hn : Constants.n = 3 ^ 2 * 2 ^ 9 := by decide
  rw [hn]
  apply X_pow_mul_sub_C_irreducible irreducible_two_part
  intro E _ _ x hx
  apply X_pow_sub_C_irreducible_of_prime_pow (by norm_num : Nat.Prime 3) (by decide) 2
  intro b hb
  have hn := norm_gen_binomial (by norm_num : 2 ^ 9 ≠ 0) x hx
  norm_num at hn
  have hnorm : (Algebra.norm (ZMod Constants.q) b) ^ 3 = -(Constants.c0 : ZMod Constants.q) := by
    rw [← map_pow, hb, hn]
  apply c0_not_cube (-Algebra.norm (ZMod Constants.q) b)
  rw [neg_pow, hnorm]
  norm_num

theorem beta_pow_m : (Constants.beta : ZMod Constants.q) ^ Constants.m = -1 := by
  rw [beta_def, ← pow_mul]
  have he : (Constants.q - 1) / Constants.n * Constants.m = (Constants.q - 1) / 2 := by
    decide
  rw [he, c0_pow_half]

theorem beta_pow_third : (Constants.beta : ZMod Constants.q) ^ (Constants.n / 3) =
    (cubeResidue : ZMod Constants.q) := by
  rw [beta_def, ← pow_mul]
  have he : (Constants.q - 1) / Constants.n * (Constants.n / 3) = (Constants.q - 1) / 3 := by
    decide
  rw [he, c0_pow_third]

theorem beta_order : orderOf (Constants.beta : ZMod Constants.q) = Constants.n := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · have hn : Constants.n = Constants.m * 2 := by decide
    rw [hn, pow_mul, beta_pow_m]
    norm_num
  · intro p hp hd
    have hn : Constants.n = 2 ^ 9 * 3 ^ 2 := by decide
    rw [hn] at hd
    have hp23 : p = 2 ∨ p = 3 := by
      rcases hp.dvd_mul.mp hd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp
          (hp.dvd_of_dvd_pow h))
    rcases hp23 with rfl | rfl
    · have he : Constants.n / 2 = Constants.m := by decide
      rw [he, beta_pow_m]
      decide
    · rw [beta_pow_third]
      decide

theorem main_betaLaws : BetaLaws Params.main :=
  ⟨beta_def, beta_order, beta_pow_m⟩

end KummerIrr

end Praxis
