import Praxis.Proofs.Basic

namespace Praxis.Proofs.DecryptionAlgebra

open Polynomial

private theorem chunk_injective (Y M : ℕ) :
    Function.Injective (fun lm : Fin Y × Fin M => lm.1.val + Y * lm.2.val) := by
  intro a b h
  have he : finProdFinEquiv (a.2, a.1) = finProdFinEquiv (b.2, b.1) := by
    apply Fin.ext
    exact h
  have hp := finProdFinEquiv.injective he
  exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)

private theorem eval_of_chunks {F J : Type*} [CommSemiring F] [Fintype J]
    (P : Polynomial F) (tau : F) (e : J → ℕ) (he : Function.Injective e)
    (hcover : ∀ n, P.coeff n ≠ 0 → n ∈ Set.range e) :
    (∑ j, P.coeff (e j) * tau ^ e j) = P.eval tau := by
  classical
  have hs : P.support ⊆ Finset.univ.image e := by
    intro n hn
    obtain ⟨j, hj⟩ := hcover n (Polynomial.mem_support_iff.mp hn)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  calc
    _ = ∑ n ∈ Finset.univ.image e, P.coeff n * tau ^ n := by
      symm
      exact Finset.sum_image he.injOn
    _ = P.eval tau := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum_eq_of_subset (fun n a => a * tau ^ n)
        (fun _ => zero_mul _) hs]

theorem quotient_chunks {F : Type*} [CommSemiring F] (Y M : ℕ) (hY : 0 < Y)
    (P : Polynomial F) (tau : F) (hP : P.natDegree < Y * M) :
    (∑ l : Fin Y, ∑ m : Fin M,
      P.coeff (l.val + Y * m.val) * (tau ^ l.val * tau ^ (Y * m.val))) = P.eval tau := by
  have h := eval_of_chunks P tau _ (chunk_injective Y M) (fun n hn => by
    have hn' : n < Y * M := lt_of_le_of_lt (le_natDegree_of_ne_zero hn) hP
    refine ⟨(⟨n % Y, Nat.mod_lt _ hY⟩, ⟨n / Y, ?_⟩), ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hY).2 (by simpa [Nat.mul_comm] using hn')
    · simp only
      exact Nat.mod_add_div n Y)
  simpa only [Fintype.sum_prod_type, pow_add] using h

theorem remainder_chunks {F : Type*} [CommSemiring F] (U Y M : ℕ) (hY : 0 < Y)
    (hdiv : U ∣ Y) (P : Polynomial F) (tau : F) (hP : P.natDegree < Y * M)
    (hsparse : ∀ n, U ∣ n → P.coeff n = 0) :
    (∑ l : Fin Y, ∑ m : Fin M,
      if U ∣ l.val then 0 else
        P.coeff (l.val + Y * m.val) * (tau ^ l.val * tau ^ (Y * m.val))) = P.eval tau := by
  rw [← quotient_chunks Y M hY P tau hP]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs with hl
  · rw [hsparse _ (dvd_add hl (dvd_mul_of_dvd_left hdiv _)), zero_mul]
  · rfl

end Praxis.Proofs.DecryptionAlgebra
