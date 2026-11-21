import Praxis.Proofs.View.ForwardCoins
import Praxis.Enc
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.QAP
import Praxis.Setting

namespace Praxis.Proofs.View

open Polynomial

set_option maxRecDepth 2048

lemma setEps_valid {P : Params} [Fact (Nat.Prime P.q)] (Dm : QAPData P)
    (c : Coins P) (hc : ValidCoins Dm c) (x : Fq P) (hx : x ≠ 0)
    (hforbid : ∀ k : Fin P.K1, x ≠ -(betaF P ^ (2*k.val))⁻¹) :
    ValidCoins Dm (setCoin c .eps x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [setCoin] using hc.1
  · intro s hs
    have he : s ≠ .eps := by intro hh; subst s; contradiction
    simpa [setCoin, Function.update_of_ne he] using hc.2.1 s hs
  · simpa [setCoin] using hx
  · simpa [setCoin] using hforbid

lemma eps_poly_zero (p : Polynomial (Fq P0)) (hd : p.natDegree ≤ 2)
    (h : ∀ ε : Fq P0, ε ≠ 0 → (∀ k : Fin P0.K1, ε ≠ -(betaF P0 ^ (2*k.val))⁻¹) →
      p.eval ε = 0) : p = 0 := by
  classical
  let bad : Finset (Fq P0) := insert 0 (Finset.univ.image fun k : Fin P0.K1 => -(betaF P0 ^ (2*k.val))⁻¹)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (Finset.univ \ bad)
  · intro ε hε
    have hn : ε ∉ bad := (Finset.mem_sdiff.mp hε).2
    apply h ε
    · intro he
      apply hn
      simp [bad, he]
    · intro k he
      apply hn
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, he.symm⟩
  · have hb : bad.card ≤ P0.K1+1 := by
      apply (Finset.card_insert_le _ _).trans
      apply Nat.add_le_add_right
      exact Finset.card_image_le.trans_eq (by simp only [Finset.card_univ, Fintype.card_fin])
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ bad)]
    simp only [Finset.card_univ, ZMod.card]
    exact hd.trans_lt ((show 2 < P0.q - (P0.K1+1) by decide).trans_le (Nat.sub_le_sub_left hb _))

lemma eps_affine_sep (F H H' : Fq P0)
    (h : ∀ ε : Fq P0, ε ≠ 0 → (∀ k : Fin P0.K1, ε ≠ -(betaF P0 ^ (2*k.val))⁻¹) →
      F + ε*H + H'/ε = 0) : F = 0 := by
  let p : Polynomial (Fq P0) := C H' + C F * X + C H * X^2
  have hp : p = 0 := by
    apply eps_poly_zero
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · apply (natDegree_add_le _ _).trans
        apply max_le
        · simp
        · exact (natDegree_C_mul_le _ _).trans (by simp)
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    · intro ε hε hf
      have hh := h ε hε hf
      simp only [p, eval_add, eval_mul, eval_pow, eval_C, eval_X]
      field_simp [hε] at hh
      linear_combination hh
  have hc := congrArg (fun p : Polynomial (Fq P0) => p.coeff 1) hp
  simpa [p] using hc

end Praxis.Proofs.View
