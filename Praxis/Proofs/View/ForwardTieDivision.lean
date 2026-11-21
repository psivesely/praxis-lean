import Praxis.Proofs.View.ForwardSeparation
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Proofs.Ties.Division
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open Polynomial

set_option maxRecDepth 2048

lemma fin_monomial_degree_pred {F : Type*} [Semiring F] (n : ℕ) (f : Fin n → F) :
    (∑ e : Fin n, monomial e.val (f e)).natDegree ≤ n-1 := by
  apply natDegree_sum_le_of_forall_le
  intro e _
  apply (natDegree_monomial_le _).trans
  have he := e.isLt
  omega

lemma fin_monomial_coeff {F : Type*} [Semiring F] (n : ℕ) (f : Fin n → F) (e : Fin n) :
    (∑ e' : Fin n, monomial e'.val (f e')).coeff e.val = f e := by
  classical
  simp only [finsetSum_coeff, coeff_monomial, ← Fin.ext_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

lemma kummer_poly_degree {P : Params} [Fact (Nat.Prime P.q)] :
    (X^P.n - C (c0F P) : Polynomial (Fq P)).natDegree = P.n := natDegree_X_pow_sub_C

lemma tie_reduction_of_cancel (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (s : TieIdx) (i : Fin (P0.N+1)) (gm : Fin (P0.n-1) → Fq P0)
    (h : ∀ u : Fq P0, u ≠ 0 →
      (∑ t ∈ Finset.range (2*P0.n-1), u^t * tiePoly v W s t i) +
        (u^P0.n - c0F P0) * (∑ e : Fin (P0.n-1), gm e * u^e.val) = 0) :
    ∀ e : Fin P0.n, reduceP P0.n (c0F P0) (tiePoly v W s) e i = 0 := by
  classical
  let Qp : Polynomial (Fq P0) := ∑ e : Fin (P0.n-1),
    monomial e.val (tieQuot v W s e.val i + gm e)
  let Rp : Polynomial (Fq P0) := ∑ e : Fin P0.n,
    monomial e.val (reduceP P0.n (c0F P0) (tiePoly v W s) e i)
  let Kp : Polynomial (Fq P0) := X^P0.n - C (c0F P0)
  let p : Polynomial (Fq P0) := Kp*Qp + Rp
  have hQ : Qp.natDegree ≤ P0.n-2 := by
    simpa only [Qp, Nat.sub_sub] using fin_monomial_degree_pred (P0.n-1)
      (fun e => tieQuot v W s e.val i + gm e)
  have hR : Rp.natDegree ≤ P0.n-1 := fin_monomial_degree_pred _ _
  have hK : Kp.natDegree = P0.n := kummer_poly_degree (P := P0)
  have hp : p = 0 := by
    apply polynomial_zero_off_zero
    · have hd : p.natDegree ≤ 2*P0.n := by
        apply (natDegree_add_le _ _).trans
        apply max_le
        · apply natDegree_mul_le.trans
          omega
        · omega
      exact hd.trans_lt (by simpa only [ZMod.card] using (show 2*P0.n < P0.q-1 by decide))
    · intro u hu
      have ht := Ties.tie_division v W s u i
      have hh := h u hu
      have hqt : (∑ e : Fin (P0.n-1), tieQuot v W s e.val i * u^e.val) =
          ∑ e ∈ Finset.range (P0.n-1), u^e * tieQuot v W s e i := by
        rw [Fin.sum_univ_eq_sum_range (fun e => tieQuot v W s e i * u^e) (P0.n-1)]
        apply Finset.sum_congr rfl
        intro e _
        ring
      have hrd : (∑ e : Fin P0.n, reduceP P0.n (c0F P0) (tiePoly v W s) e i * u^e.val) =
          ∑ e : Fin P0.n, u^e.val * reduceP P0.n (c0F P0) (tiePoly v W s) e i := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      simp only [p, Qp, Rp, Kp, eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C,
        eval_finsetSum, eval_monomial, add_mul, Finset.sum_add_distrib]
      rw [hqt, hrd]
      linear_combination hh - ht
  have hdiv : Kp ∣ Rp := by
    refine ⟨-Qp, ?_⟩
    change Kp*Qp + Rp = 0 at hp
    linear_combination hp
  have hr0 : Rp = 0 := by
    by_contra hn
    have hd := natDegree_le_of_dvd hdiv hn
    rw [hK] at hd
    exact (not_lt_of_ge hd) (hR.trans_lt (by decide))
  intro e
  have hc := congrArg (fun p : Polynomial (Fq P0) => p.coeff e.val) hr0
  rw [fin_monomial_coeff] at hc
  exact hc

end Praxis.Proofs.View
