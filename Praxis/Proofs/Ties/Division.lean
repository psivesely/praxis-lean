import Praxis.Proofs.Ties.Honest
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Ties

open Praxis.Algebra (Vec)

private lemma rawMulMV_top {F : Type*} [CommSemiring F] {N n : ℕ}
    (hn : 0 < n) (A : KPoly (Algebra.Mat F N) n) (b : KPoly (Vec F N) n) :
    rawMulMV A b (n - 1 + n) = 0 := by
  unfold rawMulMV
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  have hj := j.isLt
  have hk := k.isLt
  exact if_neg (by omega)

private lemma eval_division {F : Type*} [CommRing F] (n : ℕ) (hn : 0 < n)
    (p : ℕ → F) (htop : p (n - 1 + n) = 0) (u c : F) :
    ∑ t ∈ Finset.range (2 * n - 1), u ^ t * p t =
      (u ^ n - c) * ∑ e ∈ Finset.range (n - 1), u ^ e * p (e + n) +
        ∑ e : Fin n, u ^ e.val * (p e.val + c * p (e.val + n)) := by
  have hn' : n - 1 + 1 = n := by omega
  have htail := Finset.sum_range_succ (fun e => u ^ e * p (e + n)) (n - 1)
  rw [hn', htop, mul_zero, add_zero] at htail
  have hred : (∑ e : Fin n, u ^ e.val * (p e.val + c * p (e.val + n))) =
      (∑ e ∈ Finset.range n, u ^ e * p e) +
        c * ∑ e ∈ Finset.range (n - 1), u ^ e * p (e + n) := by
    rw [Fin.sum_univ_eq_sum_range (fun e => u ^ e * (p e + c * p (e + n)))]
    simp_rw [mul_add, mul_left_comm (u ^ _) c]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htail]
  have hsplit : 2 * n - 1 = n + (n - 1) := by omega
  rw [hsplit, Finset.sum_range_add, hred]
  have hhigh : (∑ e ∈ Finset.range (n - 1), u ^ (n + e) * p (n + e)) =
      u ^ n * ∑ e ∈ Finset.range (n - 1), u ^ e * p (e + n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [pow_add, Nat.add_comm n e, mul_assoc]
  rw [hhigh]
  ring

theorem tie_division (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (s : TieIdx) (u : Fq P0)
    (i : Fin (P0.N + 1)) :
    ∑ t ∈ Finset.range (2 * P0.n - 1), u ^ t * tiePoly v W s t i =
      (u ^ P0.n - c0F P0) * ∑ e ∈ Finset.range (P0.n - 1), u ^ e * tieQuot v W s e i +
        ∑ e : Fin P0.n, u ^ e.val * reduceP P0.n (c0F P0) (tiePoly v W s) e i := by
  have hn : 0 < P0.n := by decide
  have htop : tiePoly v W s (P0.n - 1 + P0.n) = 0 := by
    cases s <;> simp only [tiePoly, Pi.sub_apply, rawMulMV_top hn, sub_self]
  simpa only [tieQuot, quotP, reduceP, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    eval_division P0.n hn (fun t => tiePoly v W s t i)
      (congrFun htop i) u (c0F P0)

end Praxis.Proofs.Ties
