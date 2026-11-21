import Praxis.Encryption.GroupModel
import Praxis.Encryption.BN254
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.Defs.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import VCVio.EvalDist.Defs.Instances
import Mathlib.Probability.Distributions.Uniform

namespace Praxis.Algebra.Bilinear

open OracleComp OracleSpec GroupModel.Sorted

open scoped BigOperators

open Classical

noncomputable def gridLaw {F : Type} {n : ℕ} (S : Fin n → Finset F)
    (hS : ∀ i, (S i).Nonempty) : PMF (Fin n → F) :=
  PMF.uniformOfFinset (Fintype.piFinset S) (Fintype.piFinset_nonempty.mpr hS)

theorem prob_uniform_finset {α : Type} (s : Finset α) (hs : s.Nonempty) (E : α → Prop) :
    Pr[E | PMF.uniformOfFinset s hs] = ((s.filter E).card : ENNReal) / s.card := by
  classical
  rw [probEvent_eq_tsum_ite]
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply]
  calc
    _ = ∑' x, if x ∈ s.filter E then (s.card : ENNReal)⁻¹ else 0 := by
      apply tsum_congr
      intro x
      by_cases he : E x <;> by_cases hx : x ∈ s <;> simp [he, hx]
    _ = ∑ x ∈ s.filter E, if x ∈ s.filter E then (s.card : ENNReal)⁻¹ else 0 :=
      tsum_eq_sum fun x hx => if_neg hx
    _ = ∑ _x ∈ s.filter E, (s.card : ENNReal)⁻¹ :=
      Finset.sum_congr rfl fun x hx => if_pos hx
    _ = _ := by simp [div_eq_mul_inv, nsmul_eq_mul]

theorem product_root_count {F : Type} [CommRing F] [IsDomain F] [DecidableEq F]
    {n : ℕ} (P : MvPolynomial (Fin n) F) (hP : P ≠ 0)
    (S : Fin n → Finset F) (m : ℕ) (hm : 0 < m) (hS : ∀ i, m ≤ (S i).card) :
    ((Fintype.piFinset S).filter (fun x => MvPolynomial.eval x P = 0)).card /
      (∏ i, ((S i).card : ℚ≥0)) ≤ (P.totalDegree : ℚ≥0) / m := by
  apply (MvPolynomial.schwartz_zippel_sup_sum hP S).trans
  apply Finset.sup_le
  intro s hs
  calc
    (∑ i, (s i : ℚ≥0) / (S i).card) ≤ ∑ i, (s i : ℚ≥0) / m := by
      apply Finset.sum_le_sum
      intro i _
      exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hm)
        (by exact_mod_cast hS i)
    _ = (∑ i, (s i : ℚ≥0)) / m := (Finset.sum_div _ _ _).symm
    _ ≤ (P.totalDegree : ℚ≥0) / m := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (show ∑ i, s i ≤ P.totalDegree from by
        simpa [Finsupp.sum_fintype] using MvPolynomial.le_totalDegree hs)

theorem small_roots_product_eval {F : Type} [CommRing F] [IsDomain F] [DecidableEq F] {n : ℕ}
    (S : Fin n → Finset F) (hS : ∀ i, (S i).Nonempty)
    (m : ℕ) (hm : 0 < m) (hmin : ∀ i, m ≤ (S i).card)
    (P : MvPolynomial (Fin n) F) (hP : P ≠ 0) :
    Pr[fun x => MvPolynomial.eval x P = 0 | gridLaw S hS] ≤
      (P.totalDegree : ENNReal) / m := by
  classical
  let count := ((Fintype.piFinset S).filter (fun x => MvPolynomial.eval x P = 0)).card
  let size := ∏ i, (S i).card
  have hprod : 0 < size := Finset.prod_pos fun i _ => (hS i).card_pos
  have h := product_root_count P hP S m hm hmin
  have hn : count * m ≤ P.totalDegree * size := by
    have hh := (div_le_div_iff₀ (show (0 : ℚ≥0) < ∏ i, ((S i).card : ℚ≥0) by
      exact_mod_cast hprod) (show (0 : ℚ≥0) < m by exact_mod_cast hm)).mp h
    exact_mod_cast hh
  have hmE : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hsE : (size : ENNReal) ≠ 0 := by exact_mod_cast hprod.ne'
  have hnE : (count : ENNReal) * m ≤ (P.totalDegree : ENNReal) * size := by
    exact_mod_cast hn
  have hd : (count : ENNReal) / size ≤ (P.totalDegree : ENNReal) / m := by
    apply (ENNReal.div_le_iff hsE (ENNReal.natCast_ne_top size)).mpr
    have hc : (P.totalDegree : ENNReal) / m * size =
        ((P.totalDegree : ENNReal) * size) / m := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm]
    rw [hc]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hmE)
      (Or.inl (ENNReal.natCast_ne_top m))).mpr hnE
  rw [gridLaw, prob_uniform_finset]
  convert hd using 1 <;> simp only [count, size, Fintype.card_piFinset, Nat.cast_prod] <;> congr

end Praxis.Algebra.Bilinear
