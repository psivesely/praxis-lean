import Praxis.QAP
import Praxis.Algebra.ViewMixing.RemainderInterpolation
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Stack
import Praxis.Algebra.ViewMixing.CosetAveraging

open scoped BigOperators

open Polynomial

open Praxis.Algebra (Mat MomentGate e0)

namespace Praxis.Proofs.QAP

variable {P : Params} [Fact (Nat.Prime P.q)] {S : Relation P} {Dm : QAPData P}

theorem qap_eval (W : Mat (Fq P) P.N) (x : Fq P) :
    (Dm.qapPoly W).eval x = ∑ i, ∑ j, W i j * (Dm.A i).eval x * (Dm.B j).eval x := by
  simp [QAPData.qapPoly, Polynomial.eval_finsetSum]

theorem qap_col (hD : ValidQAP Dm S) (W : Mat (Fq P) P.N)
    (j : Fin (P.N + 1)) (hj : j ≠ 0) :
    (Dm.qapPoly W).eval (Dm.colPt j) = W j j - W 0 j := by
  classical
  rw [qap_eval]
  simp [hD.A_col, hD.B_col, hj, mul_ite]
  have ht (i : Fin (P.N + 1)) :
      (if i = j then W i j else if i = 0 then -W i j else 0) =
        (if i = j then W i j else 0) - (if i = 0 then W i j else 0) := by
    split_ifs <;> simp_all
  simp_rw [ht]
  simp [Finset.sum_sub_distrib]

theorem qap_col_zero (hD : ValidQAP Dm S) (W : Mat (Fq P) P.N) :
    (Dm.qapPoly W).eval (Dm.colPt 0) = 0 := by
  simp [qap_eval, hD.A_col]

theorem qap_rho (hD : ValidQAP Dm S) (W : Mat (Fq P) P.N) :
    (Dm.qapPoly W).eval Dm.rho = W 0 0 := by
  classical
  rw [qap_eval]
  simp [hD.A_rho, hD.B_rho, e0, mul_ite]

def gateValue (S : Relation P) (W : Mat (Fq P) P.N) (t : Fin P.gatesMax) :
    Option (Fin P.productsMax) → Fq P
  | none => -(∑ j, W 0 j * (S t).linear j)
  | some f => if hf : f.val < (S t).products then
      ∑ i, ∑ j, (S t).left ⟨f.val, hf⟩ i * W i j * (S t).right ⟨f.val, hf⟩ j
    else 0

theorem qap_gate (hD : ValidQAP Dm S) (W : Mat (Fq P) P.N)
    (t : Fin P.gatesMax) (j : Fin P.U) :
    (Dm.qapPoly W).eval (Dm.gatePoint t j) =
      Dm.Z0.eval (Dm.gatePoint t j) * gateValue S W t (Dm.place t j) := by
  classical
  rw [qap_eval]
  simp only [hD.A_gate, hD.B_gate]
  cases hp : Dm.place t j with
  | none =>
    simp only [gateVals, hp, gateValue, e0, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_neg_distrib, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  | some f =>
    by_cases hf : f.val < (S t).products
    · simp only [gateVals, hp, hf, dite_true, gateValue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp [gateVals, hp, hf, gateValue]

private theorem sum_fin_lt (m n : ℕ) (hmn : m ≤ n) (f : Fin m → Fq P) :
    (∑ t : Fin n, if ht : t.val < m then f ⟨t.val, ht⟩ else 0) = ∑ t, f t := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Fin.sum_univ_add]
  have hn (t : Fin l) : ¬ m + t.val < m := by omega
  simp [hn]

theorem sum_gateValue (hS : InShape P S) (W : Mat (Fq P) P.N) (t : Fin P.gatesMax) :
    (∑ j : Fin P.U, gateValue S W t (Dm.place t j)) = MomentGate (S t) W := by
  classical
  rw [(Dm.place t).sum_comp]
  simp only [Fintype.sum_option, gateValue]
  rw [sum_fin_lt (P := P) _ _ (hS t)
    (fun f => ∑ i, ∑ j, (S t).left f i * W i j * (S t).right f j)]
  simp [MomentGate, sub_eq_add_neg, add_comm]

theorem Z0_col (hD : ValidQAP Dm S) (j : Fin (P.N + 1)) :
    Dm.Z0.eval (Dm.colPt j) = 0 := by
  rw [hD.Z0_eq]
  simp only [z0Poly, eval_mul, eval_prod]
  have hz : (∏ i, (X - C (Dm.colPt i) : Polynomial (Fq P)).eval (Dm.colPt j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  rw [hz, mul_zero]

theorem Z0_gate_ne (hD : ValidQAP Dm S) (t : Fin P.gatesMax) (j : Fin P.U) :
    Dm.Z0.eval (Dm.gatePoint t j) ≠ 0 := by
  have hc (i : Fin (P.N + 1)) : Dm.gatePoint t j ≠ Dm.colPt i := by
    intro he
    have hh := hD.distinct (a₁ := Sum.inr (Sum.inr (t, j))) (a₂ := Sum.inl i) he
    cases hh
  have hr : Dm.gatePoint t j ≠ Dm.rho := by
    intro he
    have hh := hD.distinct (a₁ := Sum.inr (Sum.inr (t, j)))
      (a₂ := Sum.inr (Sum.inl ())) he
    cases hh
  rw [hD.Z0_eq, z0Poly, eval_mul, eval_prod]
  apply mul_ne_zero
  · simpa using sub_ne_zero.mpr hr
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
      simpa only [eval_sub, eval_X, eval_C] using sub_ne_zero.mpr (hc i))

theorem full_product (hD : ValidQAP Dm S) :
    (∏ x : QAPIndex P, (X - C (Dm.point x))) = Dm.Z * (X - C Dm.rho) := by
  classical
  have hm : Dm.rho ∈ Dm.pointSet := Finset.mem_image.mpr ⟨rhoIndex, Finset.mem_univ _, rfl⟩
  rw [hD.Z_eq, zPoly, Finset.prod_erase_mul _ _ hm]
  rw [QAPData.pointSet, Finset.prod_image hD.distinct.injOn]

theorem full_eval (hD : ValidQAP Dm S) (x : QAPIndex P) :
    (Dm.Z * (X - C Dm.rho)).eval (Dm.point x) = 0 := by
  rw [← full_product hD, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp)

theorem supported_of_allowed {r : Polynomial (Fq P)} (hr : AllowedRem r) :
    ViewCosets.RemainderSupported P.U r := by
  intro e he hd
  exact (Polynomial.mem_support_iff.mp he) (hr.2 e hd)

theorem criterion_forward (hU : 0 < P.U) (hG : 0 < P.gatesMax)
    (hS : InShape P S) (hD : ValidQAP Dm S) (W : Mat (Fq P) P.N)
    (hb : ∀ i : Fin P.N, W i.succ i.succ = W 0 i.succ)
    (hg : ∀ t, MomentGate (S t) W = 0) : QAPCriterion Dm W := by
  classical
  letI : NeZero P.U := ⟨Nat.ne_of_gt hU⟩
  have hmu : IsPrimitiveRoot Dm.mu P.U := IsPrimitiveRoot.iff_orderOf.mpr hD.mu_order
  have hNodes : Function.Injective (fun x : Fin P.gatesMax × Fin P.U =>
      Dm.delta x.1 * Dm.mu ^ x.2.val) := by
    intro x y he
    exact Sum.inr.inj (Sum.inr.inj (hD.distinct
      (a₁ := Sum.inr (Sum.inr x)) (a₂ := Sum.inr (Sum.inr y)) he))
  obtain ⟨rem, hdeg, hs, hrem⟩ := ViewInterpolation.exists_supported_remainder
    hmu hmu.neZero'.out Dm.delta hNodes
    (fun x => gateValue S W x.1 (Dm.place x.1 x.2))
    (fun t => by rw [sum_gateValue hS W t]; exact hg t)
  let p := Dm.qapPoly W - C (W 0 0) * Dm.Lrho - Dm.Z0 * rem
  have hp : ∀ x : QAPIndex P, p.eval (Dm.point x) = 0 := by
    intro x
    rcases x with j | (_ | ⟨t, j⟩)
    · have hq : (Dm.qapPoly W).eval (Dm.colPt j) = 0 := by
        refine Fin.cases (qap_col_zero hD W) (fun i => ?_) j
        rw [qap_col hD W i.succ (Fin.succ_ne_zero i), hb, sub_self]
      have hl := hD.Lrho_eval (Sum.inl j)
      simp only [QAPData.point, rhoIndex, Sum.inl_ne_inr, if_false] at hl
      simpa [p, QAPData.point, hq, Z0_col hD, hl]
    · have hl := hD.Lrho_eval (rhoIndex (P := P))
      simp only [rhoIndex, QAPData.point, if_true] at hl
      simp [p, QAPData.point, qap_rho hD W, hD.Z0_eq, z0Poly, hl]
    · have hl := hD.Lrho_eval (Sum.inr (Sum.inr (t, j)))
      simp only [QAPData.point, rhoIndex, Sum.inr.injEq, Sum.inr_ne_inl, if_false] at hl
      have hr : rem.eval (Dm.gatePoint t j) = gateValue S W t (Dm.place t j) := hrem (t, j)
      simp [p, QAPData.point, qap_gate hD W, hr, hl]
  have hdvd := ViewInterpolation.product_linear_dvd Finset.univ Dm.point hD.distinct p
    (by intro x _; exact hp x)
  rw [full_product hD] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, rem, ?_, ?_, ?_⟩
  · dsimp [p] at hq
    linear_combination hq
  · by_cases hz : rem = 0
    · simp [hz, Nat.mul_pos hU hG]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by simpa using hdeg)
  · intro e he
    by_contra hn
    exact hs e (Polynomial.mem_support_iff.mpr hn) he

theorem criterion_backward (hS : InShape P S) (hD : ValidQAP Dm S)
    (W : Mat (Fq P) P.N) (hc : QAPCriterion Dm W) :
    (∀ i : Fin P.N, W i.succ i.succ = W 0 i.succ) ∧
      ∀ t, MomentGate (S t) W = 0 := by
  classical
  obtain ⟨q, rem, he, hr⟩ := hc
  have hmu : IsPrimitiveRoot Dm.mu P.U := IsPrimitiveRoot.iff_orderOf.mpr hD.mu_order
  constructor
  · intro i
    have hx := congrArg (Polynomial.eval (Dm.colPt i.succ)) he
    have hl := hD.Lrho_eval (Sum.inl i.succ)
    simp only [QAPData.point, rhoIndex, Sum.inl_ne_inr, if_false] at hl
    have hz := full_eval hD (Sum.inl i.succ)
    simp only [QAPData.point] at hz
    simp only [eval_sub, eval_add, eval_mul, eval_C, qap_col hD W _ (Fin.succ_ne_zero i),
      hl, hz, Z0_col hD, mul_zero, sub_zero, zero_mul, add_zero] at hx
    exact sub_eq_zero.mp hx
  · intro t
    have hv (j : Fin P.U) : gateValue S W t (Dm.place t j) =
        rem.eval (Dm.gatePoint t j) := by
      have hx := congrArg (Polynomial.eval (Dm.gatePoint t j)) he
      have hl := hD.Lrho_eval (Sum.inr (Sum.inr (t, j)))
      simp only [QAPData.point, rhoIndex, Sum.inr.injEq, Sum.inr_ne_inl, if_false] at hl
      have hz := full_eval hD (Sum.inr (Sum.inr (t, j)))
      simp only [QAPData.point] at hz
      simp only [eval_sub, eval_add, eval_mul, eval_C, qap_gate hD W, hl, hz,
        mul_zero, sub_zero, zero_add] at hx
      exact mul_left_cancel₀ (Z0_gate_ne hD t j) hx
    calc
      MomentGate (S t) W = ∑ j : Fin P.U, gateValue S W t (Dm.place t j) :=
        (sum_gateValue (Dm := Dm) hS W t).symm
      _ = ∑ j : Fin P.U, rem.eval (Dm.gatePoint t j) := Finset.sum_congr rfl (fun j _ => hv j)
      _ = 0 := ViewCosets.remainder_coset_sum_zero hmu rem (supported_of_allowed hr) (Dm.delta t)

end Praxis.Proofs.QAP
