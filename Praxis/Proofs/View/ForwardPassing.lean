import Praxis.Proofs.View.ForwardLines
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.View.ForwardCells
import Praxis.Proofs.View.ForwardLinear
import Praxis.Proofs.View.ForwardMain
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open Polynomial

set_option maxRecDepth 2048

lemma chunk_exp_lt {B M a j : ℕ} (ha : a < B) (hj : j < M) : a + B*j < B*M := by
  calc
    a + B*j < B + B*j := Nat.add_lt_add_right ha _
    _ = B*(j+1) := by ring
    _ ≤ B*M := Nat.mul_le_mul_left B hj

section Degrees

variable {P : Params} [Fact (Nat.Prime P.q)]

lemma hC_degree_le (E : ExprT P) (σ : Sector) (cl : Cell P) :
    (hC E σ cl).natDegree ≤ P.E1 * P.Mq := by
  apply natDegree_sum_le_of_forall_le
  intro a _
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt (chunk_exp_lt a.isLt j.isLt))

lemma RC_degree_pred (E : ExprT P) (σ : Sector) (cl : Cell P) :
    (RC E σ cl).natDegree ≤ P.U * P.E1p * P.Wr - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro a _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply (natDegree_monomial_le _).trans
  have hh := chunk_exp_lt a.1.isLt j.isLt
  omega

lemma RC_degree_le (E : ExprT P) (σ : Sector) (cl : Cell P) :
    (RC E σ cl).natDegree ≤ P.U * P.E1p * P.Wr :=
  (RC_degree_pred E σ cl).trans (Nat.sub_le _ _)

lemma RC_allowed (E : ExprT P) (σ : Sector) (cl : Cell P)
    (hcover : P.E1p * P.Wr = P.gatesMax) (hpos : 0 < P.U * P.gatesMax) : AllowedRem (RC E σ cl) := by
  constructor
  · have hd := RC_degree_pred E σ cl
    have hb : P.U * P.E1p * P.Wr = P.U * P.gatesMax := by rw [Nat.mul_assoc, hcover]
    rw [hb] at hd
    omega
  · intro k hk
    simp only [RC, finsetSum_coeff, coeff_monomial]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with he
    · exfalso
      rw [← he] at hk
      have hm := Nat.mod_eq_zero_of_dvd hk
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
        Nat.add_zero, Nat.mod_mod] at hm
      exact a.2 (Nat.dvd_of_mod_eq_zero hm)
    · rfl

lemma Z0_degree_le (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S) :
    Dm.Z0.natDegree ≤ P.N + 2 := by
  rw [hD.Z0_eq, z0Poly]
  have hp : (∏ j : Fin (P.N+1), (X - C (Dm.colPt j) : Polynomial (Fq P))).natDegree ≤ P.N+1 := by
    simpa using Polynomial.natDegree_prod_le Finset.univ (fun j : Fin (P.N+1) => (X - C (Dm.colPt j) : Polynomial (Fq P)))
  apply natDegree_mul_le.trans
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using add_le_add (show (X-C Dm.rho : Polynomial (Fq P)).natDegree ≤ 1 by simp) hp

lemma zCell_degree_le (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (hsize : Fintype.card (QAPIndex P) = P.D) (cl : Cell P) :
    (Dm.zCell cl).natDegree ≤ P.D := by
  have hz := Z_degree Dm S hD hsize
  unfold QAPData.zCell
  split_ifs
  · apply natDegree_mul_le.trans
    have hx : (X - C Dm.rho : Polynomial (Fq P)).natDegree = 1 := by simp
    rw [hx]
    omega
  · exact Nat.le_of_lt hz

lemma qapPoly_degree_le (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (W : Mat (Fq P) P.N) : (Dm.qapPoly W).natDegree ≤ 2*P.D := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_mul_le.trans
  have ha := (natDegree_C_mul_le (W i j) (Dm.A i)).trans (Nat.le_of_lt (hD.A_degree i))
  have hb := Nat.le_of_lt (hD.B_degree j)
  omega

lemma cellPolynomial_degree_le (pp : PublicParams P) (S : Relation P) (hD : ValidQAP pp.qap S)
    (hsize : Fintype.card (QAPIndex P) = P.D) (E : ExprT P) (σ : Sector) (cl : Cell P) (ι : Fq P) :
    (pp.qap.qapPoly (aC E σ cl) + hC E σ cl * pp.qap.zCell cl + pp.qap.Z0 * RC E σ cl -
      (if IsKeyCell cl then C ι * pp.qap.Lrho else 0)).natDegree ≤
      4*P.D + P.E1*P.Mq + P.U*P.E1p*P.Wr + P.N+2 := by
  have hq := qapPoly_degree_le pp.qap S hD (aC E σ cl)
  have hh := (natDegree_mul_le (p := hC E σ cl) (q := pp.qap.zCell cl)).trans
    (add_le_add (hC_degree_le E σ cl) (zCell_degree_le pp.qap S hD hsize cl))
  have hr := (natDegree_mul_le (p := pp.qap.Z0) (q := RC E σ cl)).trans
    (add_le_add (Z0_degree_le pp.qap S hD) (RC_degree_le E σ cl))
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      exact max_le (by omega) (by omega)
    · omega
  · split_ifs
    · exact (natDegree_C_mul_le _ _).trans (by have hd := hD.Lrho_degree; omega)
    · simp

end Degrees

lemma cell_polynomial_identity {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P) (S : Relation P) (hD : ValidQAP pp.qap S)
    (hsize : Fintype.card (QAPIndex P) = P.D)
    (hsmall : P.D < P.q-P.D)
    (hbound : 4*P.D + P.E1*P.Mq + P.U*P.E1p*P.Wr + P.N+2 < P.q-P.D)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (ι : Fq P)
    (h : ∀ y τ, (∀ k, τ ≠ pp.qap.point k) → ∀ cl,
      braceVal pp r E σ cl y τ = if IsKeyCell cl then ι * pp.qap.Lrho.eval τ else 0)
    (cl : Cell P) :
    pp.qap.qapPoly (aC E σ cl) + hC E σ cl * pp.qap.zCell cl + pp.qap.Z0 * RC E σ cl =
      if IsKeyCell cl then C ι * pp.qap.Lrho else 0 := by
  apply sub_eq_zero.mp
  apply tau_poly_zero pp.qap hsize
  · exact (cellPolynomial_degree_le pp S hD hsize E σ cl ι).trans_lt hbound
  · intro τ hτ
    have hh := h 0 τ hτ cl
    by_cases hk : IsKeyCell cl
    · simp only [braceVal, if_pos hk] at hh
      rw [cellForm_zero pp.qap (aC E σ cl) (sC E σ cl) r] at hh
      simp only [if_pos hk, eval_sub, eval_add, eval_mul, eval_C]
      linear_combination hh
    · simp only [braceVal, if_neg hk] at hh
      rw [cellForm_zero pp.qap (aC E σ cl) (sC E σ cl) r] at hh
      simp only [if_neg hk, eval_sub, eval_add, eval_mul, eval_zero]
      linear_combination hh

lemma cell_symm_search {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P) (S : Relation P) (hD : ValidQAP pp.qap S)
    (hsize : Fintype.card (QAPIndex P) = P.D)
    (hsmall : P.D < P.q-P.D)
    (hbound : 4*P.D + P.E1*P.Mq + P.U*P.E1p*P.Wr + P.N+2 < P.q-P.D)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (ι : Fq P)
    (h : ∀ y τ, (∀ k, τ ≠ pp.qap.point k) → ∀ cl,
      braceVal pp r E σ cl y τ = if IsKeyCell cl then ι * pp.qap.Lrho.eval τ else 0)
    (cl : Cell P) : Matrix.IsSymm (aC E σ cl) ∧ Matrix.mulVec (aC E σ cl) r = -sC E σ cl := by
  apply symm_search_of_cellForm pp.qap S hD hsize hsmall
    (aC E σ cl) (sC E σ cl) r
    (fun τ => (pp.qap.zCell cl).eval τ * (hC E σ cl).eval τ +
      pp.qap.Z0.eval τ * (RC E σ cl).eval τ -
      (if IsKeyCell cl then ι * pp.qap.Lrho.eval τ else 0))
  intro y τ hτ
  have hh := h y τ hτ cl
  unfold braceVal at hh
  linear_combination hh

lemma cells_pass {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    (S : Relation P) (hD : ValidQAP pp.qap S)
    (hcrit : ∀ W : Mat (Fq P) P.N, W.IsSymm → (Passes S W ↔ QAPCriterion pp.qap W))
    (hsize : Fintype.card (QAPIndex P) = P.D)
    (hsmall : P.D < P.q-P.D)
    (hbound : 4*P.D + P.E1*P.Mq + P.U*P.E1p*P.Wr + P.N+2 < P.q-P.D)
    (hcover : P.E1p*P.Wr = P.gatesMax) (hpos : 0 < P.U*P.gatesMax)
    (r : Vec (Fq P) P.N) (E : ExprT P) (σ : Sector) (ι : Fq P)
    (h : ∀ y τ, (∀ k, τ ≠ pp.qap.point k) → ∀ cl,
      braceVal pp r E σ cl y τ = if IsKeyCell cl then ι * pp.qap.Lrho.eval τ else 0)
    (cl : Cell P) : Passes S (aC E σ cl) ∧ (IsKeyCell cl → aC E σ cl 0 0 = ι) := by
  have hs := cell_symm_search pp S hD hsize hsmall hbound r E σ ι h cl
  exact passes_of_cellIdentity pp.qap S hD hsize (aC E σ cl)
    (hcrit _ hs.1) cl ι (hC E σ cl) (RC E σ cl)
    (RC_allowed _ _ _ hcover hpos) (cell_polynomial_identity pp S hD hsize hsmall hbound r E σ ι h cl)

end Praxis.Proofs.View
