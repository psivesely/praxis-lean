import Praxis.Proofs.View.ForwardSeparation
import Mathlib.Data.Fintype.Sum
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Stack

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot e0)

open Polynomial

set_option maxRecDepth 2048

lemma qapIndex_card : Fintype.card (QAPIndex P0) = P0.D := by
  change Fintype.card (Fin (P0.N+1) ⊕ (Unit ⊕ (Fin P0.gatesMax × Fin P0.U))) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod]
  simp only [Fintype.card_fin, Fintype.card_unit]
  rfl

section Generic

variable {P : Params} [Fact (Nat.Prime P.q)]

lemma tau_poly_zero (Dm : QAPData P) (hsize : Fintype.card (QAPIndex P) = P.D) (p : Polynomial (Fq P))
    (hd : p.natDegree < P.q - P.D)
    (h : ∀ τ, (∀ k, τ ≠ Dm.point k) → p.eval τ = 0) : p = 0 := by
  classical
  let bad := Finset.univ.image Dm.point
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (Finset.univ \ bad)
  · intro τ hτ
    apply h τ
    intro k hk
    exact (Finset.mem_sdiff.mp hτ).2 (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩)
  · have hb : bad.card ≤ P.D := by
      exact (Finset.card_image_le).trans_eq (by rw [Finset.card_univ, hsize])
    have hg : P.q - P.D ≤ (Finset.univ \ bad).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ bad)]
      simpa only [Finset.card_univ, ZMod.card] using Nat.sub_le_sub_left hb P.q
    exact hd.trans_le hg

lemma B_indep (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (f : Fin (P.N + 1) → Fq P) (h : ∑ j, C (f j) * Dm.B j = 0) : f = 0 := by
  classical
  ext i
  have hh := congrArg (fun p : Polynomial (Fq P) => p.eval (Dm.colPt i)) h
  simpa [eval_finsetSum, hD.B_col, mul_ite] using hh

lemma A_indep (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (c : Fq P) (f : Fin (P.N + 1) → Fq P)
    (h : C c + ∑ j, C (f j) * Dm.A j = 0) : c = 0 ∧ f = 0 := by
  classical
  have hc : c = 0 := by
    have hh := congrArg (fun p : Polynomial (Fq P) => p.eval (Dm.colPt 0)) h
    simpa [eval_finsetSum, hD.A_col] using hh
  have hf0 : f 0 = 0 := by
    have hh := congrArg (fun p : Polynomial (Fq P) => p.eval Dm.rho) h
    simpa [eval_finsetSum, hD.A_rho, e0, mul_ite, hc] using hh
  refine ⟨hc, ?_⟩
  ext i
  by_cases hi : i = 0
  · simpa [hi] using hf0
  have hh := congrArg (fun p : Polynomial (Fq P) => p.eval (Dm.colPt i)) h
  simp only [eval_add, eval_C, eval_finsetSum, eval_mul, hD.A_col, if_neg hi,
    hc, zero_add, eval_zero] at hh
  have he (j : Fin (P.N + 1)) :
      f j * (if j = i then 1 else if j = 0 then -1 else 0) =
        (if j = i then f j else 0) - (if j = 0 then f j else 0) := by
    by_cases hji : j = i
    · subst j
      simp [hi]
    · by_cases hj : j = 0 <;> simp [hji, hj, Ne.symm hi]
  simp only [he, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hf0, sub_zero] at hh
  exact hh

lemma quad_odd (M : Mat (Fq P) P.N) (b : Vec (Fq P) P.N) (htwo : (2 : Fq P) ≠ 0)
    (h : ∀ y : Vec (Fq P) P.N, ∑ i, ∑ j, M i j * y i * (b j - y j) = 0)
    (i : Fin (P.N + 1)) : ∑ j, M i j * b j = 0 := by
  classical
  have hp := h (Pi.single i 1)
  have hn := h (-Pi.single i 1)
  simp only [Pi.single_apply, Pi.neg_apply, mul_ite, mul_one, mul_zero, mul_sub,
    mul_neg, neg_mul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    neg_neg] at hp hn
  apply (mul_eq_zero.mp (show (2 : Fq P) * (∑ j, M i j * b j) = 0 by
    linear_combination hp - hn)).resolve_left htwo

lemma qapPoly_rho (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (W : Mat (Fq P) P.N) : (Dm.qapPoly W).eval Dm.rho = W 0 0 := by
  classical
  simp [QAPData.qapPoly, eval_finsetSum, hD.A_rho, hD.B_rho, e0, mul_ite]

lemma Z0_rho (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S) :
    Dm.Z0.eval Dm.rho = 0 := by
  simp [hD.Z0_eq, z0Poly]

lemma Z_rho_ne_zero (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S) :
    Dm.Z.eval Dm.rho ≠ 0 := by
  classical
  rw [hD.Z_eq]
  simp only [zPoly, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hp).symm

lemma Z_point (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (k : QAPIndex P) (hk : k ≠ rhoIndex) : Dm.Z.eval (Dm.point k) = 0 := by
  classical
  have hkr : Dm.point k ≠ Dm.rho := by
    intro hh
    exact hk (hD.distinct (a₁ := k) (a₂ := rhoIndex) hh)
  rw [hD.Z_eq]
  simp only [zPoly, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_eq_zero (i := Dm.point k)
  · exact Finset.mem_erase.mpr ⟨hkr, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
  · exact sub_self _

lemma Z_degree (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (hsize : Fintype.card (QAPIndex P) = P.D) :
    Dm.Z.natDegree < P.D := by
  classical
  rw [hD.Z_eq]
  have hr : Dm.rho ∈ Dm.pointSet := Finset.mem_image.mpr ⟨rhoIndex, Finset.mem_univ _, rfl⟩
  have hc : Dm.pointSet.card = P.D := by
    rw [QAPData.pointSet, Finset.card_image_of_injective _ hD.distinct]
    simp [hsize]
  have hd := Polynomial.natDegree_prod_le (Dm.pointSet.erase Dm.rho)
    (fun p => (X - C p : Polynomial (Fq P)))
  have hb : (zPoly Dm.pointSet Dm.rho).natDegree ≤ P.D - 1 := by
    simpa [zPoly, Finset.card_erase_of_mem hr, hc] using hd
  apply hb.trans_lt
  have hpos : 0 < P.D := by
    rw [← hsize]
    exact Fintype.card_pos_iff.mpr ⟨rhoIndex⟩
  omega

lemma Lrho_eq_normalized_Z (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (hsize : Fintype.card (QAPIndex P) = P.D) :
    Dm.Lrho = C (Dm.Z.eval Dm.rho)⁻¹ * Dm.Z := by
  classical
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hD.distinct
  · intro k
    by_cases hk : k = rhoIndex
    · subst k
      change Dm.Lrho.eval Dm.rho = _
      have hL : Dm.Lrho.eval Dm.rho = 1 := by simpa only [QAPData.point, rhoIndex, ite_true] using hD.Lrho_eval rhoIndex
      simp [QAPData.point, rhoIndex, hL, Z_rho_ne_zero Dm S hD]
    · simp [hD.Lrho_eval, hk, Z_point Dm S hD k hk]
  · rw [hsize]
    apply max_lt hD.Lrho_degree
    exact (natDegree_C_mul_le _ _).trans_lt (Z_degree Dm S hD hsize)

lemma allowedRem_neg {P : Params} (R : Polynomial (Fq P)) (hR : AllowedRem R) : AllowedRem (-R) := by
  exact ⟨by simpa using hR.1, fun k hk => by simp [hR.2 k hk]⟩

lemma cell_algebra (D : QAPData P) (M : Mat (Fq P) P.N) (a : Vec (Fq P) P.N) (r : Vec (Fq P) P.N) (yv : Fin (P.N + 1) → (Fq P)) :
    (∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1), Polynomial.C (M i j) *
        (Polynomial.C (yv i) * (Polynomial.C (r j) + D.A j) +
          D.A i * (D.B j - Polynomial.C (yv j)))) +
      ∑ i : Fin (P.N + 1), Polynomial.C (yv i) * Polynomial.C (a i) =
    (∑ i, Polynomial.C (yv i) * (Polynomial.C (M.mulVec r i + a i) +
        ∑ j, Polynomial.C (M i j - M j i) * D.A j)) + D.qapPoly M := by
  have swap : ∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1),
      Polynomial.C (M i j) * D.A i * Polynomial.C (yv j) =
      ∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1),
        Polynomial.C (yv i) * (Polynomial.C (M j i) * D.A j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e1 : (∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1), Polynomial.C (M i j) *
        (Polynomial.C (yv i) * (Polynomial.C (r j) + D.A j) +
          D.A i * (D.B j - Polynomial.C (yv j)))) =
      (∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1),
        (Polynomial.C (yv i) * (Polynomial.C (M i j) * Polynomial.C (r j) +
          Polynomial.C (M i j) * D.A j) + Polynomial.C (M i j) * D.A i * D.B j)) -
      ∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1),
        Polynomial.C (M i j) * D.A i * Polynomial.C (yv j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : (∑ i, Polynomial.C (yv i) * (Polynomial.C (M.mulVec r i + a i) +
        ∑ j, Polynomial.C (M i j - M j i) * D.A j)) + D.qapPoly M =
      ((∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1),
        (Polynomial.C (yv i) * (Polynomial.C (M i j) * Polynomial.C (r j) +
          Polynomial.C (M i j) * D.A j) + Polynomial.C (M i j) * D.A i * D.B j)) -
      ∑ i : Fin (P.N + 1), ∑ j : Fin (P.N + 1),
        Polynomial.C (yv i) * (Polynomial.C (M j i) * D.A j)) +
      ∑ i : Fin (P.N + 1), Polynomial.C (yv i) * Polynomial.C (a i) := by
    simp only [QAPData.qapPoly, Matrix.mulVec, dotProduct, map_add, map_sum, map_sub, map_mul,
      mul_add, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  rw [e1, e2, swap]

end Generic

lemma passes_of_cellIdentity {P : Params} [Fact (Nat.Prime P.q)]
    (Dm : QAPData P) (S : Relation P) (hD : ValidQAP Dm S)
    (hsize : Fintype.card (QAPIndex P) = P.D) (W : Mat (Fq P) P.N)
    (hcrit : Passes S W ↔ QAPCriterion Dm W) (cl : Cell P)
    (ι : Fq P) (h R : Polynomial (Fq P)) (hR : AllowedRem R)
    (hid : Dm.qapPoly W + h * Dm.zCell cl + Dm.Z0 * R =
      if IsKeyCell cl then C ι * Dm.Lrho else 0) :
    Passes S W ∧ (IsKeyCell cl → W 0 0 = ι) := by
  classical
  have hρ := congrArg (fun p : Polynomial (Fq P) => p.eval Dm.rho) hid
  have hLρ : Dm.Lrho.eval Dm.rho = 1 := by simpa [QAPData.point, rhoIndex] using hD.Lrho_eval rhoIndex
  by_cases hk : IsKeyCell cl
  · have hcorner : W 0 0 = ι := by
      simpa [qapPoly_rho Dm S hD, QAPData.zCell, hk, Z0_rho Dm S hD, hLρ] using hρ
    refine ⟨hcrit.mpr ?_, fun _ => hcorner⟩
    refine ⟨-h, -R, ?_, allowedRem_neg R hR⟩
    rw [hcorner]
    simp only [QAPData.zCell, if_pos hk] at hid
    linear_combination hid
  · have hcorner : W 0 0 = -(h.eval Dm.rho) * Dm.Z.eval Dm.rho := by
      simp only [qapPoly_rho Dm S hD, eval_add, eval_mul, QAPData.zCell, if_neg hk,
        Z0_rho Dm S hD, zero_mul, add_zero, eval_zero] at hρ
      linear_combination hρ
    obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := h) (a := Dm.rho)
    refine ⟨hcrit.mpr ?_, fun hh => (hk hh).elim⟩
    refine ⟨-g, -R, ?_, allowedRem_neg R hR⟩
    rw [Lrho_eq_normalized_Z Dm S hD hsize, hcorner]
    simp only [QAPData.zCell, if_neg hk] at hid
    have he : C ((-(h.eval Dm.rho) * Dm.Z.eval Dm.rho)) *
        (C (Dm.Z.eval Dm.rho)⁻¹ * Dm.Z) = -C (h.eval Dm.rho) * Dm.Z := by
      rw [map_mul, map_neg, mul_assoc, ← mul_assoc (C (Dm.Z.eval Dm.rho)), ← map_mul,
        mul_inv_cancel₀ (Z_rho_ne_zero Dm S hD), map_one, one_mul]
    rw [he]
    linear_combination hid - Dm.Z * hg

end Praxis.Proofs.View
