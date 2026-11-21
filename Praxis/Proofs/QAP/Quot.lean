import Praxis.Proofs.QAP.Criterion
import Praxis.Algebra.ViewMixing.RemainderInterpolation
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.QAP

open Praxis.Algebra (Vec)

private theorem z_dvd_Lrho {P : Params} [Fact (Nat.Prime P.q)] (S : Relation P) (Dm : QAPData P)
    (hD : ValidQAP Dm S) : Dm.Z ∣ Dm.Lrho := by
  classical
  rw [hD.Z_eq]
  unfold zPoly
  apply ViewInterpolation.product_linear_dvd _ id (Function.injective_id) _
  intro p hp
  have hp' := (Finset.mem_erase.mp hp)
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hp'.2
  have hne : k ≠ rhoIndex := by
    intro he
    apply hp'.1
    simpa [he, QAPData.point, rhoIndex] using hk.symm
  simpa [hk, hne] using hD.Lrho_eval k

private theorem witness_passes {P : Params} [Fact (Nat.Prime P.q)] (S : Relation P) (x : Vec (Fq P) P.N)
    (hx : IsWitness S x) : Passes S (fun i j => x i * x j) := by
  obtain ⟨hx0, hb, hg⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    exact mul_comm _ _
  · intro j
    rcases hb j with h | h <;> simp [h, hx0]
  · intro t
    unfold Algebra.MomentGate
    rw [sub_eq_zero]
    have h := hg t
    unfold Algebra.dot at h
    simp only [Finset.sum_mul, Finset.mul_sum] at h ⊢
    have h' : (∑ j, ∑ i, ∑ k, (S t).left j i * x i *
        ((S t).right j k * x k)) = ∑ k, x 0 * ((S t).linear k * x k) := by
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    convert h' using 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk
      ring
    · ring

private theorem outer_qap {P : Params} [Fact (Nat.Prime P.q)] (Dm : QAPData P) (x : Vec (Fq P) P.N) :
    Dm.qapPoly (fun i j => x i * x j) = Dm.Ax x * Dm.Bx x := by
  classical
  unfold QAPData.qapPoly QAPData.Ax QAPData.Bx
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.C_mul]
  ring

private theorem z_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S) :
    Dm.Z.natDegree = P.N + 1 + P.gatesMax * P.U := by
  classical
  have hrho : Dm.rho ∈ Dm.pointSet := by
    apply Finset.mem_image.mpr
    exact ⟨rhoIndex, Finset.mem_univ _, rfl⟩
  rw [hD.Z_eq]
  unfold zPoly
  rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_erase_of_mem hrho, QAPData.pointSet,
    Finset.card_image_of_injective _ hD.distinct]
  simp only [Finset.card_univ, QAPIndex, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit, Fintype.card_prod]
  omega

private theorem z0_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S) :
    Dm.Z0.natDegree = P.N + 2 := by
  classical
  rw [hD.Z0_eq]
  unfold z0Poly
  rw [(Polynomial.monic_X_sub_C _).natDegree_mul (Polynomial.monic_prod_X_sub_C _ _)]
  simp
  omega

private theorem qap_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S)
    (W : Algebra.Mat (Fq P) P.N) : (Dm.qapPoly W).natDegree ≤ 2 * (P.D - 1) := by
  classical
  unfold QAPData.qapPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  have h := Polynomial.natDegree_mul_le (p := Polynomial.C (W i j) * Dm.A i) (q := Dm.B j)
  have ha := Polynomial.natDegree_C_mul_le (W i j) (Dm.A i)
  have hi := hD.A_degree i
  have hj := hD.B_degree j
  omega

private theorem quotient_degree {F : Type*} [Field F] (p z a h : Polynomial F) (D : ℕ)
    (hD : 0 < D) (hz : z ≠ 0) (hzdeg : D - 1 ≤ z.natDegree)
    (hp : p.natDegree ≤ 2 * (D - 1)) (ha : a.natDegree ≤ 2 * (D - 1))
    (heq : p = h * z + a) : h.natDegree < D := by
  by_cases hh : h = 0
  · simp [hh, hD]
  · have he : h * z = p - a := by linear_combination -heq
    have hle : (h * z).natDegree ≤ 2 * (D - 1) := by
      rw [he]
      exact (Polynomial.natDegree_sub_le _ _).trans (max_le hp ha)
    rw [Polynomial.natDegree_mul hh hz] at hle
    omega

private theorem cell_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S)
    (hsize : P.D = P.N + 2 + P.U * P.gatesMax)
    (hcover : P.D ≤ P.E1 * P.Mq) (W : Stack P) (c : Cell P)
    (h R : Polynomial (Fq P)) (hR : AllowedRem R)
    (heq : Dm.qapPoly (W c) - (if IsKeyCell c then Polynomial.C (W c 0 0) * Dm.Lrho else 0) =
      h * Dm.zCell c + Dm.Z0 * R) : h.natDegree < P.E1 * P.Mq := by
  classical
  rw [Nat.mul_comm P.U P.gatesMax] at hsize
  have hpD : 0 < P.D := by omega
  have hzmon : Dm.Z.Monic := by
    rw [hD.Z_eq]
    exact Polynomial.monic_prod_X_sub_C _ _
  have hzcmon : (Dm.zCell c).Monic := by
    unfold QAPData.zCell
    split_ifs
    · exact hzmon.mul (Polynomial.monic_X_sub_C _)
    · exact hzmon
  have hzdeg : P.D - 1 ≤ (Dm.zCell c).natDegree := by
    have hz := z_degree S Dm hD
    unfold QAPData.zCell
    split_ifs
    · rw [hzmon.natDegree_mul (Polynomial.monic_X_sub_C _), Polynomial.natDegree_X_sub_C]
      omega
    · omega
  have hp : (Dm.qapPoly (W c) - (if IsKeyCell c then Polynomial.C (W c 0 0) * Dm.Lrho else 0)).natDegree ≤
      2 * (P.D - 1) := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le (qap_degree S Dm hD (W c))
    split_ifs
    · have ht := Polynomial.natDegree_C_mul_le (W c 0 0) Dm.Lrho
      have hl := hD.Lrho_degree
      omega
    · simp
  have ha : (Dm.Z0 * R).natDegree ≤ 2 * (P.D - 1) := by
    have hm := Polynomial.natDegree_mul_le (p := Dm.Z0) (q := R)
    have hz := z0_degree S Dm hD
    have hr := hR.1
    rw [Nat.mul_comm P.U P.gatesMax] at hr
    omega
  have hh := quotient_degree _ _ _ _ P.D hpD hzcmon.ne_zero hzdeg hp ha heq
  omega

private theorem cell_of_criterion {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S)
    (hsize : P.D = P.N + 2 + P.U * P.gatesMax)
    (hcover : P.D ≤ P.E1 * P.Mq) (W : Stack P) (c : Cell P)
    (hc : QAPCriterion Dm (W c)) : ∃ h R, CellQuotient Dm W c h R := by
  obtain ⟨h, R, hq, hR⟩ := hc
  by_cases hk : IsKeyCell c
  · have he : Dm.qapPoly (W c) - (if IsKeyCell c then Polynomial.C (W c 0 0) * Dm.Lrho else 0) =
        h * Dm.zCell c + Dm.Z0 * R := by
      simpa [QAPData.zCell, hk] using hq
    exact ⟨h, R, he, hR, cell_degree S Dm hD hsize hcover W c h R hR he⟩
  · obtain ⟨l, hl⟩ := z_dvd_Lrho S Dm hD
    let h' := h * (Polynomial.X - Polynomial.C Dm.rho) + Polynomial.C (W c 0 0) * l
    have he : Dm.qapPoly (W c) - (if IsKeyCell c then Polynomial.C (W c 0 0) * Dm.Lrho else 0) =
        h' * Dm.zCell c + Dm.Z0 * R := by
      simp only [QAPData.zCell, hk, if_false]
      rw [hl] at hq
      dsimp [h']
      linear_combination hq
    exact ⟨h', R, he, hR, cell_degree S Dm hD hsize hcover W c h' R hR he⟩

private theorem honest_of_criterion {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S)
    (x : Vec (Fq P) P.N) (hx : IsWitness S x)
    (hcrit : QAPCriterion Dm (fun i j => x i * x j)) :
    ∃ hk ho R, HonestQuotient Dm x hk ho R := by
  obtain ⟨hk, R, hq, hR⟩ := hcrit
  obtain ⟨l, hl⟩ := z_dvd_Lrho S Dm hD
  have hx0 : x 0 = 1 := hx.1
  rw [outer_qap] at hq
  simp only [hx0, mul_one, Polynomial.C_1, one_mul] at hq
  refine ⟨hk, hk * (Polynomial.X - Polynomial.C Dm.rho) + l, R, hq, ?_, hR⟩
  rw [hl] at hq
  linear_combination hq

set_option maxRecDepth 8192 in

theorem cellQuotient_exists (S : Relation P0) (hS : InShape P0 S) (Dm : QAPData P0)
    (hD : ValidQAP Dm S) (W : Stack P0) (c : Cell P0) (hc : Passes S (W c)) :
    ∃ h R, CellQuotient Dm W c h R := by
  have hsize : P0.D = P0.N + 2 + P0.U * P0.gatesMax := by decide
  have hcover : P0.D ≤ P0.E1 * P0.Mq := by decide
  exact cell_of_criterion S Dm hD hsize hcover W c ((qap_criterion S hS Dm hD _ hc.1).mp hc)

set_option maxRecDepth 8192 in

theorem honestQuotient_exists (S : Relation P0) (hS : InShape P0 S) (Dm : QAPData P0)
    (hD : ValidQAP Dm S) (x : Vec (Fq P0) P0.N) (hx : IsWitness S x) :
    ∃ hk ho R, HonestQuotient Dm x hk ho R := by
  exact honest_of_criterion S Dm hD x hx
    ((qap_criterion S hS Dm hD _ (witness_passes S x hx).1).mp (witness_passes S x hx))

end Praxis.Proofs.QAP
