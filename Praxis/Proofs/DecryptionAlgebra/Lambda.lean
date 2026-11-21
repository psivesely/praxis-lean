import Praxis.Proofs.DecryptionAlgebra.Psi
import Praxis.Proofs.View.NoKey
import Praxis.Proofs.Ties.Origin
import Praxis.Proofs.QAP.Quot
import Praxis.Proofs.Rank1
import Praxis.Proofs.DecryptionAlgebra.Lambda.Chunks
import Praxis.Proofs.DecryptionAlgebra.Lambda.Compare
import Praxis.Dec
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.Ties.Honest
import Praxis.Proofs.View.Converse
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Relation
import Praxis.Scheme
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.DecryptionAlgebra

open Praxis.Algebra (Vec dot)

open Polynomial

private theorem chosen_honest_quotient (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (x : Vec (Fq P0) P0.N) (hx : IsWitness S x) :
    HonestQuotient (ppOf ch S).qap x ((honestQuot (ppOf ch S).qap x).1)
      ((honestQuot (ppOf ch S).qap x).2.1) ((honestQuot (ppOf ch S).qap x).2.2) := by
  classical
  obtain ⟨hk, ho, R, h⟩ := QAP.honestQuotient_exists S hS _
    (QAP.domainMap_valid ch S) x hx
  have he : ∃ t : Polynomial (Fq P0) × Polynomial (Fq P0) × Polynomial (Fq P0),
      HonestQuotient (ppOf ch S).qap x t.1 t.2.1 t.2.2 := ⟨(hk, ho, R), h⟩
  simpa only [honestQuot, dif_pos he] using Classical.choose_spec he

private theorem chosen_cell_quotient (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (W : Stack P0) (cl : Cell P0) (hW : Passes S (W cl)) :
    CellQuotient (ppOf ch S).qap W cl ((cellQuot (ppOf ch S).qap W cl).1)
      ((cellQuot (ppOf ch S).qap W cl).2) := by
  classical
  obtain ⟨h, R, hq⟩ := QAP.cellQuotient_exists S hS _ (QAP.domainMap_valid ch S) W cl hW
  have he : ∃ t : Polynomial (Fq P0) × Polynomial (Fq P0),
      CellQuotient (ppOf ch S).qap W cl t.1 t.2 := ⟨(h, R), hq⟩
  simpa only [cellQuot, dif_pos he] using Classical.choose_spec he

private theorem qap_honest {P : Params} [Fact (Nat.Prime P.q)]
    (Dm : QAPData P) (x : Vec (Fq P) P.N) (w : Fq P) :
    Dm.qapPoly (w • Matrix.vecMulVec x x) = C w * (Dm.Ax x * Dm.Bx x) := by
  classical
  unfold QAPData.qapPoly QAPData.Ax QAPData.Bx
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul]
  ring

private theorem key_weight {P : Params} (v : Fin P.n → Vec (Fq P) P.N)
    (x : Vec (Fq P) P.N) (cl : Cell P) (hc : IsKeyCell cl) :
    weight v x cl = wKey v x := by
  rcases hc with ⟨h₁, h₂, h₃⟩
  simp [weight, cellWeight, cellExp, legExp, wKey, h₁, h₂, h₃, LegKind.base]

private theorem key_filter {P : Params} [NeZero P.K1] [NeZero P.K2] :
    Finset.univ.filter (IsKeyCell (P := P)) = {keyCell} := by
  classical
  ext cl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    apply Prod.ext
    · apply Fin.ext; simpa [keyCell] using h₁
    · apply Prod.ext h₂
      apply Fin.ext; simpa [keyCell] using h₃
  · rintro rfl
    simp [IsKeyCell, keyCell]

private theorem honest_key_coeff {P : Params} [Fact (Nat.Prime P.q)]
    [NeZero P.K1] [NeZero P.K2]
    (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) (hx : x 0 = 1) :
    keyCoeff (honestStack v x) = wKey v x := by
  classical
  rw [keyCoeff, key_filter]
  simp only [Finset.sum_singleton, honestStack, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, hx, mul_one]
  exact key_weight v x keyCell (by simp [IsKeyCell, keyCell])

private theorem honest_cell_identity {P : Params} [Fact (Nat.Prime P.q)]
    (Dm : QAPData P) (v : Fin P.n → Vec (Fq P) P.N)
    (x : Vec (Fq P) P.N) (hk ho R : Polynomial (Fq P))
    (hq : HonestQuotient Dm x hk ho R) (cl : Cell P) :
    Dm.qapPoly (honestStack v x cl) -
        (if IsKeyCell cl then C (wKey v x) * Dm.Lrho else 0) =
      (if IsKeyCell cl then C (wKey v x) * hk else C (weight v x cl) * ho) *
        Dm.zCell cl + Dm.Z0 * (C (weight v x cl) * R) := by
  rw [honestStack, qap_honest]
  by_cases hc : IsKeyCell cl
  · simp only [hc, if_true, QAPData.zCell, key_weight v x cl hc]
    rw [← mul_sub, hq.1]
    ring
  · simp only [hc, if_false, sub_zero, QAPData.zCell]
    rw [hq.2.1]
    ring

private theorem z_monic {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S) :
    Dm.Z.Monic := by
  rw [hD.Z_eq]
  exact monic_prod_X_sub_C _ _

private theorem z_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S) :
    Dm.Z.natDegree = (P.N + 2 + P.gatesMax * P.U) - 1 := by
  classical
  have hrho : Dm.rho ∈ Dm.pointSet := by
    change Dm.point rhoIndex ∈ Finset.univ.image Dm.point
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hc : Dm.pointSet.card = P.N + 2 + P.gatesMax * P.U := by
    rw [QAPData.pointSet, Finset.card_image_iff.mpr hD.distinct.injOn]
    simp only [Finset.card_univ, QAPIndex, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_unit]
    omega
  rw [hD.Z_eq]
  simp only [zPoly]
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.card_erase_of_mem hrho, hc]
  norm_cast

private theorem z0_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S) :
    Dm.Z0.natDegree = P.N + 2 := by
  rw [hD.Z0_eq]
  unfold z0Poly
  rw [(monic_X_sub_C _).natDegree_mul (monic_prod_X_sub_C _ _)]
  simp
  omega

private theorem ax_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S)
    (x : Vec (Fq P) P.N) : (Dm.Ax x).natDegree ≤ P.D - 1 := by
  unfold QAPData.Ax
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (Nat.le_sub_one_of_lt (hD.A_degree i))

private theorem bx_degree {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S)
    (x : Vec (Fq P) P.N) : (Dm.Bx x).natDegree ≤ P.D - 1 := by
  unfold QAPData.Bx
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (Nat.le_sub_one_of_lt (hD.B_degree i))

private theorem honest_degrees {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (Dm : QAPData P) (hD : ValidQAP Dm S)
    (x : Vec (Fq P) P.N) (hk ho R : Polynomial (Fq P))
    (h : HonestQuotient Dm x hk ho R)
    (hshape : P.D = P.N + 2 + P.gatesMax * P.U) :
    hk.natDegree < P.D ∧ ho.natDegree < P.D := by
  have hDpos : 2 ≤ P.D := by rw [hshape]; omega
  have hz := z_degree S Dm hD
  rw [← hshape] at hz
  have hz0 := z0_degree S Dm hD
  have hprod : (Dm.Ax x * Dm.Bx x).natDegree ≤ 2 * (P.D - 1) := by
    have h : (Dm.Ax x * Dm.Bx x).natDegree ≤
        (Dm.Ax x).natDegree + (Dm.Bx x).natDegree := natDegree_mul_le
    have ha := ax_degree S Dm hD x
    have hb := bx_degree S Dm hD x
    omega
  have hzr : (Dm.Z0 * R).natDegree ≤ P.D - 1 := by
    have hr := h.2.2.1
    rw [Nat.mul_comm P.U P.gatesMax] at hr
    have hm : (Dm.Z0 * R).natDegree ≤ Dm.Z0.natDegree + R.natDegree := natDegree_mul_le
    rw [hz0] at hm
    rw [hshape]
    omega
  have hbig : ((Dm.Ax x * Dm.Bx x - Dm.Lrho) - Dm.Z0 * R).natDegree ≤
      2 * (P.D - 1) := by
    have hl := hD.Lrho_degree
    have hsub := natDegree_sub_le (Dm.Ax x * Dm.Bx x) Dm.Lrho
    have hsub2 := natDegree_sub_le (Dm.Ax x * Dm.Bx x - Dm.Lrho) (Dm.Z0 * R)
    omega
  have hother : (Dm.Ax x * Dm.Bx x - Dm.Z0 * R).natDegree ≤
      2 * (P.D - 1) := by
    have hsub := natDegree_sub_le (Dm.Ax x * Dm.Bx x) (Dm.Z0 * R)
    omega
  have heq1 : hk * (Dm.Z * (X - C Dm.rho)) =
      Dm.Ax x * Dm.Bx x - Dm.Lrho - Dm.Z0 * R := by
    rw [h.1]
    ring
  have heq2 : ho * Dm.Z = Dm.Ax x * Dm.Bx x - Dm.Z0 * R := by
    rw [h.2.1]
    ring
  have hstar : (Dm.Z * (X - C Dm.rho)).Monic := (z_monic S Dm hD).mul (monic_X_sub_C _)
  have hstar_deg : (Dm.Z * (X - C Dm.rho)).natDegree = P.D := by
    rw [(z_monic S Dm hD).natDegree_mul (monic_X_sub_C _), hz, natDegree_X_sub_C]
    omega
  constructor
  · by_cases hk0 : hk = 0
    · simp only [hk0, natDegree_zero]; omega
    · rw [← heq1, natDegree_mul hk0 hstar.ne_zero, hstar_deg] at hbig
      omega
  · by_cases ho0 : ho = 0
    · simp only [ho0, natDegree_zero]; omega
    · rw [← heq2, natDegree_mul ho0 (z_monic S Dm hD).ne_zero, hz] at hother
      omega

private theorem lambda_cell_quotient {P : Params} [Fact (Nat.Prime P.q)]
    (S : Relation P) (pp : PublicParams P)
    (hD : ValidQAP pp.qap S) (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N)
    (hx : x 0 = 1) (cl : Cell P)
    (hq : HonestQuotient pp.qap x (honestQuot pp.qap x).1
      (honestQuot pp.qap x).2.1 (honestQuot pp.qap x).2.2)
    (hshape : P.D = P.N + 2 + P.gatesMax * P.U) (hcover : P.D ≤ P.E1 * P.Mq) :
    CellQuotient pp.qap (honestStack v x) cl ((lambdaCoeffs pp v x).h cl)
      ((lambdaCoeffs pp v x).R cl) := by
  let k := lambdaCoeffs pp v x
  have hdeg := honest_degrees S pp.qap hD x _ _ _ hq hshape
  refine ⟨?_, ?_, ?_⟩
  · have hi := honest_cell_identity pp.qap v x _ _ _ hq cl
    by_cases hc : IsKeyCell cl
    · simpa only [k, lambdaCoeffs, honestStack, Matrix.smul_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, hx, mul_one, hc, if_true, key_weight v x cl hc] using hi
    · simpa only [k, lambdaCoeffs, honestStack, Matrix.smul_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, hx, mul_one, hc, if_false] using hi
  · constructor
    · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) hq.2.2.1
    · intro n hn
      simp only [lambdaCoeffs, coeff_C_mul, hq.2.2.2 n hn, mul_zero]
  · simp only [lambdaCoeffs]
    split_ifs <;> apply lt_of_le_of_lt (natDegree_C_mul_le _ _)
    · exact lt_of_lt_of_le hdeg.1 hcover
    · exact lt_of_lt_of_le hdeg.2 hcover

private theorem honest_comparison {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P)
    (name : (expGroups P.q).GT → ClassName P) (m : Msg P) (seed : Seed P)
    (c : Coins P) (x : Vec (Fq P) P.N) (σ : Sector)
    (hk : ∀ cl, CellQuotient pp.qap (honestStack (formsOf HF seed) x) cl
      ((lambdaCoeffs pp (formsOf HF seed) x).h cl) ((lambdaCoeffs pp (formsOf HF seed) x).R cl))
    (hk' : ∀ cl, CellQuotient pp.qap (honestStack (formsOf HF seed) x) cl
      ((stackComb pp (formsOf HF seed) (rField c.2.1) (honestStack (formsOf HF seed) x)).h cl)
      ((stackComb pp (formsOf HF seed) (rField c.2.1) (honestStack (formsOf HF seed) x)).R cl))
    (hz : coin c .zeta ≠ 0) (hz' : coin c .zeta' ≠ 0)
    (hw : 0 < P.E1) (hrw : 0 < P.U * P.E1p)
    (hrem : P.U * P.gatesMax = P.U * P.E1p * P.Wr) :
    (show Fq P from evalComb (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c) σ
        (lambdaCoeffs pp (formsOf HF seed) x)) =
      (show Fq P from evalComb (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c) σ
        (stackComb pp (formsOf HF seed) (rField c.2.1) (honestStack (formsOf HF seed) x))) +
      sectorScale c σ * (dot x (rField c.2.1) *
        ∑ cl : Cell P, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) +
      (match σ with | .plain => 0 | .alpha => keyCoeff (honestStack (formsOf HF seed) x) * gtExp pp c) := by
  let W := honestStack (formsOf HF seed) x
  let k := lambdaCoeffs pp (formsOf HF seed) x
  let k' := stackComb pp (formsOf HF seed) (rField c.2.1) W
  let ct := encrypt (expGroups P.q) HF kdf name pp m seed c
  have hd := evalComb_difference (expGroups P.q) ct σ k k' rfl rfl rfl
  change (show Fq P from evalComb (expGroups P.q) ct σ k) -
    (show Fq P from evalComb (expGroups P.q) ct σ k') = _ at hd
  have hs := sc_pair pp HF kdf name m seed c σ W (rField c.2.1)
  rw [honest_sc] at hs
  have hzsc : (∑ cl : Cell P, ∑ i : Fin (P.N + 1), k.sc cl i •
      (expGroups P.q).pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.SC σ cl.2))) = 0 := by
    simp [k, lambdaCoeffs]
  change (∑ cl : Cell P, ∑ i : Fin (P.N + 1), k'.sc cl i •
      (expGroups P.q).pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.SC σ cl.2))) = _ at hs
  rw [hs, hzsc] at hd
  rw [quotient_pair_sum pp HF kdf name m seed c σ W k' hk' hz hw,
      quotient_pair_sum pp HF kdf name m seed c σ W k hk hz hw,
      remainder_pair_sum pp HF kdf name m seed c σ W k' hk' hz' hrw hrem,
      remainder_pair_sum pp HF kdf name m seed c σ W k hk hz' hrw hrem] at hd
  have hc := correction_sums pp c σ W k k' hk hk'
  dsimp only [expGroups] at hd
  let q (z : CombCoeffs P) := ∑ cl : Cell P, sectorScale c σ *
    (gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) * (z.h cl).eval (coin c .tau))
  let r (z : CombCoeffs P) := ∑ cl : Cell P, sectorScale c σ *
    (gamma c cl * pp.qap.Z0.eval (coin c .tau) * (z.R cl).eval (coin c .tau))
  cases σ
  · change (show Fq P from evalComb (expGroups P.q) ct .plain k) -
      (show Fq P from evalComb (expGroups P.q) ct .plain k') =
      sectorScale c .plain * (dot x (rField c.2.1) *
        ∑ cl : Cell P, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) - 0 +
      (q k' - q k) + (r k' - r k) + (0 - 0) at hd
    change (show Fq P from evalComb (expGroups P.q) ct .plain k) =
      (show Fq P from evalComb (expGroups P.q) ct .plain k') +
        sectorScale c .plain * (dot x (rField c.2.1) *
          ∑ cl : Cell P, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) + 0
    generalize he₁ : (show Fq P from evalComb (expGroups P.q) ct .plain k) = a at hd ⊢
    generalize he₂ : (show Fq P from evalComb (expGroups P.q) ct .plain k') = b at hd ⊢
    simp only [q, r, sectorScale, one_mul, sub_zero, add_zero] at hd hc ⊢
    linear_combination hd - hc
  · change (show Fq P from evalComb (expGroups P.q) ct .alpha k) -
      (show Fq P from evalComb (expGroups P.q) ct .alpha k') =
      sectorScale c .alpha * (dot x (rField c.2.1) *
        ∑ cl : Cell P, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) - 0 +
      (q k' - q k) + (r k' - r k) +
        ((show Fq P from k'.key • ct.gT) - (show Fq P from k.key • ct.gT)) at hd
    change (show Fq P from evalComb (expGroups P.q) ct .alpha k) =
      (show Fq P from evalComb (expGroups P.q) ct .alpha k') +
        sectorScale c .alpha * (dot x (rField c.2.1) *
          ∑ cl : Cell P, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) +
        keyCoeff W * gtExp pp c
    generalize he₁ : (show Fq P from evalComb (expGroups P.q) ct .alpha k) = a at hd ⊢
    generalize he₂ : (show Fq P from evalComb (expGroups P.q) ct .alpha k') = b at hd ⊢
    simp only [ct, encrypt, exp_encT] at hd
    change a - b = sectorScale c .alpha * (dot x (rField c.2.1) *
      ∑ cl : Cell P, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) - 0 +
      (q k' - q k) + (r k' - r k) +
      (keyCoeff W * gtExp pp c - 0 * gtExp pp c) at hd
    simp only [sectorScale, q, r, zero_mul, sub_zero] at hd hc ⊢
    linear_combination hd - hc

theorem decryption_lambda (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (HF : FormOracle P0) (kdf : KDF P0) (m : Msg P0) (seed : Seed P0) (c : Coins P0)
    (hc : ValidCoins (ppOf ch S).qap c) (x : Vec (Fq P0) P0.N) (hx : IsWitness S x)
    (hw : wKey (formsOf HF seed) x ≠ 0) :
    evalComb (expGroups P0.q)
        (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .plain
        (lambdaCoeffs (ppOf ch S) (formsOf HF seed) x) =
      (expGroups P0.q).encT (wKey (formsOf HF seed) x * kappa (ppOf ch S) c +
        dot x (rField c.2.1) *
          ∑ cl : Cell P0, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) ∧
    evalComb (expGroups P0.q)
        (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .alpha
        (lambdaCoeffs (ppOf ch S) (formsOf HF seed) x) =
      (expGroups P0.q).encT (coin c .alpha * (wKey (formsOf HF seed) x * kappa (ppOf ch S) c +
        dot x (rField c.2.1) *
          ∑ cl : Cell P0, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i)) := by
  have hD : ValidQAP (ppOf ch S).qap S := QAP.domainMap_valid ch S
  have hq := chosen_honest_quotient ch S hS x hx
  have hx0 : x 0 = 1 := hx.1
  have hshape : P0.D = P0.N + 2 + P0.gatesMax * P0.U := by decide
  have hcover : P0.D ≤ P0.E1 * P0.Mq := by decide
  have hw1 : 0 < P0.E1 := by decide
  have hw2 : 0 < P0.U * P0.E1p := by decide
  have hrem : P0.U * P0.gatesMax = P0.U * P0.E1p * P0.Wr := by decide
  have hz : coin c .zeta ≠ 0 := hc.2.1 .zeta rfl
  have hz' : coin c .zeta' ≠ 0 := hc.2.1 .zeta' rfl
  have hpass (cl : Cell P0) : Passes S (honestStack (formsOf HF seed) x cl) :=
    Rank1.honest_cell_passes S x hx (weight (formsOf HF seed) x cl)
  have hW : PassingStack S (formsOf HF seed) (honestStack (formsOf HF seed) x) :=
    ⟨hpass, Ties.honest_ties (formsOf HF seed) x⟩
  have hLam (cl : Cell P0) := lambda_cell_quotient S (ppOf ch S) hD
    (formsOf HF seed) x hx0 cl hq hshape hcover
  have hs (cl : Cell P0) := chosen_cell_quotient ch S hS
    (honestStack (formsOf HF seed) x) cl (hpass cl)
  have hv := View.view_converse ch S hS HF kdf m seed c hc
    (honestStack (formsOf HF seed) x) hW
  have hp := honest_comparison (ppOf ch S) HF kdf canonName m seed c x .plain
    hLam hs hz hz' hw1 hw2 hrem
  have ha := honest_comparison (ppOf ch S) HF kdf canonName m seed c x .alpha
    hLam hs hz hz' hw1 hw2 hrem
  have hkey := honest_key_coeff (formsOf HF seed) x hx0
  rw [hv.1, exp_encT, hkey] at hp
  rw [hv.2, hkey] at ha
  constructor
  · rw [exp_encT]
    change (show Fq P0 from evalComb (expGroups P0.q)
      (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .plain
      (lambdaCoeffs (ppOf ch S) (formsOf HF seed) x)) = _
    simpa only [sectorScale, one_mul, add_zero] using hp
  · rw [exp_encT]
    change (show Fq P0 from evalComb (expGroups P0.q)
      (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .alpha
      (lambdaCoeffs (ppOf ch S) (formsOf HF seed) x)) = _
    simp only [sectorScale, zero_add, gtExp] at ha ⊢
    generalize hψ : (∑ cl : Cell P0, weight (formsOf HF seed) x cl * gamma c cl *
      ∑ i, x i * c.1 i) = ψ at ha ⊢
    rw [ha]
    change (0 : Fq P0) + coin c .alpha * (dot x (rField c.2.1) * ψ) +
      wKey (formsOf HF seed) x * (coin c .alpha * kappa (ppOf ch S) c) = _
    ring

end Praxis.Proofs.DecryptionAlgebra
