import Praxis.Proofs.DecryptionAlgebra.Lambda.Chunks
import Praxis.Dec
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.DecryptionAlgebra

open Praxis.Algebra (Vec dot)

open Polynomial

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem rank_contract {F I : Type*} [CommSemiring F] [Fintype I]
    (w : F) (x r y : I → F) :
    (∑ i, ((w • Matrix.vecMulVec x x).mulVec r) i * y i) =
      w * (∑ j, x j * r j) * (∑ i, x i * y i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exp_encT (a : Fq P) : (expGroups P.q).encT a = a := by
  change a • ((1 : Fq P) * 1) = a
  simp [smul_eq_mul]

theorem exp_scaled_pair (a b z : Fq P) :
    (a • (expGroups P.q).pair ((expGroups P.q).enc1 b) ((expGroups P.q).enc2 z) :
      (expGroups P.q).GT) = a * (b * z) := by
  change a • ((b • (1 : Fq P)) * (z • (1 : Fq P))) = _
  simp [smul_eq_mul]

theorem sc_pair (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P)
    (name : (expGroups P.q).GT → ClassName P) (m : Msg P) (seed : Seed P)
    (c : Coins P) (σ : Sector) (W : Stack P) (r : Vec (Fq P) P.N) :
    (∑ cl : Cell P, ∑ i : Fin (P.N + 1), (W cl).mulVec r i •
      (expGroups P.q).pair
        ((encrypt (expGroups P.q) HF kdf name pp m seed c).g1 (.L1 cl.1 i))
        ((encrypt (expGroups P.q) HF kdf name pp m seed c).g2 (.SC σ cl.2))) =
      sectorScale c σ * ∑ cl : Cell P, gamma c cl * ∑ i, ((W cl).mulVec r) i * c.1 i := by
  change (∑ cl : Cell P, ∑ i : Fin (P.N + 1), (W cl).mulVec r i *
      ((g1Exp pp c (.L1 cl.1 i) * 1) *
        (g2Exp pp (formsOf HF seed) c (.SC σ cl.2) * 1))) = _
  simp only [g1Exp, g2Exp, mul_one, Finset.mul_sum, gamma]
  apply Finset.sum_congr rfl
  intro cl _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem honest_sc (v : Fin P.n → Vec (Fq P) P.N) (x r y : Vec (Fq P) P.N)
    (c : Coins P) :
    (∑ cl : Cell P, gamma c cl * ∑ i, ((honestStack v x cl).mulVec r) i * y i) =
      dot x r * ∑ cl : Cell P, weight v x cl * gamma c cl * ∑ i, x i * y i := by
  simp only [honestStack, rank_contract, dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cl _
  simp only [← Finset.mul_sum]
  ring

theorem evalComb_difference (B : BilinearGroups P.q) (ct : Ciphertext B) (σ : Sector)
    (k k' : CombCoeffs P) (hW : k.W = k'.W) (hQ : k.Q = k'.Q) (hX : k.X = k'.X) :
    evalComb B ct σ k - evalComb B ct σ k' =
      ((∑ cl : Cell P, ∑ i : Fin (P.N + 1),
        k'.sc cl i • B.pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.SC σ cl.2))) -
       (∑ cl : Cell P, ∑ i : Fin (P.N + 1),
        k.sc cl i • B.pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.SC σ cl.2)))) +
      ((∑ cl : Cell P, ∑ a : Fin P.E1, ∑ j : Fin P.Mq,
        (k'.h cl).coeff (a.val + P.E1 * j.val) • B.pair (ct.g1 (.QP a)) (ct.g2 (.QB σ cl j))) -
       (∑ cl : Cell P, ∑ a : Fin P.E1, ∑ j : Fin P.Mq,
        (k.h cl).coeff (a.val + P.E1 * j.val) • B.pair (ct.g1 (.QP a)) (ct.g2 (.QB σ cl j)))) +
      ((∑ cl : Cell P, ∑ a : Fin (P.U * P.E1p), ∑ j : Fin P.Wr,
        if h : P.U ∣ a.val then 0 else
          (k'.R cl).coeff (a.val + P.U * P.E1p * j.val) •
            B.pair (ct.g1 (.RP ⟨a, h⟩)) (ct.g2 (.RB σ cl j))) -
       (∑ cl : Cell P, ∑ a : Fin (P.U * P.E1p), ∑ j : Fin P.Wr,
        if h : P.U ∣ a.val then 0 else
          (k.R cl).coeff (a.val + P.U * P.E1p * j.val) •
            B.pair (ct.g1 (.RP ⟨a, h⟩)) (ct.g2 (.RB σ cl j)))) +
      ((match σ with | .plain => 0 | .alpha => k'.key • ct.gT) -
       (match σ with | .plain => 0 | .alpha => k.key • ct.gT)) := by
  cases σ <;> simp only [evalComb, hW, hQ, hX] <;> abel

theorem quotient_pair (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P)
    (name : (expGroups P.q).GT → ClassName P) (m : Msg P) (seed : Seed P)
    (c : Coins P) (σ : Sector) (cl : Cell P) (h : Polynomial (Fq P))
    (hz : coin c .zeta ≠ 0) (hwidth : 0 < P.E1) (hh : h.natDegree < P.E1 * P.Mq) :
    (∑ a : Fin P.E1, ∑ j : Fin P.Mq,
      h.coeff (a.val + P.E1 * j.val) •
        (expGroups P.q).pair
          ((encrypt (expGroups P.q) HF kdf name pp m seed c).g1 (.QP a))
          ((encrypt (expGroups P.q) HF kdf name pp m seed c).g2 (.QB σ cl j))) =
      sectorScale c σ * (gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) * h.eval (coin c .tau)) := by
  rw [← quotient_chunks P.E1 P.Mq hwidth h (coin c .tau) hh]
  simp only [encrypt, exp_scaled_pair, g1Exp, g2Exp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  field_simp
  <;> ring

theorem remainder_pair (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P)
    (name : (expGroups P.q).GT → ClassName P) (m : Msg P) (seed : Seed P)
    (c : Coins P) (σ : Sector) (cl : Cell P) (R : Polynomial (Fq P))
    (hz : coin c .zeta' ≠ 0) (hwidth : 0 < P.U * P.E1p)
    (hR : R.natDegree < (P.U * P.E1p) * P.Wr)
    (hsparse : ∀ n, P.U ∣ n → R.coeff n = 0) :
    (∑ a : Fin (P.U * P.E1p), ∑ j : Fin P.Wr,
      if ha : P.U ∣ a.val then 0 else
        R.coeff (a.val + P.U * P.E1p * j.val) •
          (expGroups P.q).pair
            ((encrypt (expGroups P.q) HF kdf name pp m seed c).g1 (.RP ⟨a, ha⟩))
            ((encrypt (expGroups P.q) HF kdf name pp m seed c).g2 (.RB σ cl j))) =
      sectorScale c σ * (gamma c cl * pp.qap.Z0.eval (coin c .tau) * R.eval (coin c .tau)) := by
  rw [← remainder_chunks P.U (P.U * P.E1p) P.Wr hwidth (dvd_mul_right _ _) R
    (coin c .tau) hR hsparse]
  change (∑ a : Fin (P.U * P.E1p), ∑ j : Fin P.Wr,
    if ha : P.U ∣ a.val then (0 : Fq P) else
      R.coeff (a.val + P.U * P.E1p * j.val) *
        ((g1Exp pp c (.RP ⟨a, ha⟩) * 1) *
          (g2Exp pp (formsOf HF seed) c (.RB σ cl j) * 1))) = _
  simp only [g1Exp, g2Exp, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  by_cases ha : P.U ∣ a.val
  · simp only [dif_pos ha, if_pos ha, mul_zero]
  · simp only [dif_neg ha, if_neg ha]
    field_simp
    <;> ring

theorem correction_sums (pp : PublicParams P) (c : Coins P) (σ : Sector)
    (W : Stack P) (k k' : CombCoeffs P)
    (hk : ∀ cl, CellQuotient pp.qap W cl (k.h cl) (k.R cl))
    (hk' : ∀ cl, CellQuotient pp.qap W cl (k'.h cl) (k'.R cl)) :
    (∑ cl : Cell P, sectorScale c σ * (gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) * (k.h cl).eval (coin c .tau))) +
      (∑ cl : Cell P, sectorScale c σ * (gamma c cl * pp.qap.Z0.eval (coin c .tau) * (k.R cl).eval (coin c .tau))) =
    (∑ cl : Cell P, sectorScale c σ * (gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) * (k'.h cl).eval (coin c .tau))) +
      (∑ cl : Cell P, sectorScale c σ * (gamma c cl * pp.qap.Z0.eval (coin c .tau) * (k'.R cl).eval (coin c .tau))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro cl _
  have he := congrArg (Polynomial.eval (coin c .tau)) ((hk cl).1.symm.trans (hk' cl).1)
  simp only [eval_add, eval_mul] at he
  linear_combination sectorScale c σ * gamma c cl * he

theorem quotient_pair_sum (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P)
    (name : (expGroups P.q).GT → ClassName P) (m : Msg P) (seed : Seed P)
    (c : Coins P) (σ : Sector) (W : Stack P) (k : CombCoeffs P)
    (hk : ∀ cl, CellQuotient pp.qap W cl (k.h cl) (k.R cl))
    (hz : coin c .zeta ≠ 0) (hwidth : 0 < P.E1) :
    (∑ cl : Cell P, ∑ a : Fin P.E1, ∑ j : Fin P.Mq,
      (k.h cl).coeff (a.val + P.E1 * j.val) •
        (expGroups P.q).pair
          ((encrypt (expGroups P.q) HF kdf name pp m seed c).g1 (.QP a))
          ((encrypt (expGroups P.q) HF kdf name pp m seed c).g2 (.QB σ cl j))) =
    ∑ cl : Cell P, sectorScale c σ *
      (gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) * (k.h cl).eval (coin c .tau)) := by
  apply Finset.sum_congr rfl
  intro cl _
  exact quotient_pair pp HF kdf name m seed c σ cl (k.h cl) hz hwidth (hk cl).2.2

theorem remainder_pair_sum (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P)
    (name : (expGroups P.q).GT → ClassName P) (m : Msg P) (seed : Seed P)
    (c : Coins P) (σ : Sector) (W : Stack P) (k : CombCoeffs P)
    (hk : ∀ cl, CellQuotient pp.qap W cl (k.h cl) (k.R cl))
    (hz : coin c .zeta' ≠ 0) (hwidth : 0 < P.U * P.E1p)
    (hrem : P.U * P.gatesMax = P.U * P.E1p * P.Wr) :
    (∑ cl : Cell P, ∑ a : Fin (P.U * P.E1p), ∑ j : Fin P.Wr,
      if ha : P.U ∣ a.val then 0 else
        (k.R cl).coeff (a.val + P.U * P.E1p * j.val) •
          (expGroups P.q).pair
            ((encrypt (expGroups P.q) HF kdf name pp m seed c).g1 (.RP ⟨a, ha⟩))
            ((encrypt (expGroups P.q) HF kdf name pp m seed c).g2 (.RB σ cl j))) =
    ∑ cl : Cell P, sectorScale c σ *
      (gamma c cl * pp.qap.Z0.eval (coin c .tau) * (k.R cl).eval (coin c .tau)) := by
  apply Finset.sum_congr rfl
  intro cl _
  apply remainder_pair pp HF kdf name m seed c σ cl (k.R cl) hz hwidth
  · rw [← hrem]
    exact (hk cl).2.1.1
  · exact (hk cl).2.1.2

end Praxis.Proofs.DecryptionAlgebra
