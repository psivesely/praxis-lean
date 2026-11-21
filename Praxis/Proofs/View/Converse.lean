import Praxis.Proofs.Ties.Origin
import Praxis.Proofs.QAP.Quot
import Praxis.Proofs.Basic
import Praxis.Proofs.Degree
import Praxis.Dec
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Kummer
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.Ties.Division
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Relation
import Praxis.Scheme
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec dot)

open Polynomial

set_option maxRecDepth 1024

@[simp] theorem exp_pair (q : ℕ) (a b : ZMod q) :
    (expGroups q).pair a b = a * b := by
  rfl

@[simp] theorem exp_enc1 (q : ℕ) (a : ZMod q) : (expGroups q).enc1 a = a := by
  change a * 1 = a
  exact mul_one a

@[simp] theorem exp_enc2 (q : ℕ) (a : ZMod q) : (expGroups q).enc2 a = a := by
  change a * 1 = a
  exact mul_one a

@[simp] theorem exp_encT (q : ℕ) (a : ZMod q) : (expGroups q).encT a = a := by
  change a * (1 * 1) = a
  simp

theorem sum_chunks {A : Type*} [AddCommMonoid A] (n m : ℕ) (f : ℕ → A) :
    (∑ a : Fin n, ∑ j : Fin m, f (a.val + n * j.val)) =
      ∑ t ∈ Finset.range (n * m), f t := by
  calc
    _ = ∑ p : Fin m × Fin n, f (p.2.val + n * p.1.val) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ t : Fin (m * n), f t.val := by
      exact (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).sum_comp (fun t => f t.val)
    _ = _ := by simpa [Nat.mul_comm] using (Fin.sum_univ_eq_sum_range (fun t => f t) (m * n))

theorem quotient_chunks (h : Polynomial (Fq P0)) (τ : Fq P0)
    (hh : h.natDegree < P0.E1 * P0.Mq) :
    (∑ a : Fin P0.E1, ∑ j : Fin P0.Mq,
      h.coeff (a.val + P0.E1 * j.val) * (τ ^ a.val * τ ^ (P0.E1 * j.val))) =
      h.eval τ := by
  simp_rw [← pow_add]
  calc
    _ = ∑ t ∈ Finset.range (P0.E1 * P0.Mq), h.coeff t * τ ^ t :=
      sum_chunks P0.E1 P0.Mq (fun t => h.coeff t * τ ^ t)
    _ = _ := (Polynomial.eval_eq_sum_range' hh τ).symm

theorem remainder_chunks (R : Polynomial (Fq P0)) (τ : Fq P0)
    (hR : AllowedRem R) :
    (∑ a : Fin (P0.U * P0.E1p), ∑ j : Fin P0.Wr,
      if P0.U ∣ a.val then 0 else
        R.coeff (a.val + P0.U * P0.E1p * j.val) *
          (τ ^ a.val * τ ^ (P0.U * P0.E1p * j.val))) = R.eval τ := by
  have hcover : P0.U * P0.E1p * P0.Wr = P0.U * P0.gatesMax := by decide
  have hdeg : R.natDegree < (P0.U * P0.E1p) * P0.Wr := by
    rw [hcover]
    exact hR.1
  have hsum : (∑ a : Fin (P0.U * P0.E1p), ∑ j : Fin P0.Wr,
      (if P0.U ∣ a.val then 0 else
        R.coeff (a.val + P0.U * P0.E1p * j.val) *
          (τ ^ a.val * τ ^ (P0.U * P0.E1p * j.val)))) =
      ∑ a : Fin (P0.U * P0.E1p), ∑ j : Fin P0.Wr,
        R.coeff (a.val + P0.U * P0.E1p * j.val) *
          (τ ^ a.val * τ ^ (P0.U * P0.E1p * j.val)) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with ha
    · have hd : P0.U ∣ a.val + P0.U * P0.E1p * j.val := by
        apply dvd_add ha
        exact dvd_mul_of_dvd_left (dvd_mul_right P0.U P0.E1p) j.val
      simp [hR.2 _ hd]
    · rfl
  rw [hsum]
  simp_rw [← pow_add]
  calc
    _ = ∑ t ∈ Finset.range ((P0.U * P0.E1p) * P0.Wr), R.coeff t * τ ^ t :=
      sum_chunks (P0.U * P0.E1p) P0.Wr (fun t => R.coeff t * τ ^ t)
    _ = _ := (Polynomial.eval_eq_sum_range' hdeg τ).symm

theorem chosen_cell_quotient (S : Relation P0) (hS : InShape P0 S)
    (Dm : QAPData P0) (hD : ValidQAP Dm S) (W : Stack P0) (cl : Cell P0)
    (hW : Passes S (W cl)) :
    CellQuotient Dm W cl (cellQuot Dm W cl).1 (cellQuot Dm W cl).2 := by
  classical
  obtain ⟨h, R, hq⟩ := QAP.cellQuotient_exists S hS Dm hD W cl hW
  have hex : ∃ p : Polynomial (Fq P0) × Polynomial (Fq P0),
      CellQuotient Dm W cl p.1 p.2 := ⟨(h, R), hq⟩
  unfold cellQuot
  rw [dif_pos hex]
  exact hex.choose_spec

theorem rearrange_quotient {R : Type*} [CommRing R] (a b c d : R)
    (h : a - b = c + d) : a - c - d = b := by
  linear_combination h

theorem collapse_from_quotient {P : Params} [Fact (Nat.Prime P.q)]
    (Dm : QAPData P) (W : Stack P) (cl : Cell P) (τ : Fq P)
    (hq : CellQuotient Dm W cl (cellQuot Dm W cl).1 (cellQuot Dm W cl).2) :
    (Dm.qapPoly (W cl)).eval τ -
      (Dm.zCell cl).eval τ * (cellQuot Dm W cl).1.eval τ -
      Dm.Z0.eval τ * (cellQuot Dm W cl).2.eval τ =
      (if IsKeyCell cl then W cl 0 0 else 0) * Dm.Lrho.eval τ := by
  have he := congrArg (Polynomial.eval τ) hq.1
  apply rearrange_quotient
  by_cases hk : IsKeyCell cl <;>
    simpa only [hk, if_true, if_false, eval_sub, eval_add, eval_mul, eval_C, eval_zero,
      zero_mul, sub_zero, mul_comm] using he

theorem cell_collapse (S : Relation P0) (hS : InShape P0 S)
    (Dm : QAPData P0) (hD : ValidQAP Dm S) (W : Stack P0) (cl : Cell P0)
    (hW : Passes S (W cl)) (τ : Fq P0) :
    (Dm.qapPoly (W cl)).eval τ -
      (Dm.zCell cl).eval τ * (cellQuot Dm W cl).1.eval τ -
      Dm.Z0.eval τ * (cellQuot Dm W cl).2.eval τ =
      (if IsKeyCell cl then W cl 0 0 else 0) * Dm.Lrho.eval τ :=
  collapse_from_quotient Dm W cl τ (chosen_cell_quotient S hS Dm hD W cl hW)

theorem gamma_of_key (c : Coins P0) (cl : Cell P0) (h : IsKeyCell cl) :
    gamma c cl = gammaKey c := by
  rcases cl with ⟨k, kind, j⟩
  rcases h with ⟨hk, he, hj⟩
  simp [gamma, gammaKey, legScale, IsKeyCell] at *
  subst kind
  simp [gamma, gammaKey, legScale, hk, hj]

theorem key_sum (c : Coins P0) (Dm : QAPData P0) (a : Cell P0 → Fq P0) :
    (∑ cl : Cell P0, gamma c cl * (if IsKeyCell cl then a cl else 0) *
      Dm.Lrho.eval (coin c .tau)) =
    (∑ cl ∈ Finset.univ.filter (IsKeyCell (P := P0)), a cl) *
      (gammaKey c * Dm.Lrho.eval (coin c .tau)) := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro cl _
  by_cases h : IsKeyCell cl
  · simp [h, gamma_of_key c cl h]
    ring
  · simp [h]

theorem symmetric_cell_algebra {F ι : Type*} [CommRing F] [Fintype ι]
    (M : ι → ι → F) (y r A B ν : ι → F) (s : F)
    (hs : ∀ i j, M i j = M j i) :
    (∑ i, ∑ j, M i j * (y i * (s * (r j + A j) + ν j) + A i * (s * (B j - y j)))) =
      s * ((∑ i, y i * ∑ j, M i j * r j) + ∑ i, ∑ j, M i j * A i * B j) +
        ∑ i, y i * ∑ j, M i j * ν j := by
  classical
  have hc : (∑ i, ∑ j, M i j * y i * A j) = ∑ i, ∑ j, M i j * A i * y j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
    ring
  simp only [mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  have hca : (∑ i, ∑ j, s * M i j * y i * A j) =
      ∑ i, ∑ j, s * M i j * A i * y j := by
    calc
      _ = s * (∑ i, ∑ j, M i j * y i * A j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = s * (∑ i, ∑ j, M i j * A i * y j) := congrArg (s * ·) hc
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hcr : (∑ i, ∑ j, M i j * y i * s * r j) =
      ∑ i, ∑ j, s * y i * M i j * r j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcv : (∑ i, ∑ j, M i j * y i * ν j) =
      ∑ i, ∑ j, y i * M i j * ν j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  ring_nf
  rw [hca, hcr, hcv]
  ring

theorem symmetric_cell (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (c : Coins P0) (l : Leg P0) (M : Algebra.Mat (Fq P0) P0.N) (hM : M.IsSymm) :
    (∑ i, ∑ j, M i j * (c.1 i * H1 pp v c l j +
      (pp.qap.A i).eval (coin c .tau) * H2 pp c l j)) =
    legScale c l * (dot c.1 (M.mulVec (rField c.2.1)) +
      (pp.qap.qapPoly M).eval (coin c .tau)) + dot c.1 (M.mulVec (legMask v c l)) := by
  simpa only [H1, H2, dot, Matrix.mulVec, dotProduct, QAPData.qapPoly,
    eval_finset_sum, eval_mul, eval_C] using
    symmetric_cell_algebra M c.1 (rField c.2.1)
      (fun i => (pp.qap.A i).eval (coin c .tau))
      (fun j => (pp.qap.B j).eval (coin c .tau))
      (legMask v c l) (legScale c l) (fun i j => (hM.apply i j).symm)

theorem pairing_algebra {F : Type*} [Field F] (p y A h₁ h₂ o₁ o₂ s w : F)
    (ho : o₂ ≠ 0) :
    w * ((p * y) * (s * (h₁ - o₁ / o₂ * h₂)) +
      (p * (o₁ * y + o₂ * A)) * (s * (h₂ / o₂))) =
      s * (p * (w * (y * h₁ + A * h₂))) := by
  field_simp
  <;> ring

theorem quotient_pairing_algebra {F : Type*} [Field F] (w z t g a s : F)
    (hz : z ≠ 0) : w * ((z * t) * (s * (g * a / z))) = s * (g * (w * (t * a))) := by
  field_simp
  <;> ring

theorem tie_pairing_algebra {F : Type*} [Field F] (w z y p t k u s : F)
    (hz : z ≠ 0) :
    w * ((z * y) * (s * (p * t * k * u / z))) =
      s * ((p * k) * (t * (w * y * u))) := by
  field_simp
  <;> ring

theorem cross_pairing_algebra {F : Type*} [Field F] (w z y p t u s : F)
    (hz : z ≠ 0) :
    w * ((z * y) * (s * (p * t * u / z))) = s * (p * (t * (w * y * u))) := by
  field_simp
  <;> ring

theorem converse_cell_pairing_sum (pp : PublicParams P0) (HF : FormOracle P0) (kdf : KDF P0)
    (m : Msg P0) (seed : Seed P0) (c : Coins P0) (hc : ValidCoins pp.qap c)
    (σ : Sector) (k : CombCoeffs P0) :
    (∑ cl : Cell P0, ∑ i : Fin (P0.N + 1), ∑ j : Fin (P0.N + 1),
      k.W cl i j • ((expGroups P0.q).pair
        ((encrypt (expGroups P0.q) HF kdf canonName pp m seed c).g1 (.L1 cl.1 i))
        ((encrypt (expGroups P0.q) HF kdf canonName pp m seed c).g2 (.ZeroCoordinate σ cl.2 j)) +
      (expGroups P0.q).pair
        ((encrypt (expGroups P0.q) HF kdf canonName pp m seed c).g1 (.L2 cl.1 i))
        ((encrypt (expGroups P0.q) HF kdf canonName pp m seed c).g2 (.R2 σ cl.2 j)))) =
    sectorScale c σ * ∑ cl : Cell P0, piAt c cl.1.val *
      ∑ i : Fin (P0.N + 1), ∑ j : Fin (P0.N + 1),
        k.W cl i j * (c.1 i * H1 pp (formsOf HF seed) c cl.2 j +
          (pp.qap.A i).eval (coin c .tau) * H2 pp c cl.2 j) := by
  have ho : coin c .Om22 ≠ 0 := hc.2.1 .Om22 rfl
  simp only [encrypt, exp_enc1, exp_enc2, exp_pair]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cl _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change k.W cl i j * ((g1Exp pp c (.L1 cl.1 i)) * (g2Exp pp (formsOf HF seed) c (.ZeroCoordinate σ cl.2 j)) +
    (g1Exp pp c (.L2 cl.1 i)) * (g2Exp pp (formsOf HF seed) c (.R2 σ cl.2 j))) = _
  simpa only [g1Exp, g2Exp, r1Exp, r2Exp] using
    pairing_algebra (piAt c cl.1.val) (c.1 i) ((pp.qap.A i).eval (coin c .tau))
      (H1 pp (formsOf HF seed) c cl.2 j) (H2 pp c cl.2 j) (coin c .Om12)
      (coin c .Om22) (sectorScale c σ) (k.W cl i j) ho

theorem mask_sum_reorder {F I S E : Type*} [CommSemiring F] [Fintype I] [Fintype S]
    [Fintype E] (y : I → F) (t : S → F) (u : E → F) (q : S → E → I → F) :
    (∑ i, y i * ∑ s, t s * ∑ e, u e * q s e i) =
      ∑ s, t s * ∑ e, ∑ i, q s e i * y i * u e := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

theorem tie_evaluation (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (ht : Ties v W) (c : Coins P0) (s : TieIdx) (i : Fin (P0.N + 1)) :
    (∑ t ∈ Finset.range (2 * P0.n - 1), coin c .u ^ t * tiePoly v W s t i) =
      kummerAtU c * ∑ e : Fin (P0.n - 1), coin c .u ^ e.val * tieQuot v W s e.val i := by
  rw [Ties.tie_division]
  have hzero (e : Fin P0.n) : reduceP P0.n (c0F P0) (tiePoly v W s) e i = 0 := by
    have h := congrFun (congrFun (ht s) e) i
    exact h
  simp only [hzero, mul_zero, Finset.sum_const_zero, add_zero, kummerAtU]
  rw [← Fin.sum_univ_eq_sum_range]

theorem mask_cancellation (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (ht : Ties v W) (c : Coins P0) (he : coin c .eps ≠ 0) :
    (∑ cl : Cell P0, piAt c cl.1.val * dot c.1 ((W cl).mulVec (legMask v c cl.2))) -
      coin c .pi * kummerAtU c *
        (∑ s : TieIdx, cTie c s * ∑ e : Fin (P0.n - 1), ∑ i : Fin (P0.N + 1),
          tieQuot v W s e.val i * c.1 i * coin c .u ^ e.val) -
      coin c .pi * (∑ g : CrossIdx, crossVal c g *
        ∑ e : Fin (2 * P0.n - 1), ∑ i : Fin (P0.N + 1),
          crossPoly v W g e.val i * c.1 i * coin c .u ^ e.val) = 0 := by
  have hm := Ties.mask_origin v W c he
  simp_rw [tie_evaluation v W ht c] at hm
  have htie : (∑ i : Fin (P0.N + 1), c.1 i * ∑ s : TieIdx,
      cTie c s * (kummerAtU c * ∑ e : Fin (P0.n - 1),
        coin c .u ^ e.val * tieQuot v W s e.val i)) =
      kummerAtU c * ∑ s : TieIdx, cTie c s * ∑ e : Fin (P0.n - 1),
        ∑ i : Fin (P0.N + 1), tieQuot v W s e.val i * c.1 i * coin c .u ^ e.val := by
    calc
      _ = ∑ i : Fin (P0.N + 1), c.1 i * ∑ s : TieIdx,
          (kummerAtU c * cTie c s) * ∑ e : Fin (P0.n - 1),
            coin c .u ^ e.val * tieQuot v W s e.val i := by
        apply Finset.sum_congr rfl
        intro i _
        apply congrArg (c.1 i * ·)
        apply Finset.sum_congr rfl
        intro s _
        rw [mul_left_comm, mul_assoc]
      _ = ∑ s : TieIdx, (kummerAtU c * cTie c s) * ∑ e : Fin (P0.n - 1),
          ∑ i : Fin (P0.N + 1), tieQuot v W s e.val i * c.1 i * coin c .u ^ e.val :=
        mask_sum_reorder c.1 (fun s => kummerAtU c * cTie c s)
          (fun e : Fin (P0.n - 1) => coin c .u ^ e.val)
          (fun s e i => tieQuot v W s e.val i)
      _ = _ := by simp_rw [Finset.mul_sum, mul_assoc]
  have hcross : (∑ i : Fin (P0.N + 1), c.1 i * ∑ g : CrossIdx,
      crossVal c g * ∑ t ∈ Finset.range (2 * P0.n - 1),
        coin c .u ^ t * crossPoly v W g t i) =
      ∑ g : CrossIdx, crossVal c g * ∑ e : Fin (2 * P0.n - 1),
        ∑ i : Fin (P0.N + 1), crossPoly v W g e.val i * c.1 i * coin c .u ^ e.val := by
    simp_rw [← Fin.sum_univ_eq_sum_range]
    exact mask_sum_reorder c.1 (crossVal c)
      (fun e : Fin (2 * P0.n - 1) => coin c .u ^ e.val)
      (fun g e i => crossPoly v W g e.val i)
  simp_rw [mul_add, Finset.sum_add_distrib, htie, hcross] at hm
  rw [hm]
  have hr {F : Type} [CommRing F] (p k a b : F) : p * (k * a + b) - p * k * a - p * b = 0 := by ring
  exact hr _ _ _ _

def quotChunks (h : Polynomial (Fq P0)) (τ : Fq P0) : Fq P0 :=
  ∑ a : Fin P0.E1, ∑ j : Fin P0.Mq,
    h.coeff (a.val + P0.E1 * j.val) * (τ ^ a.val * τ ^ (P0.E1 * j.val))

def remChunks (R : Polynomial (Fq P0)) (τ : Fq P0) : Fq P0 :=
  ∑ a : Fin (P0.U * P0.E1p), ∑ j : Fin P0.Wr,
    if P0.U ∣ a.val then 0 else
      R.coeff (a.val + P0.U * P0.E1p * j.val) *
        (τ ^ a.val * τ ^ (P0.U * P0.E1p * j.val))

theorem distributive_six {F : Type*} [Ring F] (s a b d e f g k : F) :
    s*a - s*b - s*d - s*e - s*f - s*g - k = s*(a-b-d-e-f-g)-k := by
  noncomm_ring

theorem cell_sums_assembly {F I : Type*} [CommRing F] [Fintype I]
    (p s d q z h r v k : I → F) (z0 L : F)
    (hc : ∀ i, q i - z i * h i - z0 * r i = k i * L) :
    (∑ i, p i * (s i * (d i + q i) + v i)) -
      (∑ i, (p i * s i) * d i) - (∑ i, (p i * s i) * z i * h i) -
      (∑ i, (p i * s i) * z0 * r i) =
      (∑ i, (p i * s i) * k i * L) + ∑ i, p i * v i := by
  classical
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination (p i * s i) * hc i

theorem add_mask_zero {F : Type*} [CommRing F] (a b d e : F) (h : b - d - e = 0) :
    a + b - d - e = a := by
  linear_combination h

theorem evalComb_encrypt (pp : PublicParams P0) (HF : FormOracle P0) (kdf : KDF P0)
    (m : Msg P0) (seed : Seed P0) (c : Coins P0) (hc : ValidCoins pp.qap c)
    (σ : Sector) (k : CombCoeffs P0) :
    evalComb (expGroups P0.q) (encrypt (expGroups P0.q) HF kdf canonName pp m seed c) σ k =
    (show Fq P0 from sectorScale c σ *
      ((∑ cl : Cell P0, piAt c cl.1.val * ∑ i : Fin (P0.N + 1), ∑ j : Fin (P0.N + 1),
          k.W cl i j * (c.1 i * H1 pp (formsOf HF seed) c cl.2 j +
            (pp.qap.A i).eval (coin c .tau) * H2 pp c cl.2 j)) -
       (∑ cl : Cell P0, gamma c cl * ∑ i : Fin (P0.N + 1), k.sc cl i * c.1 i) -
       (∑ cl : Cell P0, gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) * quotChunks (k.h cl) (coin c .tau)) -
       (∑ cl : Cell P0, gamma c cl * pp.qap.Z0.eval (coin c .tau) * remChunks (k.R cl) (coin c .tau)) -
       coin c .pi * kummerAtU c * (∑ s : TieIdx, cTie c s * ∑ e : Fin (P0.n - 1),
          ∑ i : Fin (P0.N + 1), k.Q s e.val i * c.1 i * coin c .u ^ e.val) -
       coin c .pi * (∑ g : CrossIdx, crossVal c g * ∑ e : Fin (2 * P0.n - 1),
          ∑ i : Fin (P0.N + 1), k.X g e.val i * c.1 i * coin c .u ^ e.val)) -
      (match σ with | .plain => (0 : Fq P0) | .alpha => k.key * (coin c .alpha * kappa pp c))) := by
  let ct := encrypt (expGroups P0.q) HF kdf canonName pp m seed c
  have hz : coin c .zeta ≠ 0 := hc.2.1 .zeta rfl
  have hzp : coin c .zeta' ≠ 0 := hc.2.1 .zeta' rfl
  have hz4 : coin c .zeta4 ≠ 0 := hc.2.1 .zeta4 rfl
  have hsc : (∑ cl : Cell P0, ∑ i : Fin (P0.N + 1), k.sc cl i •
      (expGroups P0.q).pair (ct.g1 (.L1 cl.1 i)) (ct.g2 (.SC σ cl.2))) =
      sectorScale c σ * ∑ cl : Cell P0, gamma c cl * ∑ i : Fin (P0.N + 1), k.sc cl i * c.1 i := by
    simp only [ct, encrypt, exp_enc1, exp_enc2, exp_pair]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cl _
    apply Finset.sum_congr rfl
    intro i _
    change k.sc cl i * (g1Exp pp c (.L1 cl.1 i) * g2Exp pp (formsOf HF seed) c (.SC σ cl.2)) = _
    simp only [g1Exp, g2Exp, gamma]
    ac_rfl
  have hq : (∑ cl : Cell P0, ∑ a : Fin P0.E1, ∑ j : Fin P0.Mq,
      (k.h cl).coeff (a.val + P0.E1 * j.val) •
        (expGroups P0.q).pair (ct.g1 (.QP a)) (ct.g2 (.QB σ cl j))) =
      sectorScale c σ * ∑ cl : Cell P0, gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) *
        quotChunks (k.h cl) (coin c .tau) := by
    simp only [ct, encrypt, exp_enc1, exp_enc2, exp_pair, quotChunks]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cl _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    change (k.h cl).coeff (a.val + P0.E1 * j.val) *
      (g1Exp pp c (.QP a) * g2Exp pp (formsOf HF seed) c (.QB σ cl j)) = _
    simp only [g1Exp, g2Exp]
    exact quotient_pairing_algebra ((k.h cl).coeff (a.val + P0.E1 * j.val))
      (coin c .zeta) (coin c .tau ^ a.val)
      (gamma c cl * (pp.qap.zCell cl).eval (coin c .tau))
      (coin c .tau ^ (P0.E1 * j.val)) (sectorScale c σ) hz
  have hr : (∑ cl : Cell P0, ∑ a : Fin (P0.U * P0.E1p), ∑ j : Fin P0.Wr,
      if h : P0.U ∣ a.val then 0 else (k.R cl).coeff (a.val + P0.U * P0.E1p * j.val) •
        (expGroups P0.q).pair (ct.g1 (.RP ⟨a, h⟩)) (ct.g2 (.RB σ cl j))) =
      sectorScale c σ * ∑ cl : Cell P0, gamma c cl * pp.qap.Z0.eval (coin c .tau) *
        remChunks (k.R cl) (coin c .tau) := by
    simp only [ct, encrypt, exp_enc1, exp_enc2, exp_pair, remChunks]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cl _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with ha
    · rfl
    · change (k.R cl).coeff (a.val + P0.U * P0.E1p * j.val) *
        (g1Exp pp c (.RP ⟨a, ha⟩) * g2Exp pp (formsOf HF seed) c (.RB σ cl j)) = _
      simp only [g1Exp, g2Exp]
      exact quotient_pairing_algebra ((k.R cl).coeff (a.val + P0.U * P0.E1p * j.val))
        (coin c .zeta') (coin c .tau ^ a.val) (gamma c cl * pp.qap.Z0.eval (coin c .tau))
        (coin c .tau ^ (P0.U * P0.E1p * j.val)) (sectorScale c σ) hzp
  have ht : (∑ s : TieIdx, ∑ e : Fin (P0.n - 1), ∑ i : Fin (P0.N + 1),
      k.Q s e.val i • (expGroups P0.q).pair (ct.g1 (.GY i)) (ct.g2 (.GM σ s e))) =
      sectorScale c σ * (coin c .pi * kummerAtU c * ∑ s : TieIdx, cTie c s *
        ∑ e : Fin (P0.n - 1), ∑ i : Fin (P0.N + 1),
          k.Q s e.val i * c.1 i * coin c .u ^ e.val) := by
    simp only [ct, encrypt, exp_enc1, exp_enc2, exp_pair]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro i _
    change k.Q s e.val i * (g1Exp pp c (.GY i) *
      g2Exp pp (formsOf HF seed) c (.GM σ s e)) = _
    simp only [g1Exp, g2Exp]
    exact tie_pairing_algebra (k.Q s e.val i) (coin c .zeta4) (c.1 i)
      (coin c .pi) (cTie c s) (kummerAtU c) (coin c .u ^ e.val) (sectorScale c σ) hz4
  have hx : (∑ g : CrossIdx, ∑ e : Fin (2 * P0.n - 1), ∑ i : Fin (P0.N + 1),
      k.X g e.val i • (expGroups P0.q).pair (ct.g1 (.GY i)) (ct.g2 (.GB σ g e))) =
      sectorScale c σ * (coin c .pi * ∑ g : CrossIdx, crossVal c g *
        ∑ e : Fin (2 * P0.n - 1), ∑ i : Fin (P0.N + 1),
          k.X g e.val i * c.1 i * coin c .u ^ e.val) := by
    simp only [ct, encrypt, exp_enc1, exp_enc2, exp_pair]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro i _
    change k.X g e.val i * (g1Exp pp c (.GY i) *
      g2Exp pp (formsOf HF seed) c (.GB σ g e)) = _
    simp only [g1Exp, g2Exp]
    exact cross_pairing_algebra (k.X g e.val i) (coin c .zeta4) (c.1 i)
      (coin c .pi) (crossVal c g) (coin c .u ^ e.val) (sectorScale c σ) hz4
  unfold evalComb
  change _ = _
  rw [converse_cell_pairing_sum pp HF kdf m seed c hc σ k, hsc, hq, hr, ht, hx]
  cases σ <;> simp only [ct, encrypt, exp_encT, gtExp, sectorScale]
  all_goals change (_ : Fq P0) = _
  all_goals exact distributive_six _ _ _ _ _ _ _ _

theorem stack_cell_sum (S : Relation P0) (hS : InShape P0 S) (pp : PublicParams P0)
    (hD : ValidQAP pp.qap S) (v : Fin P0.n → Vec (Fq P0) P0.N) (c : Coins P0)
    (W : Stack P0) (hW : PassingStack S v W) :
    (∑ cl : Cell P0, piAt c cl.1.val * ∑ i : Fin (P0.N + 1), ∑ j : Fin (P0.N + 1),
      W cl i j * (c.1 i * H1 pp v c cl.2 j + (pp.qap.A i).eval (coin c .tau) * H2 pp c cl.2 j)) -
    (∑ cl : Cell P0, gamma c cl * ∑ i : Fin (P0.N + 1), (W cl).mulVec (rField c.2.1) i * c.1 i) -
    (∑ cl : Cell P0, gamma c cl * (pp.qap.zCell cl).eval (coin c .tau) *
      quotChunks (cellQuot pp.qap W cl).1 (coin c .tau)) -
    (∑ cl : Cell P0, gamma c cl * pp.qap.Z0.eval (coin c .tau) *
      remChunks (cellQuot pp.qap W cl).2 (coin c .tau)) =
    keyCoeff W * kappa pp c +
      ∑ cl : Cell P0, piAt c cl.1.val * dot c.1 ((W cl).mulVec (legMask v c cl.2)) := by
  have hq (cl : Cell P0) := chosen_cell_quotient S hS pp.qap hD W cl (hW.1 cl)
  have hcollapse (cl : Cell P0) :
      (pp.qap.qapPoly (W cl)).eval (coin c .tau) -
        (pp.qap.zCell cl).eval (coin c .tau) * quotChunks (cellQuot pp.qap W cl).1 (coin c .tau) -
        pp.qap.Z0.eval (coin c .tau) * remChunks (cellQuot pp.qap W cl).2 (coin c .tau) =
        (if IsKeyCell cl then W cl 0 0 else 0) * pp.qap.Lrho.eval (coin c .tau) := by
    rw [show quotChunks (cellQuot pp.qap W cl).1 (coin c .tau) =
      (cellQuot pp.qap W cl).1.eval (coin c .tau) from quotient_chunks _ _ (hq cl).2.2]
    rw [show remChunks (cellQuot pp.qap W cl).2 (coin c .tau) =
      (cellQuot pp.qap W cl).2.eval (coin c .tau) from remainder_chunks _ _ (hq cl).2.1]
    exact cell_collapse S hS pp.qap hD W cl (hW.1 cl) _
  have hfirst : (∑ cl : Cell P0, piAt c cl.1.val * ∑ i : Fin (P0.N + 1), ∑ j : Fin (P0.N + 1),
      W cl i j * (c.1 i * H1 pp v c cl.2 j + (pp.qap.A i).eval (coin c .tau) * H2 pp c cl.2 j)) =
      ∑ cl : Cell P0, piAt c cl.1.val *
        (legScale c cl.2 * (dot c.1 ((W cl).mulVec (rField c.2.1)) +
          (pp.qap.qapPoly (W cl)).eval (coin c .tau)) +
          dot c.1 ((W cl).mulVec (legMask v c cl.2))) := by
    apply Finset.sum_congr rfl
    intro cl _
    rw [symmetric_cell pp v c cl.2 (W cl) (hW.1 cl).1]
  have hsc : (∑ cl : Cell P0, gamma c cl * ∑ i : Fin (P0.N + 1),
      (W cl).mulVec (rField c.2.1) i * c.1 i) =
      ∑ cl : Cell P0, gamma c cl * dot c.1 ((W cl).mulVec (rField c.2.1)) := by
    apply Finset.sum_congr rfl
    intro cl _
    apply congrArg (gamma c cl * ·)
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hfirst, hsc]
  have ha := cell_sums_assembly (fun cl : Cell P0 => piAt c cl.1.val)
    (fun cl => legScale c cl.2) (fun cl => dot c.1 ((W cl).mulVec (rField c.2.1)))
    (fun cl => (pp.qap.qapPoly (W cl)).eval (coin c .tau))
    (fun cl => (pp.qap.zCell cl).eval (coin c .tau))
    (fun cl => quotChunks (cellQuot pp.qap W cl).1 (coin c .tau))
    (fun cl => remChunks (cellQuot pp.qap W cl).2 (coin c .tau))
    (fun cl => dot c.1 ((W cl).mulVec (legMask v c cl.2)))
    (fun cl => if IsKeyCell cl then W cl 0 0 else 0)
    (pp.qap.Z0.eval (coin c .tau)) (pp.qap.Lrho.eval (coin c .tau)) hcollapse
  change _ = _ at ha
  have hg (cl : Cell P0) : piAt c cl.1.val * legScale c cl.2 = gamma c cl := rfl
  simp_rw [hg] at ha
  rw [key_sum] at ha
  simpa only [keyCoeff, kappa] using ha

theorem view_converse (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (HF : FormOracle P0) (kdf : KDF P0) (m : Msg P0) (seed : Seed P0) (c : Coins P0)
    (hc : ValidCoins (ppOf ch S).qap c) (W : Stack P0)
    (hW : PassingStack S (formsOf HF seed) W) :
    evalComb (expGroups P0.q)
        (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .plain
        (stackComb (ppOf ch S) (formsOf HF seed) (rField c.2.1) W) =
      (expGroups P0.q).encT (keyCoeff W * kappa (ppOf ch S) c) ∧
    evalComb (expGroups P0.q)
        (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .alpha
        (stackComb (ppOf ch S) (formsOf HF seed) (rField c.2.1) W) = 0 := by
  have hD : ValidQAP (ppOf ch S).qap S := QAP.domainMap_valid ch S
  have hm := mask_cancellation (formsOf HF seed) W hW.2 c hc.2.2.1
  have hs := stack_cell_sum S hS (ppOf ch S) hD (formsOf HF seed) c W hW
  have hcore :
      (∑ cl : Cell P0, piAt c cl.1.val * ∑ i : Fin (P0.N + 1), ∑ j : Fin (P0.N + 1),
        W cl i j * (c.1 i * H1 (ppOf ch S) (formsOf HF seed) c cl.2 j +
          ((ppOf ch S).qap.A i).eval (coin c .tau) * H2 (ppOf ch S) c cl.2 j)) -
      (∑ cl : Cell P0, gamma c cl * ∑ i : Fin (P0.N + 1), (W cl).mulVec (rField c.2.1) i * c.1 i) -
      (∑ cl : Cell P0, gamma c cl * ((ppOf ch S).qap.zCell cl).eval (coin c .tau) *
        quotChunks (cellQuot (ppOf ch S).qap W cl).1 (coin c .tau)) -
      (∑ cl : Cell P0, gamma c cl * (ppOf ch S).qap.Z0.eval (coin c .tau) *
        remChunks (cellQuot (ppOf ch S).qap W cl).2 (coin c .tau)) -
      coin c .pi * kummerAtU c * (∑ s : TieIdx, cTie c s * ∑ e : Fin (P0.n - 1),
        ∑ i : Fin (P0.N + 1), tieQuot (formsOf HF seed) W s e.val i * c.1 i * coin c .u ^ e.val) -
      coin c .pi * (∑ g : CrossIdx, crossVal c g * ∑ e : Fin (2 * P0.n - 1),
        ∑ i : Fin (P0.N + 1), crossPoly (formsOf HF seed) W g e.val i * c.1 i * coin c .u ^ e.val) =
      keyCoeff W * kappa (ppOf ch S) c := by
    rw [hs]
    exact add_mask_zero _ _ _ _ hm
  constructor <;> rw [evalComb_encrypt _ _ _ _ _ _ hc]
  all_goals change (_ : Fq P0) = _
  all_goals simp only [stackComb, hcore, sectorScale, exp_encT, one_mul, sub_zero]
  change coin c .alpha * (keyCoeff W * kappa (ppOf ch S) c) -
    keyCoeff W * (coin c .alpha * kappa (ppOf ch S) c) = (0 : Fq P0)
  rw [mul_left_comm (coin c .alpha) (keyCoeff W), sub_self]

end Praxis.Proofs.View
