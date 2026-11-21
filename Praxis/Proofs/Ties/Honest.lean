import Praxis.Proofs.Ties.Grid
import Praxis.KummerIrr
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Ties

open Praxis.Algebra (Vec)

private lemma evalCoeffs_mul {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    {n : ℕ} (c : F) (y : E) (hy : y ^ n = algebraMap F E c)
    (a b : Fin n → F) :
    Fintype.linearCombination F (fun i : Fin n => y ^ i.val) (reduceP n c (rawMul a b)) =
      Fintype.linearCombination F (fun i : Fin n => y ^ i.val) a *
        Fintype.linearCombination F (fun i : Fin n => y ^ i.val) b := by
  classical
  have term (i j : Fin n) :
      (∑ e : Fin n, ((if i.val + j.val = e.val then algebraMap F E (a i * b j) else 0) *
        y ^ e.val + algebraMap F E c *
        (if i.val + j.val = e.val + n then algebraMap F E (a i * b j) else 0) *
          y ^ e.val)) = algebraMap F E (a i * b j) * y ^ (i.val + j.val) := by
    by_cases h : i.val + j.val < n
    · rw [Finset.sum_eq_single (⟨i.val + j.val, h⟩ : Fin n)]
      · simp [show n ≠ 0 by omega]
      · intro e _ he
        have hne : i.val + j.val ≠ e.val := fun hh => he (Fin.ext hh.symm)
        have hhigh : i.val + j.val ≠ e.val + n := by omega
        simp [hne, hhigh]
      · simp
    · have hk : i.val + j.val - n < n := by omega
      rw [Finset.sum_eq_single (⟨i.val + j.val - n, hk⟩ : Fin n)]
      · have he : i.val + j.val = i.val + j.val - n + n := by omega
        simp only [show i.val + j.val ≠ i.val + j.val - n by omega, if_false,
          he.symm, if_true, zero_mul, zero_add]
        conv_rhs => rw [he, pow_add, hy]
        ring
      · intro e _ he
        have hne : i.val + j.val ≠ e.val := by omega
        have hhigh : i.val + j.val ≠ e.val + n := by
          intro hh
          apply he
          apply Fin.ext
          dsimp
          omega
        simp [hne, hhigh]
      · simp
  calc
    Fintype.linearCombination F (fun i : Fin n => y ^ i.val) (reduceP n c (rawMul a b)) =
        ∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          ((if i.val + j.val = e.val then algebraMap F E (a i * b j) else 0) * y ^ e.val +
          algebraMap F E c *
            (if i.val + j.val = e.val + n then algebraMap F E (a i * b j) else 0) *
              y ^ e.val) := by
      simp only [Fintype.linearCombination_apply, Algebra.smul_def, Algebra.algebraMap_self,
        RingHom.id_apply, reduceP, rawMul, map_add, map_mul, map_sum,
        apply_ite (algebraMap F E), map_zero, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul, add_mul]
    _ = ∑ i : Fin n, ∑ j : Fin n, algebraMap F E (a i * b j) * y ^ (i.val + j.val) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => term i j
    _ = Fintype.linearCombination F (fun i : Fin n => y ^ i.val) a *
        Fintype.linearCombination F (fun i : Fin n => y ^ i.val) b := by
      simp only [Fintype.linearCombination_apply, Algebra.smul_def]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      simp only [map_mul, pow_add]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma evalCoeffs_injective {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0) (c : F) :
    Function.Injective (Fintype.linearCombination F (fun i : Fin n => (AdjoinRoot.root
      ((Polynomial.X : Polynomial F) ^ n - Polynomial.C c)) ^ i.val)) := by
  let p : Polynomial F := Polynomial.X ^ n - Polynomial.C c
  have hm : p.Monic := Polynomial.monic_X_pow_sub_C c hn
  have hd : p.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  let b := (AdjoinRoot.powerBasis' hm).basis.reindex (finCongr hd)
  have hb (i : Fin n) : b i = AdjoinRoot.root p ^ i.val := by
    simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis'_gen]
    rfl
  intro a a' h
  apply (linearIndependent_iff_injective_fintypeLinearCombination.mp b.linearIndependent)
  change (∑ i, a i • b i) = ∑ i, a' i • b i
  simpa only [Fintype.linearCombination_apply, Algebra.smul_def, hb] using h

section Algebra

variable {P : Params} [Fact (Nat.Prime P.q)]

private lemma rootP_pow :
    (AdjoinRoot.root (KummerPoly P)) ^ P.n = algebraMap (Fq P) (KummerField P) (c0F P) := by
  apply sub_eq_zero.mp
  change (AdjoinRoot.root (KummerPoly P)) ^ P.n -
    AdjoinRoot.of (KummerPoly P) (c0F P) = 0
  have h := AdjoinRoot.eval₂_root (KummerPoly P)
  change Polynomial.eval₂ _ _ (Polynomial.X ^ P.n - Polynomial.C (c0F P)) = 0 at h
  simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] using h

private lemma eval_sigma {E : Type*} [CommRing E] [Algebra (Fq P) E]
    (y : E) (s : ℕ) (a : Fin P.n → Fq P) :
    Fintype.linearCombination (Fq P) (fun i : Fin P.n => y ^ i.val) (sigma P s a) =
      Fintype.linearCombination (Fq P)
        (fun i : Fin P.n => ((algebraMap (Fq P) E (betaF P)) ^ s * y) ^ i.val) a := by
  simp only [Fintype.linearCombination_apply, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sigma, frob, smul_eq_mul, map_mul, map_pow, mul_pow, pow_mul]
  ring

private lemma scaled_root_pow (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0) (s : ℕ) :
    (algebraMap (Fq P) (KummerField P) (betaF P) ^ s * (AdjoinRoot.root (KummerPoly P))) ^ P.n =
      algebraMap (Fq P) (KummerField P) (c0F P) := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm s P.n, pow_mul, ← map_pow, hL.2.2.1,
    map_one, one_pow, one_mul, rootP_pow]

private lemma coeffs_inj (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0) :
    Function.Injective (Fintype.linearCombination (Fq P)
      (fun i : Fin P.n => (AdjoinRoot.root (KummerPoly P)) ^ i.val)) :=
  evalCoeffs_injective hL.1 (c0F P)

private lemma eval_kmul (a b : Fin P.n → Fq P) :
    Fintype.linearCombination (Fq P)
        (fun i : Fin P.n => (AdjoinRoot.root (KummerPoly P)) ^ i.val) (kmul P a b) =
      Fintype.linearCombination (Fq P)
          (fun i : Fin P.n => (AdjoinRoot.root (KummerPoly P)) ^ i.val) a *
        Fintype.linearCombination (Fq P)
          (fun i : Fin P.n => (AdjoinRoot.root (KummerPoly P)) ^ i.val) b :=
  evalCoeffs_mul _ _ rootP_pow a b

private lemma sigma_kmul (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0)
    (s : ℕ) (a b : Fin P.n → Fq P) :
    sigma P s (kmul P a b) = kmul P (sigma P s a) (sigma P s b) := by
  apply coeffs_inj hL
  rw [eval_sigma, eval_kmul, eval_sigma, eval_sigma]
  exact evalCoeffs_mul _ _ (scaled_root_pow hL s) a b

private lemma sigma_add (s t : ℕ) (a : Fin P.n → Fq P) :
    sigma P s (sigma P t a) = sigma P (s + t) a := by
  funext e
  simp only [sigma, frob, Nat.add_mul, pow_add, mul_smul]

private lemma sigma_n (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0)
    (a : Fin P.n → Fq P) : sigma P P.n a = a := by
  funext e
  simp only [sigma, frob, pow_mul, hL.2.2.1, one_pow, one_smul]

private lemma sigma_honestU (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0) (z : Fin P.n → Fq P) :
    sigma P (P.m + 1) (kmul P z (sigma P (P.m - 1) z)) =
      kmul P (sigma P (P.m + 1) z) z := by
  rw [sigma_kmul hL, sigma_add, hL.2.2.2.2.1, sigma_n hL]

private lemma sigma_honestV (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0) (z : Fin P.n → Fq P) :
    sigma P P.m (kmul P z (sigma P P.m z)) =
      kmul P z (sigma P P.m z) := by
  rw [sigma_kmul hL, sigma_add, hL.2.2.2.1, sigma_n hL]
  apply coeffs_inj hL
  simp only [eval_kmul]
  exact mul_comm _ _

private lemma honestV_odd (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0)
    (z : Fin P.n → Fq P) (e : Fin P.n)
    (he : e.val % 2 ≠ 0) : kmul P z (sigma P P.m z) e = 0 := by
  have h := congrFun (sigma_honestV hL z) e
  have ho : Odd e.val := Nat.odd_iff.mpr (by omega)
  simp only [sigma, frob, pow_mul, hL.2.1, ho.neg_one_pow, neg_one_smul] at h
  have hh : (2 : Fq P) * kmul P z (sigma P P.m z) e = 0 := by
    change -kmul P z (sigma P P.m z) e = kmul P z (sigma P P.m z) e at h
    rw [two_mul]
    calc
      _ = -kmul P z (sigma P P.m z) e + kmul P z (sigma P P.m z) e :=
        congrArg (fun t => t + kmul P z (sigma P P.m z) e) h.symm
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp hh).resolve_left hL.2.2.2.2.2

private lemma honest_polyU
    (hgrid : Set.BijOn (fun c : Cell P => cellExp c) {c | IsUCell c} {k | k < P.n})
    (v : Fin P.n → Vec (Fq P) P.N)
    (x : Vec (Fq P) P.N) :
    polyU (honestStack v x) = fun e =>
      kmul P (zOf v x) (sigma P (P.m - 1) (zOf v x)) e • Matrix.vecMulVec x x := by
  classical
  funext e
  obtain ⟨c, hc, hce⟩ := hgrid.surjOn e.isLt
  unfold polyU stackU
  rw [Finset.sum_eq_single c]
  · simp only [honestStack, weight, cellWeight, if_neg hc, hce, Uw,
      kcoeff, dif_pos e.isLt]
  · intro d hd hdc
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact hdc (hgrid.injOn hd.1 hc (hd.2.trans hce.symm))
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hce⟩))

private lemma honest_polyV (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0)
    (hgrid : Set.BijOn (fun c : Cell P => cellExp c) {c | ¬ IsUCell c}
      {k | k < P.n ∧ Even k})
    (v : Fin P.n → Vec (Fq P) P.N)
    (x : Vec (Fq P) P.N) :
    polyV (honestStack v x) = fun e =>
      kmul P (zOf v x) (sigma P P.m (zOf v x)) e • Matrix.vecMulVec x x := by
  classical
  funext e
  by_cases he : e.val % 2 = 0
  · have h2 : 2 * (e.val / 2) = e.val := by omega
    obtain ⟨c, hc, hce⟩ := hgrid.surjOn ⟨e.isLt, Nat.even_iff.mpr he⟩
    rw [polyV, if_pos he]
    unfold stackV
    rw [Finset.sum_eq_single c]
    · have hcV : c.2.1 = .V := not_ne_iff.mp hc
      simp only [honestStack, weight, cellWeight, if_pos hcV, hce, Vw, h2,
        kcoeff, dif_pos e.isLt]
    · intro d hd hdc
      exfalso
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      exact hdc (hgrid.injOn hd.1 hc ((hd.2.trans h2).trans hce.symm))
    · intro h
      exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hce.trans h2.symm⟩))
  · rw [polyV, if_neg he, honestV_odd hL _ e he, zero_smul]

private lemma raw_rankOne (a : Fin P.n → Fq P) (x : Vec (Fq P) P.N)
    (b : Fin P.n → Vec (Fq P) P.N) (t : ℕ) :
    rawMulMV (fun e => a e • Matrix.vecMulVec x x) b t =
      rawMul a (fun e => Algebra.dot (b e) x) t • x := by
  classical
  unfold rawMulMV rawMul
  simp only [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · funext k
    simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.smul_apply, Matrix.of_apply,
      dotProduct, Pi.smul_apply, smul_eq_mul, Algebra.dot, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  · simp

private lemma dot_sigma (s : ℕ) (v : Fin P.n → Vec (Fq P) P.N)
    (x : Vec (Fq P) P.N) :
    (fun e => Algebra.dot (sigma P s v e) x) = sigma P s (zOf v x) := by
  funext e
  simp only [sigma, frob, zOf, Algebra.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma sigma_rankOne (s : ℕ) (a : Fin P.n → Fq P)
    (x : Vec (Fq P) P.N) :
    sigma P s (fun e => a e • Matrix.vecMulVec x x) =
      fun e => sigma P s a e • Matrix.vecMulVec x x := by
  funext e
  simp only [sigma, frob, smul_smul, smul_eq_mul]

private lemma reduce_rankOne (a b : Fin P.n → Fq P)
    (x : Vec (Fq P) P.N) :
    reduceP P.n (c0F P) (fun t => rawMul a b t • x) =
      fun e => kmul P a b e • x := by
  funext e
  simp only [reduceP, kmul, add_smul, smul_smul, smul_eq_mul]

private lemma reduce_sub (a b : ℕ → Vec (Fq P) P.N) :
    reduceP P.n (c0F P) (a - b) =
      reduceP P.n (c0F P) a - reduceP P.n (c0F P) b := by
  funext e
  simp only [reduceP, Pi.sub_apply, smul_sub]
  abel

private lemma reduce_honest_product (a : Fin P.n → Fq P)
    (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) (s : ℕ) :
    reduceP P.n (c0F P)
      (rawMulMV (fun e => a e • Matrix.vecMulVec x x) (sigma P s v)) =
      fun e => kmul P a (sigma P s (zOf v x)) e • x := by
  have hr : rawMulMV (fun e => a e • Matrix.vecMulVec x x) (sigma P s v) =
      fun t => rawMul a (fun e => Algebra.dot (sigma P s v e) x) t • x :=
    funext fun t => raw_rankOne a x (sigma P s v) t
  rw [hr, dot_sigma]
  exact reduce_rankOne a _ x

private lemma scalar_ties (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0) (z : Fin P.n → Fq P) :
    (kmul P (kmul P z (sigma P (P.m - 1) z)) (sigma P P.m z) =
      kmul P (kmul P z (sigma P P.m z)) (sigma P (P.m - 1) z)) ∧
    (kmul P (kmul P z (sigma P (P.m - 1) z)) (sigma P (P.m + 1) z) =
      kmul P (sigma P (P.m + 1) (kmul P z (sigma P (P.m - 1) z)))
        (sigma P (P.m - 1) z)) ∧
    (kmul P (kmul P z (sigma P P.m z)) (sigma P (P.m + 1) z) =
      kmul P (sigma P (P.m + 1) (kmul P z (sigma P (P.m - 1) z)))
        (sigma P P.m z)) := by
  rw [sigma_honestU hL]
  constructor
  · apply coeffs_inj hL
    simp only [eval_kmul]
    ring
  constructor
  · apply coeffs_inj hL
    simp only [eval_kmul]
    ring
  · apply coeffs_inj hL
    simp only [eval_kmul]
    ring

private lemma honest_ties_of_laws (hL : P.n ≠ 0 ∧ betaF P ^ P.m = -1 ∧ betaF P ^ P.n = 1 ∧
      P.m + P.m = P.n ∧ P.m + 1 + (P.m - 1) = P.n ∧ (2 : Fq P) ≠ 0)
    (hU : Set.BijOn (fun c : Cell P => cellExp c) {c | IsUCell c} {k | k < P.n})
    (hV : Set.BijOn (fun c : Cell P => cellExp c) {c | ¬ IsUCell c}
      {k | k < P.n ∧ Even k})
    (v : Fin P.n → Vec (Fq P) P.N) (x : Vec (Fq P) P.N) :
    Ties v (honestStack v x) := by
  have ht := scalar_ties hL (zOf v x)
  intro s
  cases s
  · simp only [tiePoly, honest_polyU hU, honest_polyV hL hV, reduce_sub,
      reduce_honest_product, ht.1, sub_self]
  · simp only [tiePoly, honest_polyU hU, sigma_rankOne, reduce_sub,
      reduce_honest_product, ht.2.1, sub_self]
  · simp only [tiePoly, honest_polyU hU, honest_polyV hL hV, sigma_rankOne,
      reduce_sub, reduce_honest_product, ht.2.2, sub_self]

end Algebra

private lemma mainLaws : P0.n ≠ 0 ∧ betaF P0 ^ P0.m = -1 ∧ betaF P0 ^ P0.n = 1 ∧
      P0.m + P0.m = P0.n ∧ P0.m + 1 + (P0.m - 1) = P0.n ∧ (2 : Fq P0) ≠ 0 := by
  refine ⟨by decide, KummerIrr.beta_pow_m, ?_, by decide, by decide, by decide⟩
  have hm : betaF P0 ^ P0.m = -1 := KummerIrr.beta_pow_m
  rw [show P0.n = P0.m * 2 by decide, pow_mul, hm]
  norm_num

theorem honest_ties (v : Fin P0.n → Vec (Fq P0) P0.N) (x : Vec (Fq P0) P0.N) :
    Ties v (honestStack v x) := by
  exact honest_ties_of_laws mainLaws uCell_exp_bijOn vCell_exp_bijOn v x

end Praxis.Proofs.Ties
