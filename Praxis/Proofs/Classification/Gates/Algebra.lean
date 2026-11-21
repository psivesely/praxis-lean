import Praxis.Proofs.Classification.Moore
import Praxis.Proofs.Ties.Grid
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Praxis.Grid
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 16384

namespace Praxis.Proofs.Classification.GateAlgebra

open Praxis.Algebra (Vec)

noncomputable instance kummerField : Fact (Irreducible (KummerPoly P0)) :=
  ⟨Praxis.KummerIrr.main⟩

abbrev k := Fq P0

abbrev F := KummerField P0

noncomputable abbrev emb : k →+* F := algebraMap k F

noncomputable def root : F := AdjoinRoot.root (KummerPoly P0)

lemma toK_sum (a : KPoly k P0.n) :
    toK a = ∑ e, emb (a e) * root ^ e.val := by
  simp [toK, emb, root, map_sum, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

noncomputable def eval : KPoly k P0.n →ₗ[k] F where
  toFun := toK
  map_add' a b := by simp [toK_sum, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    simp [toK_sum, emb, Algebra.smul_def, map_mul, Finset.mul_sum, mul_assoc]

lemma beta_pow_n : betaF P0 ^ P0.n = 1 := by
  rw [← Praxis.KummerIrr.main_betaLaws.2.1]
  exact pow_orderOf_eq_one _

lemma beta_ne_zero : betaF P0 ≠ 0 := by
  intro h
  have hn : P0.n ≠ 0 := by decide
  simpa [h, hn] using beta_pow_n

lemma root_power {K : Type*} [Field K] (p : Polynomial K)
    [Fact (Irreducible p)] (n : ℕ) (c : K)
    (hp : p = Polynomial.X^n - Polynomial.C c) :
    AdjoinRoot.root p ^ n = algebraMap K (AdjoinRoot p) c := by
  have h := congrArg (fun q : Polynomial K =>
    q.eval₂ (AdjoinRoot.of p) (AdjoinRoot.root p)) hp
  rw [AdjoinRoot.eval₂_root, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h.symm

lemma poly_formula (P : Params) [Fact (Nat.Prime P.q)] :
    KummerPoly P = Polynomial.X ^ P.n - Polynomial.C (c0F P) := by
  rfl

lemma root_pow_n : root ^ P0.n = emb (c0F P0) := by
  exact root_power (KummerPoly P0) P0.n (c0F P0) (poly_formula P0)

noncomputable def conjugate (s : ℕ) : F →ₐ[k] F :=
  AdjoinRoot.liftAlgHom (KummerPoly P0) (Algebra.ofId k F)
    (emb (betaF P0 ^ s) * root) (by
      simp only [KummerPoly, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm s P0.n, pow_mul,
        beta_pow_n, one_pow, map_one, one_mul, root_pow_n]
      exact sub_self _)

lemma conjugate_root (s : ℕ) : conjugate s root = emb (betaF P0 ^ s) * root := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

lemma conjugate_toK (s : ℕ) (a : KPoly k P0.n) :
    conjugate s (toK a) = toK (sigma P0 s a) := by
  simp only [toK_sum, map_sum, map_mul, map_pow, conjugate_root]
  apply Finset.sum_congr rfl
  intro e _
  change _ = emb (betaF P0 ^ (s * e.val) * a e) * root ^ e.val
  rw [(conjugate s).commutes, mul_pow]
  simp only [map_mul, map_pow, pow_mul]
  ring

lemma sigma_add (s t : ℕ) (a : KPoly k P0.n) :
    sigma P0 s (sigma P0 t a) = sigma P0 (s + t) a := by
  ext e
  simp [sigma, frob, add_mul, pow_add, mul_assoc]

lemma sigma_zero (a : KPoly k P0.n) : sigma P0 0 a = a := by
  ext e
  simp [sigma, frob]

lemma sigma_period (s : ℕ) (a : KPoly k P0.n) :
    sigma P0 (s + P0.n) a = sigma P0 s a := by
  ext e
  simp [sigma, frob, add_mul, pow_add, pow_mul, beta_pow_n]

noncomputable def sigmaLin (s : ℕ) : KPoly k P0.n →ₗ[k] KPoly k P0.n where
  toFun := sigma P0 s
  map_add' a b := by ext e; simp [sigma, frob, mul_add]
  map_smul' a b := by ext e; simp [sigma, frob, mul_left_comm]

lemma sigma_injective (s : ℕ) : Function.Injective (sigma P0 s : KPoly k P0.n → _) := by
  intro a b h
  ext e
  exact mul_left_cancel₀ (pow_ne_zero _ beta_ne_zero) (congrFun h e)

lemma fold_pair {E : Type*} [CommRing E] {n : ℕ} (r c u : E)
    (hr : r ^ n = c) (i j : Fin n) :
    (∑ e : Fin n, ((if i.val+j.val = e.val then u else 0) +
      (if i.val+j.val = e.val+n then c*u else 0)) * r^e.val) = u*r^(i.val+j.val) := by
  classical
  by_cases h : i.val+j.val < n
  · rw [Finset.sum_eq_single (⟨i.val+j.val, h⟩ : Fin n)]
    · have hn : i.val+j.val ≠ i.val+j.val+n := by have := i.isLt; omega
      rw [if_neg hn, add_zero]
      simp only [ite_true]
    · intro e _ he
      have hne : i.val+j.val ≠ e.val := by
        intro hh
        apply he
        exact Fin.ext hh.symm
      have hne' : i.val+j.val ≠ e.val+n := by omega
      simp [hne, hne']
    · simp
  · have hge : n ≤ i.val+j.val := by omega
    have hlt : i.val+j.val-n < n := by have := i.isLt; have := j.isLt; omega
    rw [Finset.sum_eq_single (⟨i.val+j.val-n, hlt⟩ : Fin n)]
    · have hne : i.val+j.val ≠ i.val+j.val-n := by have := i.isLt; omega
      have he : i.val+j.val = i.val+j.val-n+n := by omega
      rw [if_neg hne, if_pos he, zero_add]
      calc
        c*u*r^(i.val+j.val-n) = u*(r^(i.val+j.val-n)*r^n) := by rw [hr]; ring
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel hge]
    · intro e _ he
      have hne : i.val+j.val ≠ e.val := by omega
      have hne' : i.val+j.val ≠ e.val+n := by
        intro hh
        apply he
        apply Fin.ext
        change e.val = i.val+j.val-n
        omega
      simp [hne, hne']
    · simp

lemma eval_product {K E : Type*} [CommRing K] [CommRing E] (f : K →+* E)
    {n : ℕ} (c : K) (r : E) (hr : r^n = f c) (a b : Fin n → K) :
    (∑ e : Fin n, f (reduceP n c (rawMul a b) e) * r^e.val) =
      (∑ i : Fin n, f (a i)*r^i.val) * (∑ j : Fin n, f (b j)*r^j.val) := by
  classical
  have hf (p : Prop) [Decidable p] (u : K) :
      f (if p then u else 0) = if p then f u else 0 := by
    split_ifs <;> simp
  calc
    _ = ∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        ((if i.val+j.val=e.val then f (a i*b j) else 0) +
        (if i.val+j.val=e.val+n then f c*f (a i*b j) else 0))*r^e.val := by
      simp only [reduceP, rawMul, smul_eq_mul, map_add, map_sum, map_mul,
        hf, add_mul, Finset.sum_mul, Finset.mul_sum,
        Finset.sum_add_distrib, ite_mul, mul_ite, mul_zero, zero_mul]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ e : Fin n,
        ((if i.val+j.val=e.val then f (a i*b j) else 0) +
        (if i.val+j.val=e.val+n then f c*f (a i*b j) else 0))*r^e.val := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, f (a i*b j)*r^(i.val+j.val) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact fold_pair r (f c) (f (a i*b j)) hr i j
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, pow_add]
      ring

lemma toK_kmul (a b : KPoly k P0.n) : toK (kmul P0 a b) = toK a * toK b := by
  simp only [toK_sum, kmul]
  exact eval_product emb (c0F P0) root root_pow_n a b

lemma raw_odd {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ}
    (a : Fin n → K) (t : ℕ) (ht : t % 2 = 1) :
    rawMul a (fun j => (-1 : K)^j.val * a j) t = 0 := by
  have hs : rawMul a (fun j => (-1 : K)^j.val * a j) t =
      -rawMul a (fun j => (-1 : K)^j.val * a j) t := by
    unfold rawMul
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_eq_mul]
    by_cases hh : i.val+j.val=t
    · rw [if_pos (by omega), if_pos hh]
      rcases Nat.mod_two_eq_zero_or_one i.val with hi | hi
      · have hj : j.val%2=1 := by omega
        simp only [neg_one_pow_eq_pow_mod_two, hi, hj, pow_zero, pow_one]
        ring
      · have hj : j.val%2=0 := by omega
        simp only [neg_one_pow_eq_pow_mod_two, hi, hj, pow_zero, pow_one]
        ring
    · rw [if_neg (by omega), if_neg hh, neg_zero]
  have hz : (2 : K) * rawMul a (fun j => (-1 : K)^j.val * a j) t = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_left h2

lemma norm_odd (a : KPoly k P0.n) (e : Fin P0.n) (he : e.val % 2 ≠ 0) :
    kmul P0 a (sigma P0 P0.m a) e = 0 := by
  have h2 : (2 : k) ≠ 0 := by decide
  have hsig : sigma P0 P0.m a = fun j => (-1 : k)^j.val * a j := by
    ext j
    simp only [sigma, frob, smul_eq_mul, pow_mul, Praxis.KummerIrr.main_betaLaws.2.2]
  have hn : P0.n % 2 = 0 := by decide
  rw [kmul, reduceP, hsig, raw_odd h2 a e.val (by omega),
    raw_odd h2 a (e.val+P0.n) (by omega)]
  simp

lemma eval_apply (a : KPoly k P0.n) : eval a = toK a := rfl

lemma conjugate_emb (s : ℕ) (a : k) : conjugate s (emb a) = emb a :=
  (conjugate s).commutes a

lemma sigma_n (a : KPoly k P0.n) : sigma P0 P0.n a = a := by
  simpa only [zero_add, sigma_zero] using sigma_period 0 a

lemma weight_coefficients (v : Fin P0.n → Vec k P0.N)
    (xs : Finset (Vec k P0.N)) (e : Vec k P0.N → k)
    (h : ∀ c, ∑ x ∈ xs, e x * weight v x c = 0) :
    (∀ i, ∑ x ∈ xs, e x * kmul P0 (zOf v x)
      (sigma P0 (P0.m-1) (zOf v x)) i = 0) ∧
    (∀ i, ∑ x ∈ xs, e x * kmul P0 (zOf v x)
      (sigma P0 P0.m (zOf v x)) i = 0) := by
  constructor
  · intro i
    obtain ⟨c, hc, hci⟩ := Ties.uCell_exp_bijOn.surjOn i.isLt
    have hc' : c.2.1 ≠ .V := hc
    simpa [weight, cellWeight, hc', Uw, hci, kcoeff, i.isLt] using h c
  · intro i
    by_cases hi : i.val % 2 = 0
    · have heven : Even i.val := ⟨i.val/2, by omega⟩
      obtain ⟨c, hc, hci⟩ := Ties.vCell_exp_bijOn.surjOn ⟨i.isLt, heven⟩
      have hc' : c.2.1 = .V := Classical.not_not.mp hc
      have hdiv : 2*(i.val/2)=i.val := by omega
      simpa [weight, cellWeight, hc', Vw, hci, hdiv, kcoeff, i.isLt] using h c
    · simp only [norm_odd _ i hi, mul_zero, Finset.sum_const_zero]

lemma sum_product_zero (xs : Finset (Vec k P0.N)) (e : Vec k P0.N → k)
    (a b : Vec k P0.N → KPoly k P0.n)
    (h : ∀ i, ∑ x ∈ xs, e x * kmul P0 (a x) (b x) i = 0) :
    ∑ x ∈ xs, emb (e x) * toK (a x) * toK (b x) = 0 := by
  have hz : (∑ x ∈ xs, e x • kmul P0 (a x) (b x)) = 0 := by
    ext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h i
  calc
    _ = eval (∑ x ∈ xs, e x • kmul P0 (a x) (b x)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [map_smul]
      rw [eval_apply, Algebra.smul_def, toK_kmul]
      ring
    _ = 0 := by rw [hz, map_zero]

lemma scalar_partners (v : Fin P0.n → Vec k P0.N)
    (xs : Finset (Vec k P0.N)) (e : Vec k P0.N → k)
    (h : ∀ c, ∑ x ∈ xs, e x * weight v x c = 0) :
    ∀ r : Fin 3, ∑ x ∈ xs, emb (e x) * toK (zOf v x) *
      toK (sigma P0 (P0.m-1+r.val) (zOf v x)) = 0 := by
  obtain ⟨hu, hv⟩ := weight_coefficients v xs e h
  have hu' := sum_product_zero xs e (zOf v)
    (fun x => sigma P0 (P0.m-1) (zOf v x)) hu
  have hv' := sum_product_zero xs e (zOf v)
    (fun x => sigma P0 P0.m (zOf v x)) hv
  have hp := congrArg (conjugate (P0.m+1)) hu'
  simp only [map_sum, map_mul, map_zero, conjugate_emb, conjugate_toK,
    sigma_add, show (P0.m+1)+(P0.m-1)=P0.n by decide, sigma_n] at hp
  intro r
  fin_cases r
  · simpa only [Fin.val_zero, add_zero] using hu'
  · change (∑ x ∈ xs, emb (e x) * toK (zOf v x) *
      toK (sigma P0 (P0.m-1+1) (zOf v x))) = 0
    rw [show P0.m-1+1=P0.m by decide]
    exact hv'
  · change (∑ x ∈ xs, emb (e x) * toK (zOf v x) *
      toK (sigma P0 (P0.m-1+2) (zOf v x))) = 0
    rw [show P0.m-1+2=P0.m+1 by decide]
    convert hp using 1
    apply Finset.sum_congr rfl
    intro x hx
    ring

end Praxis.Proofs.Classification.GateAlgebra
