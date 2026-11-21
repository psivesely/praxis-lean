import Praxis.Proofs.Basic
import Praxis.KummerIrr
import Praxis.Kummer
import Praxis.Params
import Praxis.Setting

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open Polynomial

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

noncomputable def vecToK (a : KPoly (Fq P0) P0.n) : KummerField P0 :=
  AdjoinRoot.mk (KummerPoly P0) (∑ e : Fin P0.n, C (a e) * X ^ e.val)

theorem vecToK_sum (a : KPoly (Fq P0) P0.n) :
    vecToK a = ∑ e : Fin P0.n, a e • (AdjoinRoot.root (KummerPoly P0)) ^ e.val := by
  simp [vecToK, map_sum, map_mul, map_pow, AdjoinRoot.mk_C,
    AdjoinRoot.mk_X, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem vec_independent {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) {n d : ℕ}
    (hn : p.natDegree = n) (a : Fin d → Fin n → K)
    (ha : LinearIndependent K a) :
    LinearIndependent K (fun i => ∑ e : Fin n, a i e • (AdjoinRoot.root p) ^ e.val) := by
  let pb : PowerBasis K (AdjoinRoot p) := AdjoinRoot.powerBasis hp
  let b : Module.Basis (Fin n) K (AdjoinRoot p) := pb.basis.reindex (finCongr hn)
  have hb (i : Fin n) : b i = (AdjoinRoot.root p) ^ i.val := by
    simp only [b, Module.Basis.reindex_apply, pb, PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis_gen]
    exact congrArg (fun t : ℕ => (AdjoinRoot.root p) ^ t) (finCongr_symm_apply_coe hn i)
  let f : (Fin n → K) →ₗ[K] AdjoinRoot p := Fintype.linearCombination _ b
  have hf : Function.Injective f := b.linearIndependent.fintypeLinearCombination_injective
  have hm (x : Fin n → K) : f x = ∑ e : Fin n, x e • (AdjoinRoot.root p) ^ e.val := by
    simp [f, Fintype.linearCombination_apply, hb]
  have hh := ha.map' f (LinearMap.ker_eq_bot.mpr hf)
  change LinearIndependent K (fun i => f (a i)) at hh
  simpa only [hm] using hh

theorem vecToK_independent {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) :
    LinearIndependent (Fq P0) (fun i => vecToK (a i)) := by
  have hn : (KummerPoly P0).natDegree = P0.n := by simp [KummerPoly]
  simpa only [← vecToK_sum] using vec_independent (KummerPoly P0)
    KummerIrr.main.ne_zero hn a ha

theorem root_pow_binomial {K : Type*} [CommRing K] (p : K[X]) (n : ℕ) (c : K)
    (hp : p = X ^ n - C c) :
    (AdjoinRoot.root p) ^ n = algebraMap K (AdjoinRoot p) c := by
  subst p
  have h := AdjoinRoot.eval₂_root (X ^ n - C c)
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using h

theorem root_pow_param (P : Params) :
    (AdjoinRoot.root (KummerPoly P)) ^ P.n =
      algebraMap (Fq P) (KummerField P) (c0F P) := by
  have hp : KummerPoly P = (X : (Fq P)[X]) ^ P.n - C (c0F P) := by
    unfold KummerPoly
    rfl
  exact root_pow_binomial (KummerPoly P) P.n (c0F P) hp

theorem root_pow_n :
    (AdjoinRoot.root (KummerPoly P0)) ^ P0.n =
      algebraMap (Fq P0) (KummerField P0) (c0F P0) :=
  root_pow_param P0

theorem root_pow_q :
    (AdjoinRoot.root (KummerPoly P0)) ^ P0.q =
      algebraMap (Fq P0) (KummerField P0) (betaF P0) *
        AdjoinRoot.root (KummerPoly P0) := by
  have hq : P0.q = P0.n * ((P0.q - 1) / P0.n) + 1 := by decide
  calc
    (AdjoinRoot.root (KummerPoly P0)) ^ P0.q =
        (AdjoinRoot.root (KummerPoly P0)) ^ (P0.n * ((P0.q - 1) / P0.n) + 1) :=
      congrArg (fun t : ℕ => (AdjoinRoot.root (KummerPoly P0)) ^ t) hq
    _ = _ := by
      rw [pow_add, pow_one, pow_mul, root_pow_n, ← map_pow]
      have hb : betaF P0 = c0F P0 ^ ((P0.q - 1) / P0.n) := KummerIrr.beta_def
      rw [hb]

theorem frobenius_root (j : ℕ) :
    ((FiniteField.frobeniusAlgHom (Fq P0) (KummerField P0)) ^ j)
        (AdjoinRoot.root (KummerPoly P0)) =
      algebraMap (Fq P0) (KummerField P0) ((betaF P0) ^ j) *
        AdjoinRoot.root (KummerPoly P0) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, map_mul, AlgHom.commutes]
    have hcard : Fintype.card (Fq P0) = P0.q := ZMod.card _
    simp only [FiniteField.frobeniusAlgHom_apply, hcard, root_pow_q, pow_succ, map_mul]
    ring

theorem map_monomial {K E : Type*} [CommRing K] [CommRing E] [Algebra K E]
    (φ : E →ₐ[K] E) (r : E) (b a : K) (e : ℕ)
    (h : φ r = algebraMap K E b * r) :
    φ (a • r ^ e) = (b ^ e * a) • r ^ e := by
  simp only [Algebra.smul_def, map_mul, map_pow, AlgHom.commutes, h, mul_pow]
  ring

theorem vecToK_sigma (j : ℕ) (a : KPoly (Fq P0) P0.n) :
    vecToK (sigma P0 j a) = (vecToK a) ^ (P0.q ^ j) := by
  have hcard : Fintype.card (Fq P0) = P0.q := ZMod.card _
  have hpow (x : KummerField P0) :
      ((FiniteField.frobeniusAlgHom (Fq P0) (KummerField P0)) ^ j) x =
        x ^ (P0.q ^ j) := by
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, hcard]
  rw [← hpow, vecToK_sum, vecToK_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sigma, frob, smul_eq_mul]
  rw [map_monomial _ _ _ _ _ (frobenius_root j), ← pow_mul]

end Praxis.Proofs.Classification
