import Praxis.Proofs.Classification.Moore
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

local instance kummerIrr : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

theorem kummer_monic : (KummerPoly P0).Monic := by
  unfold KummerPoly
  generalize hn : P0.n = n
  exact Polynomial.monic_X_pow_sub_C (c0F P0) (n := n) (by
    have hpos : P0.n ≠ 0 := by decide
    omega)

theorem kummer_degree : (KummerPoly P0).natDegree = P0.n := by
  unfold KummerPoly
  generalize P0.n = n
  exact Polynomial.natDegree_X_pow_sub_C (n := n) (r := c0F P0)

theorem kummer_eq (P : Params) : KummerPoly P = Polynomial.X ^ P.n - Polynomial.C (c0F P) := rfl

attribute [local irreducible] KummerPoly

def coeffBasis : Module.Basis (Fin P0.n) (Fq P0) (KummerField P0) :=
  (AdjoinRoot.powerBasis' (g := KummerPoly P0) kummer_monic).basis.reindex (finCongr kummer_degree)

theorem coeffBasis_apply (e : Fin P0.n) :
    coeffBasis e = AdjoinRoot.root (KummerPoly P0) ^ e.val := by
  simp only [coeffBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  exact congrArg (fun t : ℕ => AdjoinRoot.root (KummerPoly P0) ^ t)
    (finCongr_symm_apply_coe kummer_degree e)

theorem toK_sum (a : KPoly (Fq P0) P0.n) :
    toK a = ∑ e, algebraMap (Fq P0) (KummerField P0) (a e) *
      AdjoinRoot.root (KummerPoly P0) ^ e.val := by
  simp [toK, map_sum, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

def coeffEquiv : KPoly (Fq P0) P0.n ≃ₗ[Fq P0] KummerField P0 :=
  coeffBasis.equivFun.symm

theorem coeffEquiv_apply (a : KPoly (Fq P0) P0.n) : coeffEquiv a = toK a := by
  rw [toK_sum, coeffEquiv, Module.Basis.equivFun_symm_apply]
  simp_rw [coeffBasis_apply, Algebra.smul_def]

theorem toK_injective : Function.Injective toK := by
  intro a b h
  exact coeffEquiv.injective ((coeffEquiv_apply a).trans (h.trans (coeffEquiv_apply b).symm))

@[simp] theorem toK_zero : toK 0 = 0 := by
  rw [← coeffEquiv_apply, map_zero]

@[simp] theorem toK_add (a b : KPoly (Fq P0) P0.n) :
    toK (a + b) = toK a + toK b := by
  simp only [← coeffEquiv_apply, map_add]

@[simp] theorem toK_sub (a b : KPoly (Fq P0) P0.n) :
    toK (a - b) = toK a - toK b := by
  simp only [← coeffEquiv_apply, map_sub]

@[simp] theorem toK_smul (r : Fq P0) (a : KPoly (Fq P0) P0.n) :
    toK (r • a) = algebraMap (Fq P0) (KummerField P0) r * toK a := by
  rw [← coeffEquiv_apply, map_smul, coeffEquiv_apply]
  exact Algebra.smul_def _ _

@[simp] theorem toK_sum_finset {ι : Type*} (s : Finset ι)
    (a : ι → KPoly (Fq P0) P0.n) :
    toK (∑ i ∈ s, a i) = ∑ i ∈ s, toK (a i) := by
  simp only [← coeffEquiv_apply, map_sum]

@[simp] theorem toK_single (e : Fin P0.n) (a : Fq P0) :
    toK (Pi.single e a) = algebraMap (Fq P0) (KummerField P0) a *
      AdjoinRoot.root (KummerPoly P0) ^ e.val := by
  classical
  rw [toK_sum, Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem root_pow_of_binomial {k : Type*} [CommRing k] (p : Polynomial k)
    (n : ℕ) (c : k) (hp : p = Polynomial.X ^ n - Polynomial.C c) :
    AdjoinRoot.root p ^ n = algebraMap k (AdjoinRoot p) c := by
  have h : AdjoinRoot.mk p (Polynomial.X ^ n - Polynomial.C c) = 0 := by
    rw [← hp]
    exact AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

theorem boolRoot_pow_n : AdjoinRoot.root (KummerPoly P0) ^ P0.n =
    algebraMap (Fq P0) (KummerField P0) (c0F P0) :=
  root_pow_of_binomial (KummerPoly P0) P0.n (c0F P0) (kummer_eq P0)

theorem beta_pow_n : betaF P0 ^ P0.n = 1 := by
  rw [← KummerIrr.main_betaLaws.2.1]
  exact pow_orderOf_eq_one _

@[simp] theorem sigma_zero {V : Type*} [MulAction (Fq P0) V]
    (a : KPoly V P0.n) : sigma P0 0 a = a := by
  ext e
  simp [sigma, frob]

theorem sigma_add {V : Type*} [MulAction (Fq P0) V]
    (s t : ℕ) (a : KPoly V P0.n) :
    sigma P0 (s + t) a = sigma P0 s (sigma P0 t a) := by
  ext e
  simp [sigma, frob, add_mul, pow_add, mul_smul]

@[simp] theorem sigma_n {V : Type*} [MulAction (Fq P0) V]
    (a : KPoly V P0.n) : sigma P0 P0.n a = a := by
  ext e
  simp [sigma, frob, pow_mul, beta_pow_n]

theorem sigma_injective {V : Type*} [MulAction (Fq P0) V] (s : ℕ) :
    Function.Injective (sigma P0 s : KPoly V P0.n → KPoly V P0.n) := by
  intro a b h
  funext e
  have hb : betaF P0 ≠ 0 := by
    intro hz
    have hbn := beta_pow_n
    rw [hz, zero_pow (by decide : P0.n ≠ 0)] at hbn
    exact zero_ne_one hbn
  have he := congrFun h e
  change (betaF P0 ^ (s * e.val)) • a e = (betaF P0 ^ (s * e.val)) • b e at he
  have := congrArg (fun x => (betaF P0 ^ (s * e.val))⁻¹ • x) he
  simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hb), one_smul] using this

end

end Praxis.Proofs.Classification
