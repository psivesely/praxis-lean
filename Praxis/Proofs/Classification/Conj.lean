import Praxis.Proofs.Classification.Coeff
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Moore
import Praxis.Params
import Praxis.Setting

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section Generic

variable {k : Type*} [CommRing k] (p : Polynomial k) (n : ℕ) (c β : k)
    (hp : p = Polynomial.X ^ n - Polynomial.C c) (hβ : β ^ n = 1)

def binomialConj (s : ℕ) : AdjoinRoot p →ₐ[k] AdjoinRoot p :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId k (AdjoinRoot p))
    ((algebraMap k (AdjoinRoot p) β) ^ s * AdjoinRoot.root p) (by
      have he := congrArg (fun f : Polynomial k =>
        f.eval₂ (Algebra.ofId k (AdjoinRoot p))
          ((algebraMap k (AdjoinRoot p) β) ^ s * AdjoinRoot.root p)) hp
      rw [he, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      change ((algebraMap k (AdjoinRoot p) β) ^ s * AdjoinRoot.root p) ^ n -
        algebraMap k (AdjoinRoot p) c = 0
      rw [mul_pow, ← pow_mul, Nat.mul_comm s n, pow_mul, ← map_pow, hβ,
        map_one, one_pow, one_mul, root_pow_of_binomial p n c hp, sub_self])

@[simp] theorem binomialConj_root (s : ℕ) :
    binomialConj p n c β hp hβ s (AdjoinRoot.root p) =
      (algebraMap k (AdjoinRoot p) β) ^ s * AdjoinRoot.root p := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

end Generic

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

local instance : NeZero P0.n := ⟨by decide⟩

attribute [local irreducible] KummerPoly

def kConj (s : ℕ) : KummerField P0 →ₐ[Fq P0] KummerField P0 :=
  binomialConj (KummerPoly P0) P0.n (c0F P0) (betaF P0) (kummer_eq P0) beta_pow_n s

@[simp] theorem kConj_root (s : ℕ) :
    kConj s (AdjoinRoot.root (KummerPoly P0)) =
      (algebraMap (Fq P0) (KummerField P0) (betaF P0)) ^ s *
        AdjoinRoot.root (KummerPoly P0) :=
  binomialConj_root _ _ _ _ _ _ s

theorem kConj_toK (s : ℕ) (a : KPoly (Fq P0) P0.n) :
    kConj s (toK a) = toK (sigma P0 s a) := by
  rw [toK_sum, toK_sum]
  simp only [map_sum, map_mul, map_pow, AlgHom.commutes, kConj_root]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sigma, frob, smul_eq_mul, map_mul, map_pow, mul_pow]
  rw [← pow_mul]
  ring

@[simp] theorem kConj_zero (a : KummerField P0) : kConj 0 a = a := by
  obtain ⟨b, rfl⟩ := coeffEquiv.surjective a
  simp only [coeffEquiv_apply, kConj_toK, sigma_zero]

theorem kConj_add (s t : ℕ) (a : KummerField P0) :
    kConj (s + t) a = kConj s (kConj t a) := by
  obtain ⟨b, rfl⟩ := coeffEquiv.surjective a
  simp only [coeffEquiv_apply, kConj_toK, sigma_add]

@[simp] theorem kConj_n (a : KummerField P0) : kConj P0.n a = a := by
  obtain ⟨b, rfl⟩ := coeffEquiv.surjective a
  simp only [coeffEquiv_apply, kConj_toK, sigma_n]

@[simp] theorem toK_constant (a : Fq P0) :
    toK (Pi.single (0 : Fin P0.n) a) = algebraMap (Fq P0) (KummerField P0) a := by
  rw [toK_single]
  simp only [Fin.val_zero, pow_zero, mul_one]

theorem kConj_fixed (z : KummerField P0) :
    kConj 1 z = z ↔ ∃ a : Fq P0, algebraMap (Fq P0) (KummerField P0) a = z := by
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := coeffEquiv.surjective z
    rw [coeffEquiv_apply] at hb
    have hs : sigma P0 1 b = b := by
      apply toK_injective
      rw [← kConj_toK, hb, hz]
    have hsingle : b = Pi.single (0 : Fin P0.n) (b 0) := by
      ext e
      by_cases he : e = 0
      · subst e
        simp
      · have hβ : betaF P0 ^ e.val ≠ 1 :=
          pow_ne_one_of_lt_orderOf (by exact fun h => he (Fin.ext h))
            (by rw [KummerIrr.main_betaLaws.2.1]; exact e.isLt)
        have h := congrFun hs e
        change betaF P0 ^ (1 * e.val) * b e = b e at h
        rw [one_mul] at h
        have hb0 : b e = 0 := by
          have heq : (betaF P0 ^ e.val - 1) * b e = 0 := by rw [sub_mul, h, one_mul, sub_self]
          exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hβ)
        simp [Pi.single_eq_of_ne he, hb0]
    refine ⟨b 0, ?_⟩
    rw [← toK_constant, ← hsingle, hb]
  · rintro ⟨a, rfl⟩
    exact (kConj 1).commutes a

theorem kConj_consecutive_fixed (z : KummerField P0)
    (h₁ : kConj (P0.m - 1) z = z) (h₂ : kConj P0.m z = z) :
    ∃ a : Fq P0, algebraMap (Fq P0) (KummerField P0) a = z := by
  apply (kConj_fixed z).mp
  calc
    kConj 1 z = kConj 1 (kConj (P0.m - 1) z) := congrArg (kConj 1) h₁.symm
    _ = kConj (1 + (P0.m - 1)) z := (kConj_add _ _ _).symm
    _ = z := by simpa only [show 1 + (P0.m - 1) = P0.m by decide] using h₂

end

end Praxis.Proofs.Classification
