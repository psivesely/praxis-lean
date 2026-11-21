import Praxis.Proofs.Classification.Coeff
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Moore
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

section

variable {k F : Type*} [CommSemiring k] [CommSemiring F] [Algebra k F] {n : ℕ}

variable (c : k) (t : F)

def wrap (i j : Fin n) (a : k) : Fin n → k := fun e =>
  (if i.val + j.val = e.val then a else 0) +
    c * (if i.val + j.val = e.val + n then a else 0)

theorem wrap_low (i j : Fin n) (a : k) (h : i.val + j.val < n) :
    wrap c i j a = Pi.single ⟨i.val + j.val, h⟩ a := by
  classical
  ext e
  have hhigh : i.val + j.val ≠ e.val + n := by omega
  simp only [wrap, if_neg hhigh, mul_zero, add_zero, Pi.single_apply]
  congr 1
  exact propext (by rw [Fin.ext_iff]; exact eq_comm)

theorem wrap_high (i j : Fin n) (a : k) (h : n ≤ i.val + j.val) :
    wrap c i j a = Pi.single ⟨i.val + j.val - n, by omega⟩ (c * a) := by
  classical
  ext e
  have he : i.val + j.val = e.val + n ↔
      (⟨i.val + j.val - n, by omega⟩ : Fin n) = e := by
    rw [Fin.ext_iff]
    dsimp
    omega
  simp only [wrap, he]
  rw [if_neg (by omega)]
  by_cases he' : (⟨i.val + j.val - n, by omega⟩ : Fin n) = e
  · subst e
    simp
  · simp [he', Ne.symm he']

theorem kmul_expand (a b : Fin n → k) :
    reduceP n c (rawMul a b) = ∑ i, ∑ j, wrap c i j (a i * b j) := by
  ext e
  simp only [reduceP, rawMul, smul_eq_mul, Finset.sum_apply, wrap,
    Finset.sum_add_distrib, Finset.mul_sum]

noncomputable def evalCoeffs (t : F) : (Fin n → k) →ₗ[k] F where
  toFun a := ∑ e, algebraMap k F (a e) * t ^ e.val
  map_add' a b := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    exact (Algebra.smul_def _ _).symm

@[simp] theorem evalCoeffs_apply (a : Fin n → k) :
    evalCoeffs t a = ∑ e, algebraMap k F (a e) * t ^ e.val := rfl

@[simp] theorem evalCoeffs_single (e : Fin n) (a : k) :
    evalCoeffs t (Pi.single e a) = algebraMap k F a * t ^ e.val := by
  classical
  rw [evalCoeffs_apply, Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem eval_wrap (ht : t ^ n = algebraMap k F c) (i j : Fin n) (a : k) :
    evalCoeffs t (wrap c i j a) = algebraMap k F a * t ^ (i.val + j.val) := by
  classical
  by_cases h : i.val + j.val < n
  · rw [wrap_low c i j a h, evalCoeffs_single]
  · have h' : n ≤ i.val + j.val := by omega
    rw [wrap_high c i j a h', evalCoeffs_single, map_mul]
    have hp : t ^ (i.val + j.val) = t ^ n * t ^ (i.val + j.val - n) := by
      rw [← pow_add, Nat.add_sub_of_le h']
    rw [hp, ht]
    ring

theorem eval_reduce_mul (ht : t ^ n = algebraMap k F c) (a b : Fin n → k) :
    evalCoeffs t (reduceP n c (rawMul a b)) = evalCoeffs t a * evalCoeffs t b := by
  rw [kmul_expand, map_sum]
  simp_rw [map_sum, eval_wrap c t ht]
  simp only [evalCoeffs_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, pow_add]
  ring

end

section

variable {k F : Type*} [CommSemiring k] [CommSemiring F] [Algebra k F] {n N : ℕ}

variable (c : k) (t : F)

theorem rawMulMV_entry (M : KPoly (Algebra.Mat k N) n) (b : KPoly (Algebra.Vec k N) n)
    (r : Fin (N + 1)) (e : ℕ) :
    rawMulMV M b e r = ∑ j, rawMul (fun a => M a r j) (fun a => b a j) e := by
  simp only [rawMulMV, rawMul, Matrix.mulVec, dotProduct, Finset.sum_apply, ite_apply, Pi.zero_apply,
    smul_eq_mul]
  calc
    (∑ a : Fin n, ∑ b' : Fin n,
      if a.val + b'.val = e then ∑ j, M a r j * b b' j else 0) =
      ∑ a : Fin n, ∑ b' : Fin n, ∑ j : Fin (N + 1),
        if a.val + b'.val = e then M a r j * b b' j else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b' _
      split_ifs <;> simp
    _ = _ := by
      conv_lhs =>
        arg 2
        ext a
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

theorem reduceMV_entry (M : KPoly (Algebra.Mat k N) n) (b : KPoly (Algebra.Vec k N) n)
    (r : Fin (N + 1)) :
    (fun e => reduceP n c (rawMulMV M b) e r) =
      ∑ j, reduceP n c (rawMul (fun a => M a r j) (fun a => b a j)) := by
  ext e
  simp only [reduceP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    rawMulMV_entry, Finset.sum_add_distrib, Finset.mul_sum]

theorem eval_reduce_mulVec (ht : t ^ n = algebraMap k F c)
    (M : KPoly (Algebra.Mat k N) n) (b : KPoly (Algebra.Vec k N) n) (r : Fin (N + 1)) :
    evalCoeffs t (fun e => reduceP n c (rawMulMV M b) e r) =
      (Matrix.of (fun i j => evalCoeffs t (fun e => M e i j))).mulVec
        (fun j => evalCoeffs t (fun e => b e j)) r := by
  rw [reduceMV_entry, map_sum]
  simp_rw [eval_reduce_mul c t ht]
  rfl

end

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

theorem evalCoeffs_root (a : KPoly (Fq P0) P0.n) :
    evalCoeffs (AdjoinRoot.root (KummerPoly P0)) a = toK a := by
  rw [evalCoeffs_apply]
  exact (toK_sum a).symm

theorem toK_kmul (a b : KPoly (Fq P0) P0.n) :
    toK (kmul P0 a b) = toK a * toK b := by
  rw [← evalCoeffs_root, kmul, eval_reduce_mul _ _ boolRoot_pow_n,
    evalCoeffs_root, evalCoeffs_root]

theorem toK_reduce_mulVec (M : KPoly (Algebra.Mat (Fq P0) P0.N) P0.n)
    (b : KPoly (Algebra.Vec (Fq P0) P0.N) P0.n) (r : Fin (P0.N + 1)) :
    toK (fun e => reduceP P0.n (c0F P0) (rawMulMV M b) e r) =
      (Matrix.of (fun i j => toK (fun e => M e i j))).mulVec
        (fun j => toK (fun e => b e j)) r := by
  simp_rw [← evalCoeffs_root]
  exact eval_reduce_mulVec (c0F P0) (AdjoinRoot.root (KummerPoly P0)) boolRoot_pow_n M b r

end

end Praxis.Proofs.Classification
