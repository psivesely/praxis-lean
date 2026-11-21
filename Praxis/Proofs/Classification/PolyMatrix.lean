import Praxis.Proofs.Classification.Serialization
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.CoeffMul
import Praxis.Params
import Praxis.Setting

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section Generic

variable {k F : Type*} [CommSemiring k] [CommSemiring F] [Algebra k F] {n : ℕ}

variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

def evalMatrix (t : F) (p : Fin n → Matrix I J k) : Matrix I J F :=
  fun i j => evalCoeffs t (fun e => p e i j)

theorem evalCoeffs_const_mul (t : F) (a : Fin n → k) (r : k) :
    evalCoeffs t (fun e => r * a e) = algebraMap k F r * evalCoeffs t a := by
  change evalCoeffs t (r • a) = _
  rw [map_smul, Algebra.smul_def]

theorem evalCoeffs_mul_const (t : F) (a : Fin n → k) (r : k) :
    evalCoeffs t (fun e => a e * r) = evalCoeffs t a * algebraMap k F r := by
  simp_rw [mul_comm _ r]
  rw [evalCoeffs_const_mul, mul_comm]

theorem evalCoeffs_sum (t : F) {A : Type*} [Fintype A] (f : Fin n → A → k) :
    evalCoeffs t (fun e => ∑ a, f e a) = ∑ a, evalCoeffs t (fun e => f e a) := by
  have heq : (fun e => ∑ a, f e a) = ∑ a, (fun e => f e a) := by
    funext e
    simp only [Finset.sum_apply]
  rw [heq, map_sum]

theorem evalCoeffs_dot (t : F) {A : Type*} [Fintype A] (p : Fin n → A → k) (x : A → k) :
    evalCoeffs t (fun e => dotProduct (p e) x) =
      dotProduct (fun i => evalCoeffs t (fun e => p e i)) (fun i => algebraMap k F (x i)) := by
  simp only [dotProduct]
  rw [evalCoeffs_sum]
  simp only [evalCoeffs_mul_const]

theorem evalMatrix_mul_left (t : F) (B : Matrix L I k) (p : Fin n → Matrix I J k) :
    evalMatrix t (fun e => B * p e) = B.map (algebraMap k F) * evalMatrix t p := by
  ext i j
  simp only [evalMatrix, Matrix.mul_apply, Matrix.map_apply]
  have h : (fun e => ∑ r, B i r * p e r j) =
      ∑ r, (fun e => B i r * p e r j) := by
    funext e
    simp only [Finset.sum_apply]
  rw [h, map_sum]
  simp only [evalCoeffs_const_mul]

theorem evalMatrix_mul_right (t : F) (p : Fin n → Matrix I J k) (B : Matrix J L k) :
    evalMatrix t (fun e => p e * B) = evalMatrix t p * B.map (algebraMap k F) := by
  ext i j
  simp only [evalMatrix, Matrix.mul_apply, Matrix.map_apply]
  have h : (fun e => ∑ r, p e i r * B r j) =
      ∑ r, (fun e => p e i r * B r j) := by
    funext e
    simp only [Finset.sum_apply]
  rw [h, map_sum]
  simp only [evalCoeffs_mul_const]

theorem evalMatrix_symm (t : F) (p : Fin n → Matrix I I k) (h : ∀ e, (p e).IsSymm) :
    (evalMatrix t p).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold evalMatrix
  congr 1
  funext e
  exact (h e).apply i j

end Generic

section Assembly

variable {I : Type*} [Fintype I]

def assembleU (W : Cell P0 → Matrix I I (Fq P0)) : Fin P0.n → Matrix I I (Fq P0) :=
  fun e => ∑ c ∈ Finset.univ.filter (fun c : Cell P0 => IsUCell c ∧ cellExp c = e.val), W c

def assembleV (W : Cell P0 → Matrix I I (Fq P0)) : Fin P0.n → Matrix I I (Fq P0) :=
  fun e => if e.val % 2 = 0 then
    ∑ c ∈ Finset.univ.filter (fun c : Cell P0 => ¬IsUCell c ∧ cellExp c = 2 * (e.val / 2)), W c else 0

theorem assembleU_factor {J : Type*} [Fintype J] (B : Matrix I J (Fq P0))
    (C : Cell P0 → Matrix J J (Fq P0)) :
    assembleU (fun c => B * C c * B.transpose) = fun e => B * assembleU C e * B.transpose := by
  funext e
  simp only [assembleU, Matrix.mul_sum, Matrix.sum_mul]

theorem assembleV_factor {J : Type*} [Fintype J] (B : Matrix I J (Fq P0))
    (C : Cell P0 → Matrix J J (Fq P0)) :
    assembleV (fun c => B * C c * B.transpose) = fun e => B * assembleV C e * B.transpose := by
  funext e
  simp only [assembleV]
  split_ifs <;> simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_zero, Matrix.zero_mul]

theorem assembleU_symm (W : Cell P0 → Matrix I I (Fq P0)) (h : ∀ c, (W c).IsSymm) :
    ∀ e, (assembleU W e).IsSymm := by
  intro e
  change (assembleU W e).transpose = assembleU W e
  simp only [assembleU, Matrix.transpose_sum]
  exact Finset.sum_congr rfl (fun c _ => (h c).eq)

theorem assembleV_symm (W : Cell P0 → Matrix I I (Fq P0)) (h : ∀ c, (W c).IsSymm) :
    ∀ e, (assembleV W e).IsSymm := by
  intro e
  unfold assembleV
  split_ifs
  · change (∑ c ∈ Finset.univ.filter (fun c : Cell P0 => ¬IsUCell c ∧
        cellExp c = 2 * (e.val / 2)), W c).transpose = _
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl (fun c _ => (h c).eq)
  · exact Matrix.isSymm_zero

end Assembly

end

end Praxis.Proofs.Classification
