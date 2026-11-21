import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Trans.AlgModel

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace Praxis.Algebra.Trans

theorem primitive_left_inverse {n q : ℕ} (B : Matrix (Fin n) (Fin q) ℤ)
    (hB : PrimitiveMatrix B) :
    ∃ L : Matrix (Fin q) (Fin n) ℤ, L * B = 1 := by
  let f := B.vecMulLinear.toAddMonoidHom
  have ht : AddMonoidHom.range f = ⊤ := by
    apply top_le_iff.mp
    rw [← hB]
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, Matrix.single_one_vecMul i B⟩
  have hs (j : Fin q) : ∃ v : Fin n → ℤ, v ᵥ* B = Pi.single j 1 := by
    have hm : Pi.single j 1 ∈ AddMonoidHom.range f := by rw [ht]; trivial
    exact hm
  choose L hL using hs
  refine ⟨L, ?_⟩
  ext j k
  exact (congrFun (hL j) k).trans (by simp [Pi.single_apply, Matrix.one_apply, eq_comm])

private theorem ratMatrix_mul {m n q : ℕ} (B : Matrix (Fin m) (Fin n) ℤ)
    (C : Matrix (Fin n) (Fin q) ℤ) :
    ratMatrix (B * C) = ratMatrix B * ratMatrix C := Matrix.map_mul

private theorem ratMatrix_one (q : ℕ) :
    ratMatrix (1 : Matrix (Fin q) (Fin q) ℤ) = 1 := by
  simp [ratMatrix]

theorem integral_factor_of_rational_columns {n q k : ℕ}
    (N : Matrix (Fin n) (Fin q) ℤ) (K : Matrix (Fin n) (Fin k) ℤ)
    (hN : PrimitiveMatrix N)
    (hK : ∀ j, ∃ a : Fin q → ℚ,
      (fun i => (K i j : ℚ)) = (ratMatrix N).mulVec a) :
    ∃ A : Matrix (Fin q) (Fin k) ℤ, K = N * A := by
  obtain ⟨L, hL⟩ := primitive_left_inverse N hN
  refine ⟨L * K, ?_⟩
  ext i j
  apply (Int.cast_injective (α := ℚ))
  obtain ⟨a, ha⟩ := hK j
  have hc : (ratMatrix N).mulVec ((ratMatrix L).mulVec (fun i => (K i j : ℚ))) =
      (fun i => (K i j : ℚ)) := by
    rw [ha, Matrix.mulVec_mulVec a (ratMatrix L) (ratMatrix N),
      ← ratMatrix_mul, hL, ratMatrix_one,
      Matrix.one_mulVec]
  have hh := congrFun hc i
  simpa only [ratMatrix_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    ratMatrix, Matrix.map_apply, Int.coe_castRingHom, Int.cast_sum, Int.cast_mul] using hh.symm

theorem pulledNormal_old_entry {n r q : ℕ} (T : TransitionInput n r q)
    (i : Fin n) (j : Fin q) :
    T.pulledNormal i.castSucc j = ∑ l, T.old i l * T.imageNormal l.castSucc j := by
  simp [TransitionInput.pulledNormal, Matrix.mul_apply, oldBlock]

theorem pulledNormal_mulVec {n r q : ℕ} (T : TransitionInput n r q)
    (a : Fin q → ℚ) :
    (ratMatrix T.pulledNormal).mulVec a =
      T.pullbackQ ((ratMatrix T.imageNormal).mulVec a) := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [TransitionInput.pulledNormal, TransitionInput.pullbackQ,
      ratMatrix, Matrix.mulVec, dotProduct]
  · simp only [TransitionInput.pullbackQ, Fin.snoc_castSucc]
    change (∑ j, (T.pulledNormal k.castSucc j : ℚ) * a j) =
      ∑ l, (T.old k l : ℚ) * ∑ j, (T.imageNormal l.castSucc j : ℚ) * a j
    simp only [pulledNormal_old_entry, Int.cast_sum, Int.cast_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring

theorem pulledNormal_factor {n r q : ℕ} (T : TransitionInput n r q)
    (hN : T.OrdinaryNormals) (hW : T.WholeNormalPullback)
    (hI : T.ImageNormals) :
    ∃ A : Matrix (Fin q) (Fin q) ℤ, T.pulledNormal = T.normal * A := by
  apply integral_factor_of_rational_columns T.normal T.pulledNormal hN.1
  intro j
  have hi : rationalNormal T.event T.imageQ
      ((ratMatrix T.imageNormal).mulVec (Pi.single j 1)) :=
    (hI.2.1 _).mpr ⟨Pi.single j 1, rfl⟩
  have hp := (hW _).mpr ⟨_, hi, pulledNormal_mulVec T (Pi.single j 1)⟩
  obtain ⟨a, ha⟩ := (hN.2 _).mp hp
  refine ⟨a, ?_⟩
  have he : (ratMatrix T.pulledNormal).col j =
      (fun i => (T.pulledNormal i j : ℚ)) := by ext i; rfl
  rwa [Matrix.mulVec_single_one, he] at ha

theorem pulledNormal_factor_det_ne_zero {n r q : ℕ} (T : TransitionInput n r q)
    (hB : T.OldLattice) (hI : T.ImageNormals)
    (A : Matrix (Fin q) (Fin q) ℤ) (hA : T.pulledNormal = T.normal * A) :
    A.det ≠ 0 := by
  obtain ⟨L, hL⟩ := primitive_left_inverse T.old hB
  obtain ⟨pivot, hp⟩ := hI.2.2
  have ho : T.old * oldBlock T.imageNormal = oldBlock T.normal * A := by
    ext i j
    have hh := congrFun (congrFun hA i.castSucc) j
    simpa only [TransitionInput.pulledNormal, Fin.snoc_castSucc, Matrix.mul_apply,
      oldBlock, Matrix.submatrix_apply, id_eq] using hh
  have hf : oldBlock T.imageNormal = (L * oldBlock T.normal) * A := by
    calc
      _ = (L * T.old) * oldBlock T.imageNormal := by rw [hL, Matrix.one_mul]
      _ = L * (T.old * oldBlock T.imageNormal) := Matrix.mul_assoc _ _ _
      _ = _ := by rw [ho, ← Matrix.mul_assoc]
  have hm : (oldBlock T.imageNormal).submatrix pivot id =
      ((L * oldBlock T.normal).submatrix pivot id) * A := by
    rw [hf]
    simpa using
      (Matrix.submatrix_mul_equiv (L * oldBlock T.normal) A pivot (Equiv.refl _) id).symm
  rw [hm, Matrix.det_mul] at hp
  exact (mul_ne_zero_iff.mp hp).2

theorem minor_natAbs_factor {n q : ℕ} (N : Matrix (Fin n) (Fin q) ℤ)
    (A : Matrix (Fin q) (Fin q) ℤ) (pivot : Fin q → Fin n) :
    ((N * A).submatrix pivot id).det.natAbs =
      A.det.natAbs * (N.submatrix pivot id).det.natAbs := by
  have hm : (N * A).submatrix pivot id = N.submatrix pivot id * A := by
    simpa using (Matrix.submatrix_mul_equiv N A pivot (Equiv.refl _) id).symm
  rw [hm, Matrix.det_mul, Int.natAbs_mul, Nat.mul_comm]

theorem normalPullback : NormalPullback := by
  intro n r q P T hT
  obtain ⟨hB, _, hN, hW, hI, ⟨pivot, hp⟩, _⟩ := hT
  obtain ⟨A, hA⟩ := pulledNormal_factor T hN hW hI
  have hd := pulledNormal_factor_det_ne_zero T hB hI A hA
  refine ⟨A, A.det.natAbs, pivot, hA, rfl,
    Int.natAbs_pos.mpr hd, hp, ?_⟩
  rw [hA, minor_natAbs_factor, hp]

theorem pulled_minor_cross {n : ℕ} (T : TransitionInput n 3 2) (i j : Fin n) :
    (T.pulledNormal.submatrix ![i.castSucc, j.castSucc] id).det =
      dotProduct
        (crossProduct (fun k : Fin 3 => T.imageNormal k.castSucc 0)
          (fun k : Fin 3 => T.imageNormal k.castSucc 1))
        (crossProduct (T.old i) (T.old j)) := by
  rw [dotProduct_comm, cross_dot_cross]
  simp [Matrix.det_fin_two, Matrix.submatrix_apply, TransitionInput.pulledNormal,
    Matrix.mul_apply, oldBlock, dotProduct]

end Praxis.Algebra.Trans
