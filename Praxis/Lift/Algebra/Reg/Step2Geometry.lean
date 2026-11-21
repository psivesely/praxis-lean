import Praxis.Lift.Algebra.Reg.Step2
import Praxis.Algebra.Trans.Pullback
import Praxis.Algebra.Trim.Tensor
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Lift.Algebra.Reg.Pivot2
import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.DifferenceLattice.Definitions
import Praxis.Algebra.Prefix.Chain
import Praxis.Algebra.Prefix.Height
import Praxis.Algebra.Prefix.Mono
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.NumericTrim
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation

set_option linter.ambiguousOpen false

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

namespace Praxis.Lift

namespace Algebra.Reg.Step2.Geometry

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open scoped BigOperators Matrix

theorem integer_normal_iff {m : ℕ} (G : Fin m → ℕ) (E : Finset (Grid G))
    (z : Fin m → ℤ) :
    Algebra.Trans.rationalNormal E (fun x i => ((x i : ℕ) : ℚ))
      (fun i => (z i : ℚ)) ↔ z ∈ ordinaryNormals G E := by
  constructor
  · intro hz
    let f : (Fin m → ℤ) →ₗ[ℤ] ℤ := {
      toFun v := ∑ i, z i * v i
      map_add' := by intros; simp [mul_add, sum_add_distrib]
      map_smul' := by intros; simp [mul_sum, mul_left_comm] }
    have hker : Algebra.DifferenceLattice.differenceLattice 0 E ≤ f.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have hh := hz x hx y hy
      apply Int.cast_injective (α := ℚ)
      simpa [f, dotProduct, Pi.sub_apply, Algebra.DifferenceLattice.ival] using hh
    exact fun v hv => hker hv
  · intro hz x hx y hy
    have hd : Algebra.DifferenceLattice.ival 0 x - Algebra.DifferenceLattice.ival 0 y ∈
        Algebra.DifferenceLattice.differenceLattice 0 E :=
      Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    have hh := congrArg (Int.castRingHom ℚ) (hz _ hd)
    simpa [dotProduct, Pi.sub_apply, Algebra.DifferenceLattice.ival] using hh

theorem normal_rational_span {m d : ℕ} (G : Fin m → ℕ) (E : Finset (Grid G))
    (L : IntLat (Fin m) d) (hL : ordinaryNormals G E = L.carrier) :
    ∀ z, Algebra.Trans.rationalNormal E (fun x i => ((x i : ℕ) : ℚ)) z ↔
      ∃ a : Fin d → ℚ, z = (Algebra.Trans.ratMatrix L.matrix).mulVec a := by
  intro z
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors ℤ) z
    choose w hw using hb
    have hb0 : (b.val : ℚ) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.ne_zero b.property
    have hw' (i : Fin m) : (w i : ℚ) = (b.val : ℚ) * z i := by
      simpa only [Algebra.smul_def, Int.coe_castRingHom, algebraMap_int_eq] using hw i
    have hwn : w ∈ L.carrier := by
      rw [← hL]
      apply (integer_normal_iff G E w).mp
      intro x hx y hy
      have hh := hz x hx y hy
      change (∑ i, z i * (((x i : ℕ) : ℚ) - ((y i : ℕ) : ℚ))) = 0 at hh
      change (∑ i, (w i : ℚ) * (((x i : ℕ) : ℚ) - ((y i : ℕ) : ℚ))) = 0
      simp_rw [hw', mul_assoc]
      rw [← Finset.mul_sum, hh, mul_zero]
    let c := L.basis.repr ⟨w, hwn⟩
    have he : L.matrix.mulVec (fun j => c j) = w := by
      ext i
      exact Algebra.Lattice.basis_eval L.carrier L.basis ⟨w, hwn⟩ i
    refine ⟨fun j => (c j : ℚ) / (b.val : ℚ), ?_⟩
    ext i
    have hh : (∑ j, (L.matrix i j : ℚ) * (c j : ℚ)) = (w i : ℚ) := by
      exact_mod_cast congrFun he i
    change z i = ∑ j, (L.matrix i j : ℚ) * ((c j : ℚ) / (b.val : ℚ))
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, hh]
    apply (eq_div_iff hb0).mpr
    rw [hw']
    ring
  · rintro ⟨a, rfl⟩ x hx y hy
    have hcol (j : Fin d) :
        Algebra.Trans.rationalNormal E (fun x i => ((x i : ℕ) : ℚ))
          (fun i => (L.matrix i j : ℚ)) := by
      apply (integer_normal_iff G E _).mpr
      rw [hL]
      exact (L.basis j).property
    simp only [Matrix.mulVec, Algebra.Trans.ratMatrix, Matrix.map_apply,
      Int.coe_castRingHom, dotProduct, Pi.sub_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have hh := hcol j x hx y hy
    change (∑ i, (L.matrix i j : ℚ) *
      (((x i : ℕ) : ℚ) - ((y i : ℕ) : ℚ))) = 0 at hh
    have he : (∑ i, (L.matrix i j : ℚ) * a j *
        (((x i : ℕ) : ℚ) - ((y i : ℕ) : ℚ))) =
        a j * ∑ i, (L.matrix i j : ℚ) *
          (((x i : ℕ) : ℚ) - ((y i : ℕ) : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hh, mul_zero]

def extendMatrix {R : Type*} [Zero R] [One R] {m r : ℕ}
    (B : Matrix (Fin m) (Fin r) R) : Matrix (Fin (m+1)) (Fin (r+1)) R :=
  Fin.snoc (fun i => Fin.snoc (B i) 0) (Fin.snoc 0 1)

theorem extendMatrix_mul {R : Type*} [Semiring R] {m r q : ℕ}
    (B : Matrix (Fin m) (Fin r) R) (A : Matrix (Fin r) (Fin q) R) :
    extendMatrix B * extendMatrix A = extendMatrix (B * A) := by
  ext i j
  simp only [Matrix.mul_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [extendMatrix, Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem extendMatrix_one {R : Type*} [Semiring R] {r : ℕ} :
    extendMatrix (1 : Matrix (Fin r) (Fin r) R) = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [extendMatrix, Matrix.one_apply, eq_comm]

theorem extendMatrix_mulVec {R : Type*} [Semiring R] {m r : ℕ}
    (B : Matrix (Fin m) (Fin r) R) (x : Fin (r+1) → R) :
    (extendMatrix B).mulVec x =
      Fin.snoc (B.mulVec (fun j => x j.castSucc)) (x (Fin.last r)) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [extendMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem split_range_saturated {m r : ℕ} (B : Matrix (Fin m) (Fin r) ℤ)
    (D : Matrix (Fin r) (Fin m) ℤ) (hDB : D * B = 1) :
    Algebra.Lattice.IsSaturated B.mulVecLin.range := by
  intro a ha x hx
  obtain ⟨y, hy⟩ := hx
  change B.mulVec y = a • x at hy
  have hy' : y = a • D.mulVec x := by
    have hh := congrArg D.mulVec hy
    simpa only [Matrix.mulVec_mulVec, hDB, Matrix.one_mulVec, Matrix.mulVec_smul] using hh
  refine ⟨D.mulVec x, ?_⟩
  have hh : a • B.mulVec (D.mulVec x) = a • x := by
    rw [← Matrix.mulVec_smul, ← hy']
    exact hy
  ext i
  exact (mul_left_cancel₀ ha (congrFun hh i))

theorem extended_basis_split {m r : ℕ} (L : IntLat (Fin m) r) :
    ∃ D : Matrix (Fin (r+1)) (Fin (m+1)) ℤ,
      D * extendMatrix L.matrix = 1 := by
  obtain ⟨D, hD⟩ := Algebra.Trans.primitive_left_inverse L.matrix (Algebra.Prefix.primitive_rows L)
  exact ⟨extendMatrix D, by rw [extendMatrix_mul, hD, extendMatrix_one]⟩

theorem mem_extended_range {m r : ℕ} (L : IntLat (Fin m) r) (x : Fin (m+1) → ℤ) :
    x ∈ (extendMatrix L.matrix).mulVecLin.range ↔
      (fun i => x i.castSucc) ∈ L.carrier := by
  constructor
  · rintro ⟨a, ha⟩
    have hi : L.matrix.mulVec (fun j => a j.castSucc) = fun i => x i.castSucc := by
      ext i
      have hh := congrFun ha i.castSucc
      simpa only [Matrix.mulVecLin_apply, extendMatrix_mulVec, Fin.snoc_castSucc] using hh
    rw [← hi, ← Algebra.Prefix.basis_matrix_range L]
    exact ⟨_, rfl⟩
  · intro hx
    let a : Fin (r+1) → ℤ := Fin.snoc (L.basis.equivFun ⟨_, hx⟩) (x (Fin.last m))
    refine ⟨a, ?_⟩
    change (extendMatrix L.matrix).mulVec a = x
    rw [extendMatrix_mulVec]
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [a]
    · simp only [Fin.snoc_castSucc, a]
      simpa only [Fin.snoc_castSucc, Matrix.mulVec, dotProduct, IntLat.matrix] using
        Algebra.Lattice.basis_eval L.carrier L.basis ⟨_, hx⟩ i

theorem next_carrier_in_extended {n k : ℕ} (S : Algebra.Prefix.Definitions.PivotFirstStep 2 n k)
    (L3 : IntLat (Fin k) 3) (hcontain : S.old.primitive.carrier ≤ L3.carrier) :
    S.next.primitive.carrier ≤ (extendMatrix L3.matrix).mulVecLin.range := by
  obtain ⟨D, hD⟩ := extended_basis_split L3
  have hs := split_range_saturated (extendMatrix L3.matrix) D hD
  have hr : S.next.matrix.mulVecLin.range ≤ (extendMatrix L3.matrix).mulVecLin.range := by
    rintro _ ⟨a, rfl⟩
    apply (mem_extended_range L3 _).mpr
    apply hcontain
    rw [S.old.primitive_eq]
    apply Algebra.Lattice.le_saturation
    refine ⟨a, ?_⟩
    ext i
    have hi := congrFun (congrArg (fun B : Matrix (Fin k) (Fin 2) ℤ => B.mulVec a)
      (Algebra.Prefix.step_matrix_init S)) i
    exact hi.symm
  intro x hx
  rw [S.next.primitive_eq] at hx
  obtain ⟨a, ha, hax⟩ := hx
  exact hs a ha x (hr hax)

theorem basis_factor_of_split {m r d : ℕ} (B : Matrix (Fin m) (Fin r) ℤ)
    (D : Matrix (Fin r) (Fin m) ℤ) (hDB : D * B = 1)
    (N : IntLat (Fin m) d) (hN : N.carrier ≤ B.mulVecLin.range) :
    ∃ K : Matrix (Fin r) (Fin d) ℤ, N.matrix = B * K ∧ Algebra.Trans.PrimitiveMatrix K := by
  have hcol (j : Fin d) : B.mulVec ((D * N.matrix).col j) = N.matrix.col j := by
    obtain ⟨a, ha⟩ := hN (N.basis j).property
    change B.mulVec a = N.matrix.col j at ha
    have hd : (D * N.matrix).col j = a := by
      have hh := congrArg D.mulVec ha
      rw [Matrix.mulVec_mulVec, hDB, Matrix.one_mulVec] at hh
      ext i
      change (∑ l, D i l * N.matrix l j) = a i
      exact congrFun hh.symm i
    rw [hd]
    exact ha
  have hNK : N.matrix = B * (D * N.matrix) := by
    ext i j
    exact (congrFun (hcol j) i).symm
  refine ⟨D * N.matrix, hNK, ?_⟩
  obtain ⟨J, hJ⟩ := Algebra.Trans.primitive_left_inverse N.matrix (Algebra.Prefix.primitive_rows N)
  apply Algebra.VectorInverse.primitive_of_left_inverse (D * N.matrix) (J * B)
  rw [Matrix.mul_assoc, ← hNK, hJ]

theorem primitive_pivot_max {d n k : ℕ} (Q : Algebra.Prefix.Definitions.PivotFirstPrefix d n k) :
    (Q.primitive.matrix.submatrix
      (fun j : Fin d => (⟨j.val, lt_of_lt_of_le j.isLt Q.rank_le_prefix⟩ : Fin k))
      id).det.natAbs = Q.primitive.H := by
  let pivot : Fin d → Fin k := fun j => ⟨j.val, lt_of_lt_of_le j.isLt Q.rank_le_prefix⟩
  have hB : Q.matrix.mulVecLin.range ≤ Q.primitive.carrier := by
    rw [Q.primitive_eq]
    exact Algebra.Lattice.le_saturation _
  obtain ⟨A, hA⟩ := Algebra.Prefix.exists_basis_factor Q.primitive Q.matrix hB
  have hp : (Q.matrix.submatrix pivot id).det.natAbs = Q.original.H := Q.maximal_pivot
  rw [hA, Algebra.Prefix.minor_mul] at hp
  have hH : Q.primitive.H * A.det.natAbs = Q.original.H := by
    change height Q.primitive.matrix * A.det.natAbs = Q.original.H
    rw [← Algebra.Prefix.height_mul, ← hA]
    exact Algebra.Prefix.PivotFirstPrefix.matrix_height Q
  have ha : 0 < A.det.natAbs := by
    have hh := Q.pivot_nonzero
    nlinarith
  exact Nat.eq_of_mul_eq_mul_right ha (hp.trans hH.symm)

theorem pullbackQ_eq {m r q : ℕ} (T : Algebra.Trans.TransitionInput m r q)
    (u : Fin (r+1) → ℚ) :
    T.pullbackQ u = (Algebra.Trans.ratMatrix (extendMatrix T.old)).mulVec u := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [Algebra.Trans.TransitionInput.pullbackQ, Algebra.Trans.ratMatrix,
      extendMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem imageQ_eq {m r q : ℕ} (T : Algebra.Trans.TransitionInput m r q)
    (x : Grid T.grids) :
    T.imageQ x = (Algebra.Trans.ratMatrix (extendMatrix T.old)).transpose.mulVec (T.sourceQ x) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Algebra.Trans.TransitionInput.imageQ, Algebra.Trans.TransitionInput.sourceQ,
      Algebra.Trans.ratMatrix, extendMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc]

theorem image_normal_iff {m r q : ℕ} (T : Algebra.Trans.TransitionInput m r q)
    (u : Fin (r+1) → ℚ) :
    Algebra.Trans.rationalNormal T.event T.imageQ u ↔
      Algebra.Trans.rationalNormal T.event T.sourceQ (T.pullbackQ u) := by
  have he (x y : Grid T.grids) :
      dotProduct u (T.imageQ x - T.imageQ y) =
        dotProduct (T.pullbackQ u) (T.sourceQ x - T.sourceQ y) := by
    rw [imageQ_eq, imageQ_eq, ← Matrix.mulVec_sub, pullbackQ_eq,
      Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  constructor <;> intro h x hx y hy
  · rw [← he]; exact h x hx y hy
  · rw [he]; exact h x hx y hy

theorem pulled_eq_extended {m r q : ℕ} (T : Algebra.Trans.TransitionInput m r q) :
    T.pulledNormal = extendMatrix T.old * T.imageNormal := by
  ext i j
  simp only [Matrix.mul_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [Algebra.Trans.TransitionInput.pulledNormal, Algebra.Trans.oldBlock,
      extendMatrix, Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem pullbackQ_injective {m r q : ℕ} (T : Algebra.Trans.TransitionInput m r q)
    (hB : Algebra.Trans.PrimitiveMatrix T.old) : Function.Injective T.pullbackQ := by
  obtain ⟨D, hD⟩ := Algebra.Trans.primitive_left_inverse T.old hB
  have he : extendMatrix D * extendMatrix T.old = 1 := by
    rw [extendMatrix_mul, hD, extendMatrix_one]
  have hQ : Algebra.Trans.ratMatrix (extendMatrix D) *
      Algebra.Trans.ratMatrix (extendMatrix T.old) = 1 := by
    dsimp only [Algebra.Trans.ratMatrix]
    rw [← Matrix.map_mul, he]
    simp
  intro x y hxy
  have hh := congrArg (Algebra.Trans.ratMatrix (extendMatrix D)).mulVec hxy
  simpa only [pullbackQ_eq, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] using hh

theorem normal_premises {m r q : ℕ} (T : Algebra.Trans.TransitionInput m r q)
    (N : IntLat (Fin (m+1)) q) (hN : T.normal = N.matrix)
    (hfull : ordinaryNormals T.grids T.event = N.carrier)
    (hB : T.OldLattice)
    (hpull : T.pulledNormal = T.normal) :
    T.OrdinaryNormals ∧ T.WholeNormalPullback ∧
      (∀ u, Algebra.Trans.rationalNormal T.event T.imageQ u ↔
        ∃ a : Fin q → ℚ, u = (Algebra.Trans.ratMatrix T.imageNormal).mulVec a) := by
  have hspan : ∀ z, Algebra.Trans.rationalNormal T.event T.sourceQ z ↔
      ∃ a : Fin q → ℚ, z = (Algebra.Trans.ratMatrix T.normal).mulVec a := by
    intro z
    change Algebra.Trans.rationalNormal T.event (fun x i => ((x i : ℕ) : ℚ)) z ↔ _
    rw [hN]
    exact normal_rational_span T.grids T.event N hfull z
  have hcomm (a : Fin q → ℚ) : (Algebra.Trans.ratMatrix T.normal).mulVec a =
      T.pullbackQ ((Algebra.Trans.ratMatrix T.imageNormal).mulVec a) := by
    rw [← hpull]
    exact Algebra.Trans.pulledNormal_mulVec T a
  have hImage (u : Fin (r+1) → ℚ) :
      Algebra.Trans.rationalNormal T.event T.imageQ u ↔
        ∃ a : Fin q → ℚ, u = (Algebra.Trans.ratMatrix T.imageNormal).mulVec a := by
    constructor
    · intro hu
      obtain ⟨a, ha⟩ := (hspan (T.pullbackQ u)).mp ((image_normal_iff T u).mp hu)
      refine ⟨a, pullbackQ_injective T hB ?_⟩
      exact ha.trans (hcomm a)
    · rintro ⟨a, rfl⟩
      exact (image_normal_iff T _).mpr ((hspan _).mpr ⟨a, (hcomm a).symm⟩)
  refine ⟨⟨?_, hspan⟩, ?_, hImage⟩
  · rw [hN]
    exact Algebra.Prefix.primitive_rows N
  · intro z
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := (hspan z).mp hz
      exact ⟨_, (hImage _).mpr ⟨a, rfl⟩, ha.trans (hcomm a)⟩
    · rintro ⟨u, hu, rfl⟩
      exact (image_normal_iff T u).mp hu

theorem minor_two_columns {B : Matrix (Fin 3) (Fin 2) ℚ}
    (I : Fin 2 → Fin 3) (J : Fin 2 → Fin 2)
    (h : (B.submatrix I J).det ≠ 0) : (B.submatrix I id).det ≠ 0 := by
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, id_eq] at h ⊢
  generalize J 0 = a at h
  generalize J 1 = b at h
  fin_cases a <;> fin_cases b
  · simp at h
  · exact h
  · intro hz
    apply h
    change B (I 0) 1 * B (I 1) 0 - B (I 0) 0 * B (I 1) 1 = 0
    linear_combination -hz
  · simp at h

theorem image_old_pivot {m : ℕ} (T : Algebra.Trans.TransitionInput m 3 2)
    (hpull : T.pulledNormal = T.normal)
    (pivot : Fin 2 → Fin m)
    (hdet : (T.normal.submatrix (fun j => (pivot j).castSucc) id).det ≠ 0) :
    ∃ p : Fin 2 → Fin 3, ((Algebra.Trans.oldBlock T.imageNormal).submatrix p id).det ≠ 0 := by
  let A := T.old.submatrix pivot id
  let B := Algebra.Trans.oldBlock T.imageNormal
  have he : T.normal.submatrix (fun j => (pivot j).castSucc) id = A * B := by
    ext i j
    rw [← hpull]
    exact Algebra.Trans.pulledNormal_old_entry T (pivot i) j
  have heQ : (Algebra.Trans.ratMatrix A * Algebra.Trans.ratMatrix B).det ≠ 0 := by
    dsimp only [Algebra.Trans.ratMatrix]
    rw [← Matrix.map_mul, ← he]
    change ((Int.castRingHom ℚ).mapMatrix
      (T.normal.submatrix (fun j => (pivot j).castSucc) id)).det ≠ 0
    rw [← RingHom.map_det]
    change (((T.normal.submatrix (fun j => (pivot j).castSucc) id).det : ℤ) : ℚ) ≠ 0
    exact_mod_cast hdet
  have hrank : (Algebra.Trans.ratMatrix B).rank = 2 := by
    have h1 := Matrix.rank_of_det_ne_zero heQ
    have h2 := Matrix.rank_mul_le_right (Algebra.Trans.ratMatrix A) (Algebra.Trans.ratMatrix B)
    have h3 := Matrix.rank_le_width (Algebra.Trans.ratMatrix B)
    simp only [Fintype.card_fin] at h1
    omega
  have hm : ∃ (I : Fin 2 → Fin 3) (J : Fin 2 → Fin 2),
      ((Algebra.Trans.ratMatrix B).submatrix I J).det ≠ 0 := by
    have convertRank (r : ℕ) (hr : r = 2)
        (h : ∃ (I : Fin r → Fin 3) (J : Fin r → Fin 2),
          ((Algebra.Trans.ratMatrix B).submatrix I J).det ≠ 0) :
        ∃ (I : Fin 2 → Fin 3) (J : Fin 2 → Fin 2),
          ((Algebra.Trans.ratMatrix B).submatrix I J).det ≠ 0 := by
      subst r
      exact h
    exact convertRank _ hrank (Analysis.exists_rank_minor (Algebra.Trans.ratMatrix B))
  obtain ⟨I, J, hIJ⟩ := hm
  refine ⟨I, ?_⟩
  have hh := minor_two_columns I J hIJ
  intro hz
  apply hh
  have hmap : (Algebra.Trans.ratMatrix B).submatrix I id =
      (B.submatrix I id).map (Int.castRingHom ℚ) := rfl
  rw [hmap]
  change ((Int.castRingHom ℚ).mapMatrix (B.submatrix I id)).det = 0
  rw [← RingHom.map_det]
  rw [hz, map_zero]

theorem return_geometry_of_trim {n k : ℕ} (P : VITParameters)
    (S : Algebra.Prefix.Definitions.PivotFirstStep 2 n k) (L3 : IntLat (Fin k) 3)
    (E : Finset (Grid (S.next.grids S.grids)))
    (hcontain : S.old.primitive.carrier ≤ L3.carrier)
    (hretain : S.old.primitive.mZ (S.old.grids S.grids) - P.eps ≤
      L3.mZ (S.old.grids S.grids))
    (hnormals : ordinaryNormals (S.next.grids S.grids) E = S.next.primitive.carrier)
    (htrim : S.next.primitive.mZ (S.next.grids S.grids) - P.eps ≤
      density (S.next.grids S.grids) E)
    (hellipsoid : (returnInput S L3 0 E).TrimmedEvent P.toVITData)
    (hG : GridBudget P.toVITData (S.next.grids S.grids)) : ReturnGeometry P S := by
  obtain ⟨D, hD⟩ := extended_basis_split L3
  obtain ⟨K, hK, hprim⟩ := basis_factor_of_split (extendMatrix L3.matrix) D hD
    S.next.primitive (next_carrier_in_extended S L3 hcontain)
  let T := returnInput S L3 K E
  have hB : T.OldLattice := Algebra.Prefix.primitive_rows L3
  have hpull : T.pulledNormal = T.normal := by
    rw [pulled_eq_extended]
    exact hK.symm
  obtain ⟨hOrdinary, hWhole, hImage⟩ := normal_premises T S.next.primitive rfl
    hnormals hB hpull
  let pivot : Fin 2 → Fin k := fun j => ⟨j.val, lt_of_lt_of_le j.isLt S.old.rank_le_prefix⟩
  have hpiv : (T.normal.submatrix (fun j => (pivot j).castSucc) id).det.natAbs =
      S.next.primitive.H := primitive_pivot_max S.next
  have hdet : (T.normal.submatrix (fun j => (pivot j).castSucc) id).det ≠ 0 := by
    apply Int.natAbs_ne_zero.mp
    rw [hpiv]
    exact ne_of_gt (Algebra.Prefix.height_pos S.next.primitive)
  refine ⟨L3, K, E, hcontain, hretain, htrim, hB, ?_, hOrdinary, hWhole,
    ⟨hprim, hImage, image_old_pivot T hpull pivot hdet⟩, ⟨pivot, hpiv⟩,
    ⟨fun i => S.grids_pos (S.next.coord i), hG.2.1⟩⟩
  exact hellipsoid

theorem gridLaw_density {m : ℕ} (G : Fin m → ℕ) (hG : ∀ i, 0 < G i)
    (E : Finset (Grid G)) :
    (Analysis.gridLaw G hG).prob (E : Set (Grid G)) = density G E := by
  classical
  simp only [Analysis.FiniteLaw.prob, Analysis.gridLaw, Analysis.FiniteLaw.uniform,
    Finset.mem_coe, ← Finset.sum_filter]
  simp [density, div_eq_mul_inv]

def appendZero {R : Type*} [Zero R] {m r : ℕ}
    (B : Matrix (Fin m) (Fin r) R) : Matrix (Fin (m+1)) (Fin r) R := Fin.snoc B 0

theorem appendZero_independent {m r : ℕ} (L : IntLat (Fin m) r) :
    LinearIndependent ℤ (appendZero L.matrix).col := by
  let restrict : (Fin (m+1) → ℤ) →ₗ[ℤ] (Fin m → ℤ) :=
    LinearMap.pi (fun i => LinearMap.proj i.castSucc)
  apply LinearIndependent.of_comp restrict
  have he : restrict ∘ (appendZero L.matrix).col =
      fun j => (L.basis j : Fin m → ℤ) := by
    funext j i
    simp [restrict, appendZero, IntLat.matrix]
  rw [he]
  exact L.basis.linearIndependent.map' L.carrier.subtype (Submodule.ker_subtype _)

theorem exists_current_trim {n k : ℕ} (P : VITParameters)
    (S : Algebra.Prefix.Definitions.PivotFirstStep 2 n k) (L3 : IntLat (Fin k) 3)
    (hTrim : Algebra.Trim.TrimForIntLat)
    (hdomain : P.theta0 - 30 * P.eps ≤ S.next.primitive.mZ (S.next.grids S.grids)) :
    ∃ (t : Fin 2 → ℤ) (E : Finset (Grid (S.next.grids S.grids))),
      atom (S.next.grids S.grids) (imageZ (S.next.grids S.grids) S.next.primitive.matrix) t =
        S.next.primitive.mZ (S.next.grids S.grids) ∧
      E ⊆ ordinaryFibre (S.next.grids S.grids) S.next.primitive t ∧
      S.next.primitive.mZ (S.next.grids S.grids) - P.eps ≤ density (S.next.grids S.grids) E ∧
      (returnInput S L3 0 E).TrimmedEvent P.toVITData := by
  classical
  let G := S.next.grids S.grids
  have hpos : ∀ i, 0 < G i := fun i => S.grids_pos (S.next.coord i)
  obtain ⟨t, ht, _hne⟩ := Algebra.Reg.largest_fibre G S.next.primitive hpos

  obtain ⟨U, _hout, hU⟩ := hTrim P.R P.eps P.trim.2 (Fin (k+1)) 3 G hpos
    (appendZero L3.matrix) ⟨by decide, le_rfl⟩ (appendZero_independent L3)
  let E := (ordinaryFibre G S.next.primitive t).filter (fun x => x ∈ U.ellipsoid P.R)
  have hset : (ordinaryFibre G S.next.primitive t : Set (Grid G)) ∩ U.ellipsoid P.R =
      (E : Set (Grid G)) := by ext x; simp [E]
  have hretain : S.next.primitive.mZ G - P.eps ≤ density G E := by
    have hh := hU (ordinaryFibre G S.next.primitive t : Set (Grid G))
    rw [hset] at hh
    change (Analysis.gridLaw G U.grid_pos).prob _ - _ ≤
      (Analysis.gridLaw G U.grid_pos).prob _ at hh
    rw [gridLaw_density, gridLaw_density, Algebra.Reg.ordinaryFibre_density, ht] at hh
    exact hh
  refine ⟨t, E, ht, filter_subset _ _, hretain, ?_, ?_⟩
  · apply Algebra.Reg.nonempty_of_density_pos G E
    have hs := (Algebra.Reg.rank2_slack P hdomain).1
    linarith [P.eps_pos, Algebra.Reg.threshold_pos P]
  · intro x hx
    have he := (mem_filter.mp hx).2
    have hc : U.center = (returnInput S L3 0 E).center := by
      ext j
      rw [Analysis.GridImage.center]
      change (Analysis.gridLaw G U.grid_pos).mean _ j = _
      rw [Algebra.Trim.grid_mean]
      simp only [appendZero, Matrix.map_apply, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, Int.coe_castRingHom,
        Int.cast_zero, zero_mul, add_zero]
      change (∑ i : Fin k, (L3.matrix i j : ℝ) * (((G i.castSucc : ℝ) - 1) / 2)) =
        ∑ i : Fin k, (L3.matrix i j : ℝ) * ((G i.castSucc : ℝ) - 1) / 2
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hs : Analysis.gridCovariance G ((appendZero L3.matrix).map (Int.castRingHom ℝ)) =
        (returnInput S L3 0 E).sigma := by
      ext j l
      simp [Analysis.gridCovariance, appendZero, returnInput,
        Algebra.Trans.TransitionInput.sigma, Algebra.Trans.TransitionInput.oldGrids,
        Algebra.Trans.realMatrix, Fin.sum_univ_castSucc, G]
    have hi : Analysis.gridImage G ((appendZero L3.matrix).map (Int.castRingHom ℝ)) x =
        (fun j => (imageZ (returnInput S L3 0 E).oldGrids L3.matrix
          ((returnInput S L3 0 E).oldPoint x) j : ℝ)) := by
      ext j
      simp [Analysis.gridImage, appendZero, imageZ, returnInput,
        Algebra.Trans.TransitionInput.oldPoint, Fin.sum_univ_castSucc]
    change Analysis.mahalanobisSq _ U.center _ ≤ P.R^2 at he
    rw [hs, hc, hi] at he
    simpa only [returnInput] using he

structure CurrentEvent {m : ℕ} (P : VITParameters) (G : Fin m → ℕ)
    (L : IntLat (Fin m) 2) where
  target : Fin 2 → ℤ
  event : Finset (Grid G)
  maximal : atom G (imageZ G L.matrix) target = L.mZ G
  subset_fibre : event ⊆ ordinaryFibre G L target
  retained : L.mZ G - P.eps ≤ density G event

theorem exists_current_event {m : ℕ} (P : VITParameters) (G : Fin m → ℕ)
    (L : IntLat (Fin m) 2) (hpos : ∀ i, 0 < G i) : Nonempty (CurrentEvent P G L) := by
  obtain ⟨t, ht, _hne⟩ := Algebra.Reg.largest_fibre G L hpos
  refine ⟨⟨t, ordinaryFibre G L t, ht, le_rfl, ?_⟩⟩
  rw [Algebra.Reg.ordinaryFibre_density, ht]
  exact sub_le_self _ P.eps_pos.le

theorem exists_next_event {n k : ℕ} (P : VITParameters)
    (S : Algebra.Prefix.Definitions.PivotFirstStep 2 n k)
    (hOld : GridBudget P.toVITData (S.old.grids S.grids))
    (hNew : GridBudget P.toVITData (S.next.grids S.grids))
    (hdOld : P.theta0 - 30 * P.eps ≤ S.old.primitive.mZ (S.old.grids S.grids))
    (hdNew : P.theta0 - 30 * P.eps ≤ S.next.primitive.mZ (S.next.grids S.grids))
    (hTrim : Algebra.Trim.TrimForIntLat)
    (C : CurrentEvent P (S.old.grids S.grids) S.old.primitive) :
    ∃ N : CurrentEvent P (S.next.grids S.grids) S.next.primitive,
      ordinaryNormals (S.next.grids S.grids) N.event = S.next.primitive.carrier →
      ordinaryNormals (S.old.grids S.grids) C.event ≠ S.old.primitive.carrier →
      ReturnGeometry P S := by
  classical
  by_cases ho : ordinaryNormals (S.old.grids S.grids) C.event = S.old.primitive.carrier
  · obtain ⟨N⟩ := exists_current_event P _ S.next.primitive
      (fun i => S.grids_pos (S.next.coord i))
    exact ⟨N, fun _ hn => (hn ho).elim⟩
  · have hs := (Algebra.Reg.rank2_slack P hdOld).1
    have hr := C.retained
    have hheavy : P.toVITData.mu ≤ density (S.old.grids S.grids) C.event := by
      linarith [P.eps_pos]
    have hne := Algebra.Reg.nonempty_of_density_pos _ C.event
      ((Algebra.Reg.threshold_pos P).trans_le hheavy)
    have hdim : Module.finrank ℤ (ordinaryNormals (S.old.grids S.grids) C.event) = 3 := by
      exact (Algebra.Reg.rank2_normal_dichotomy P _ S.old.primitive C.target C.event hOld
        C.subset_fibre hheavy).resolve_left ho
    let L3 : IntLat (Fin k) 3 := {
      carrier := ordinaryNormals (S.old.grids S.grids) C.event
      basis := Module.finBasisOfFinrankEq ℤ _ hdim
      saturated := Algebra.VectorInverse.normalLattice_saturated _ }
    have hcontain : S.old.primitive.carrier ≤ L3.carrier :=
      Algebra.Reg.carrier_le_normals _ S.old.primitive C.target C.event C.subset_fibre
    obtain ⟨u, hu⟩ := Algebra.Reg.event_in_normal_fibre (S.old.grids S.grids) L3 C.event hne le_rfl
    have hretain : S.old.primitive.mZ (S.old.grids S.grids) - P.eps ≤
        L3.mZ (S.old.grids S.grids) :=
      C.retained.trans (Algebra.Reg.density_le_mass _ L3 u C.event hu)
    obtain ⟨t, E, ht, hE, hret, hEll⟩ := exists_current_trim P S L3 hTrim hdNew
    refine ⟨⟨t, E, ht, hE, hret⟩, ?_⟩
    intro hn _
    exact return_geometry_of_trim P S L3 E hcontain hretain hn hret hEll hNew

theorem exists_dependent_chain {n : ℕ} (A : Fin (n+1) → Type*)
    (R : (k : Fin n) → A k.castSucc → A k.succ → Prop)
    (h0 : Nonempty (A 0)) (hs : ∀ k a, ∃ b, R k a b) :
    ∃ f : (j : Fin (n+1)) → A j, ∀ k, R k (f k.castSucc) (f k.succ) := by
  classical
  let f : (j : Fin (n+1)) → A j :=
    Fin.induction (Classical.choice h0) (fun k a => (hs k a).choose)
  refine ⟨f, ?_⟩
  intro k
  change R k (f k.castSucc)
    ((Fin.induction (motive := A) (Classical.choice h0) (fun k a => (hs k a).choose)) k.succ)
  rw [Fin.induction_succ]
  exact (hs k (f k.castSucc)).choose_spec

theorem exists_presentation_events {n : ℕ} {L : IntLat (Fin n) 2}
    (R : Algebra.Reg.Pivot2.Presentation L) (P : VITParameters) (G : Fin n → ℕ)
    (hG : GridBudget P.toVITData G) (hpos : ∀ i, 0 < G i)
    (hm : P.theta0 - 30 * P.eps ≤ L.mZ G) (hTrim : Algebra.Trim.TrimForIntLat) :
    ∃ C : (j : Fin (n-2+1)) → CurrentEvent P (R.grids G j) (R.lattices j),
      ∀ j : Fin (n-2),
        ordinaryNormals (R.grids G j.succ) (C j.succ).event = (R.lattices j.succ).carrier →
        ordinaryNormals (R.grids G j.castSucc) (C j.castSucc).event ≠
          (R.lattices j.castSucc).carrier → ReturnGeometry P (R.step G hpos j) := by
  apply exists_dependent_chain
    (fun j => CurrentEvent P (R.grids G j) (R.lattices j))
    (fun j old new =>
      ordinaryNormals (R.grids G j.succ) new.event = (R.lattices j.succ).carrier →
      ordinaryNormals (R.grids G j.castSucc) old.event ≠ (R.lattices j.castSucc).carrier →
      ReturnGeometry P (R.step G hpos j))
  · exact exists_current_event P _ _
      (fun i => hpos ((R.prefixes 0).coord i))
  · intro j C
    exact exists_next_event P (R.step G hpos j)
      (R.budget P.toVITData G hG j.castSucc) (R.budget P.toVITData G hG j.succ)
      (Presentation.domain R P G hpos hm j.castSucc)
      (Presentation.domain R P G hpos hm j.succ) hTrim C

end Algebra.Reg.Step2.Geometry

end Praxis.Lift
