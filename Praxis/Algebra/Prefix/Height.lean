import Praxis.Algebra.Prefix.Definitions
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Ring.Finset
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

namespace Praxis.Algebra.Prefix

open Finset Module

open Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Prefix.Definitions

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem saturated_minor_gcd (L : IntLat ι d) :
    univ.gcd (fun r : Fin d → ι => (L.matrix.submatrix r id).det.natAbs) = 1 := by
  classical
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hdiv
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := Algebra.Lattice.exists_prime_minor p L.carrier L.saturated L.basis
  have hd : p ∣ (L.matrix.submatrix r id).det.natAbs :=
    hdiv.trans (Finset.gcd_dvd (mem_univ (r : Fin d → ι)))
  apply hr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  change (p : ℤ) ∣ (L.matrix.submatrix r id).det
  exact Int.natCast_dvd.mpr hd

omit [Fintype ι] [DecidableEq ι] in

theorem minor_mul (B : Matrix ι (Fin d) ℤ)
    (A : Matrix (Fin d) (Fin d) ℤ) (r : Fin d → ι) :
    ((B * A).submatrix r id).det.natAbs =
      (B.submatrix r id).det.natAbs * A.det.natAbs := by
  rw [Matrix.submatrix_mul B A r id id Function.bijective_id,
    Matrix.submatrix_id_id, Matrix.det_mul, Int.natAbs_mul]

omit [DecidableEq ι] in

theorem height_mul (B : Matrix ι (Fin d) ℤ)
    (A : Matrix (Fin d) (Fin d) ℤ) :
    height (B * A) = height B * A.det.natAbs := by
  unfold height Algebra.VectorInverse.largestMinor
  simp_rw [minor_mul]
  exact (Finset.sup_mul₀ _ _ _).symm

theorem exists_basis_factor (L : IntLat ι d) (B : Matrix ι (Fin d) ℤ)
    (hB : B.mulVecLin.range ≤ L.carrier) :
    ∃ A : Matrix (Fin d) (Fin d) ℤ, B = L.matrix * A := by
  classical
  have hcol (j : Fin d) : (fun i => B i j) ∈ L.carrier := by
    apply hB
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  let col (j : Fin d) : L.carrier := ⟨fun i => B i j, hcol j⟩
  let A : Matrix (Fin d) (Fin d) ℤ := fun a j => L.basis.equivFun (col j) a
  refine ⟨A, ?_⟩
  ext i j
  exact (Algebra.Lattice.basis_eval L.carrier L.basis (col j) i).symm

theorem gcd_of_basis_factor (L : IntLat ι d)
    (A : Matrix (Fin d) (Fin d) ℤ) :
    univ.gcd (fun r : Fin d → ι =>
      ((L.matrix * A).submatrix r id).det.natAbs) = A.det.natAbs := by
  simp_rw [minor_mul]
  rw [Finset.gcd_mul_right, saturated_minor_gcd]
  simp

namespace PivotFirstPrefix

variable {n k : ℕ}

theorem matrix_height (P : Definitions.PivotFirstPrefix d n k) :
    height P.matrix = P.originalHeight := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro r hr
    change (P.original.matrix.submatrix (P.coord ∘ r) id).det.natAbs ≤
      Algebra.VectorInverse.largestMinor P.original.matrix
    exact Finset.le_sup (f := fun q : Fin d → Fin n =>
      (P.original.matrix.submatrix q id).det.natAbs) (mem_univ _)
  · let pivot : Fin d → Fin k := fun a =>
      ⟨a.val, lt_of_lt_of_le a.isLt P.rank_le_prefix⟩
    have hmax : (P.matrix.submatrix pivot id).det.natAbs = P.originalHeight :=
      P.maximal_pivot
    rw [← hmax]
    exact Finset.le_sup (f := fun r : Fin d → Fin k =>
      (P.matrix.submatrix r id).det.natAbs) (mem_univ pivot)

end PivotFirstPrefix

theorem prefix_height {n k : ℕ} (P : Definitions.PivotFirstPrefix d n k) :
    PrefixHeight P := by
  classical
  have hB : P.matrix.mulVecLin.range ≤ P.primitive.carrier := by
    rw [P.primitive_eq]
    exact Algebra.Lattice.le_saturation _
  obtain ⟨A, hA⟩ := exists_basis_factor P.primitive P.matrix hB
  have hdiv : P.divisor = A.det.natAbs := by
    unfold Definitions.PivotFirstPrefix.divisor
    rw [hA]
    exact gcd_of_basis_factor P.primitive A
  change P.divisor * height P.primitive.matrix = P.originalHeight
  rw [hdiv, mul_comm, ← height_mul, ← hA]
  exact PivotFirstPrefix.matrix_height P

end Praxis.Algebra.Prefix
