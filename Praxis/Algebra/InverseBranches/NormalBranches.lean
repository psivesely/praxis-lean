import Praxis.Algebra.InverseBranches.IntegerLift
import Praxis.Algebra.InverseBranches.AdditiveChain
import Praxis.Algebra.Conversion.ConversionStatement
import Mathlib.Analysis.Real.Sqrt
import Praxis.Algebra.DifferenceLattice.Definitions
import Mathlib.Algebra.Module.Projective
import Praxis.Algebra.DifferenceLattice.Saturation

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.VectorInverse

open Finset Module Praxis.Combinatorics Praxis.Combinatorics.UnequalChain Praxis.Algebra.Lattice Praxis.Algebra.DifferenceLattice

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primitive_of_left_inverse {d : ℕ} (B : Matrix ι (Fin d) ℤ)
    (C : Matrix (Fin d) ι ℤ) (hCB : C * B = 1) : PrimitiveRows B := by
  let H := AddSubgroup.closure (Set.range ((fun i => B i)))
  have hrow (i : ι) : (fun i => B i) i ∈ H := AddSubgroup.subset_closure ⟨i, rfl⟩
  have hb (j : Fin d) : Pi.single j 1 ∈ H := by
    have hs : ∑ i, C j i • (fun i => B i) i ∈ H := H.sum_mem fun i _ => H.zsmul_mem (hrow i) _
    convert hs using 1
    ext k
    have h := congrFun (congrFun hCB j) k
    simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, Finset.sum_apply,
      mul_comm, eq_comm] using h.symm
  apply top_le_iff.mp
  intro v _
  have hv : ∑ j, v j • (Pi.single j 1 : Fin d → ℤ) ∈ H :=
    H.sum_mem fun j _ => H.zsmul_mem (hb j) _
  convert hv using 1
  ext k
  simp [Pi.single_apply]

theorem primitive_of_saturated_basis {d : ℕ} (L : Submodule ℤ (ι → ℤ))
    (hsat : Algebra.Lattice.IsSaturated L) (b : Module.Basis (Fin d) ℤ L) :
    PrimitiveRows (fun i j => (b j : ι → ℤ) i) := by
  let : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ L) :=
    Module.IsTorsionFree.of_smul_eq_zero (by
      intro a x hx
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        obtain ⟨v, rfl⟩ := L.mkQ_surjective x
        apply (Submodule.Quotient.mk_eq_zero L).mpr
        apply hsat a ha v
        apply (Submodule.Quotient.mk_eq_zero L).mp
        change L.mkQ (a • v) = 0
        rw [map_smul]
        exact hx)
  let : Module.Free ℤ ((ι → ℤ) ⧸ L) := Module.free_iff_isTorsionFree.mpr inferInstance
  obtain ⟨s, hs⟩ := (Module.Projective.iff_split_of_projective L.mkQ L.mkQ_surjective).mp
    (inferInstance : Module.Projective ℤ ((ι → ℤ) ⧸ L))
  let f : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id - s.comp L.mkQ
  have hf (v : ι → ℤ) : f v ∈ L := by
    apply (Submodule.Quotient.mk_eq_zero L).mp
    change L.mkQ (f v) = 0
    dsimp [f]
    have he := LinearMap.congr_fun hs (L.mkQ v)
    exact sub_eq_zero.mpr he.symm
  let projection : (ι → ℤ) →ₗ[ℤ] L := f.codRestrict L hf
  have hp (v : L) : projection v = v := by
    apply Subtype.ext
    change v.val - s (L.mkQ v.val) = v.val
    have hv : L.mkQ v.val = 0 := (Submodule.Quotient.mk_eq_zero L).mpr v.property
    rw [hv, map_zero, sub_zero]
  let B : Matrix ι (Fin d) ℤ := fun i j => (b j : ι → ℤ) i
  let c : (ι → ℤ) →ₗ[ℤ] (Fin d → ℤ) := b.equivFun.toLinearMap.comp projection
  let C := LinearMap.toMatrix' c
  apply primitive_of_left_inverse B C
  have hcomp : c.comp B.mulVecLin = LinearMap.id := by
    apply LinearMap.ext
    intro v
    funext j
    have he : B.mulVecLin v = ((b.equivFun.symm v : L) : ι → ℤ) := by
      ext i
      change (B *ᵥ v) i = _
      simp [B, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply,
        Finset.sum_apply, mul_comm]
    change b.equivFun (projection (B.mulVecLin v)) j = v j
    rw [he, hp]
    exact congrFun (b.equivFun.apply_symm_apply v) j
  have hm := congrArg LinearMap.toMatrix' hcomp
  change LinearMap.toMatrix' (c.comp (Matrix.toLin' B)) = _ at hm
  simpa only [LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hm

def normalLattice (D : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℤ) where
  carrier := {w | ∀ d ∈ D, ∑ i, w i * d i = 0}
  zero_mem' := by intro d _; simp
  add_mem' := by
    intro w w' hw hw' d hd
    simp only [Pi.add_apply, add_mul, sum_add_distrib, hw d hd, hw' d hd, add_zero]
  smul_mem' := by
    intro a w hw d hd
    change (∑ i, (a * w i) * d i) = 0
    calc
      _ = a * ∑ i, w i * d i := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      _ = 0 := by rw [hw d hd, mul_zero]

theorem normalLattice_saturated (D : Submodule ℤ (ι → ℤ)) : IsSaturated (normalLattice D) := by
  intro a ha w hw d hd
  have h := hw d hd
  have he : (∑ i, (a * w i) * d i) = a * ∑ i, w i * d i := by
    rw [mul_sum]; apply sum_congr rfl; intro i _; ring
  change (∑ i, (a * w i) * d i) = 0 at h
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_left ha

noncomputable abbrev basisMatrix {d : ℕ} {L : Submodule ℤ (ι → ℤ)} (b : Basis (Fin d) ℤ L) :
    Matrix ι (Fin d) ℤ := fun i j => (b j : ι → ℤ) i

def largestMinor {d : ℕ} (B : Matrix ι (Fin d) ℤ) : ℕ :=
  univ.sup fun r : Fin d → ι => (B.submatrix r id).det.natAbs

theorem exists_maximal_basis_minor {d : ℕ} (L : Submodule ℤ (ι → ℤ))
    (hsat : IsSaturated L) (b : Basis (Fin d) ℤ L) :
    ∃ r : Fin d → ι, ((basisMatrix b).submatrix r id).det ≠ 0 ∧
      ∀ q : Fin d → ι, ((basisMatrix b).submatrix q id).det.natAbs ≤
        ((basisMatrix b).submatrix r id).det.natAbs := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨e, he⟩ := exists_prime_minor 2 L hsat b
  have he0 : ((basisMatrix b).submatrix e id).det ≠ 0 := by
    intro h
    have hm : (basisMatrix b).submatrix e id =
        (fun i j => (b j).val (e i) : Matrix (Fin d) (Fin d) ℤ) := by ext i j; rfl
    rw [hm] at h
    exact he (by rw [h, Int.cast_zero])
  have hn : (univ : Finset (Fin d → ι)).Nonempty := ⟨e, mem_univ _⟩
  obtain ⟨r, _, hmax⟩ := exists_max_image (univ : Finset (Fin d → ι))
    (fun q => ((basisMatrix b).submatrix q id).det.natAbs) hn
  refine ⟨r, ?_, fun q => hmax q (mem_univ _)⟩
  intro hzero
  have hh := hmax e (mem_univ _)
  rw [hzero, Int.natAbs_zero] at hh
  exact he0 (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hh))

theorem largestMinor_eq_pivot {d : ℕ} (B : Matrix ι (Fin d) ℤ) (r : Fin d → ι)
    (hmax : ∀ q : Fin d → ι, (B.submatrix q id).det.natAbs ≤ (B.submatrix r id).det.natAbs) :
    largestMinor B = (B.submatrix r id).det.natAbs := by
  apply le_antisymm
  · exact Finset.sup_le fun q _ => hmax q
  · exact Finset.le_sup (f := fun q : Fin d → ι => (B.submatrix q id).det.natAbs) (mem_univ r)

end Praxis.Algebra.VectorInverse
