import Praxis.Algebra.DifferenceLattice.Saturation
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

set_option linter.style.haveILetI false

set_option linter.unusedSectionVars false

noncomputable section

open Finset Module Matrix

open scoped BigOperators

namespace Praxis.Analysis

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def columnLattice (D : Matrix ι κ ℤ) : Submodule ℤ (ι → ℤ) :=
  Submodule.span ℤ (Set.range D.col)

def saturation (L : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℤ) :=
  Algebra.Lattice.saturation L

def rationalRank (D : Matrix ι κ ℤ) : ℕ := (D.map (Int.castRingHom ℚ)).rank

def ratVec : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun x i := (x i : ℚ)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

lemma ratVec_injective : Function.Injective (ratVec : (ι → ℤ) →ₗ[ℤ] (ι → ℚ)) := by
  intro x y h
  ext i
  have hi : (x i : ℚ) = (y i : ℚ) := congrFun h i
  exact_mod_cast hi

theorem rationalRank_eq_finrank (D : Matrix ι κ ℤ) :
    rationalRank D = Module.finrank ℤ (columnLattice D) := by
  letI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  let Q := D.map (Int.castRingHom ℚ)
  letI : Module.Finite ℤ (Submodule.span ℤ (Set.range Q.col)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range Q.col)
  have hm : (columnLattice D).map ratVec =
      Submodule.span ℤ (Set.range Q.col) := by
    rw [columnLattice, Submodule.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    rfl
  change Q.rank = _
  rw [Matrix.rank_eq_finrank_span_cols,
    Submodule.finrank_span_eq_finrank_span ℤ ℚ, ← hm]
  exact (Submodule.equivMapOfInjective ratVec ratVec_injective (columnLattice D)).finrank_eq.symm

theorem exists_rank_minor {K : Type*} [Field K] (A : Matrix ι κ K) :
    ∃ (I : Fin A.rank → ι) (J : Fin A.rank → κ), (A.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨s, -, -, hs, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K A.col) (Set.empty_subset (Set.univ : Set κ))
  have hsp : Submodule.span K (Set.range (fun j : s => A.col j)) =
      Submodule.span K (Set.range A.col) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact Submodule.subset_span ⟨j,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      simpa only [Set.image_eq_range] using hs ⟨j,Set.mem_univ j,rfl⟩
  have hc : Fintype.card s = A.rank := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols]
  let e : Fin A.rank ≃ s := Fintype.equivOfCardEq (by simpa using hc.symm)
  let J : Fin A.rank → κ := fun j => e j
  let B : Matrix ι (Fin A.rank) K := A.submatrix id J
  have hb : LinearIndependent K B.col := hli.comp e e.injective
  have hr : B.transpose.rank = A.rank := by
    simpa using hb.rank_matrix
  obtain ⟨t, -, -, ht, hti⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K B.row) (Set.empty_subset (Set.univ : Set ι))
  have htp : Submodule.span K (Set.range (fun i : t => B.row i)) =
      Submodule.span K (Set.range B.row) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨i,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      simpa only [Set.image_eq_range] using ht ⟨i,Set.mem_univ i,rfl⟩
  have htc : Fintype.card t = A.rank := by
    rw [← finrank_span_eq_card hti, htp, ← Matrix.rank_eq_finrank_span_row,
      ← Matrix.rank_transpose, hr]
  let f : Fin A.rank ≃ t := Fintype.equivOfCardEq (by simpa using htc.symm)
  let I : Fin A.rank → ι := fun i => f i
  refine ⟨I,J,?_⟩
  have hi : LinearIndependent K (A.submatrix I J).row := hti.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hi)).ne_zero

def KillsColumns (p : ℕ) (z : ι → ZMod p) (D : Matrix ι κ ℤ) : Prop :=
  ∀ j, ∑ i, z i * (D i j : ZMod p) = 0

def KillsSubmodule (p : ℕ) (z : ι → ZMod p) (L : Submodule ℤ (ι → ℤ)) : Prop :=
  ∀ x ∈ L, ∑ i, z i * (x i : ZMod p) = 0

theorem kills_saturation_of_small_minors {p e : ℕ} [Fact p.Prime]
    (D : Matrix ι κ ℤ) (z : ι → ZMod p)
    (hrank : rationalRank D = e) (hkill : KillsColumns p z D)
    (hsmall : ∀ (I : Fin e → ι) (J : Fin e → κ),
      |(D.submatrix I J).det| < (p : ℤ)) :
    KillsSubmodule p z (saturation (columnLattice D)) := by
  classical
  subst e
  let E := saturation (columnLattice D)
  obtain ⟨k,b⟩ := E.basisOfPid (Pi.basisFun ℤ ι)
  have hb : Module.finrank ℤ E = k := by simpa using finrank_eq_card_basis b
  have hE : Module.finrank ℤ E = rationalRank D := by
    exact (Algebra.Lattice.finrank_saturation (columnLattice D)).trans
      (rationalRank_eq_finrank D).symm
  have hk : k = rationalRank D := hb.symm.trans hE
  let b : Basis (Fin (rationalRank D)) ℤ E := b.reindex (finCongr hk)
  let Q := D.map (Int.castRingHom ℚ)
  obtain ⟨I,J,hdetQ⟩ := exists_rank_minor Q
  let M := D.submatrix I J
  have hdet : M.det ≠ 0 := by
    intro hz
    apply hdetQ
    have h := (Int.castRingHom ℚ).map_det M
    change (M.det : ℚ) = (Q.submatrix I J).det at h
    rw [hz, Int.cast_zero] at h
    exact h.symm
  have hmod : (M.det : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : (p : ℤ) ∣ M.det := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hlt : M.det.natAbs < (p : ℤ).natAbs := by
      rw [← Nat.cast_lt (α:=ℤ), Int.natCast_natAbs, Int.natCast_natAbs]
      simpa [M] using hsmall I J
    exact hdet (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hlt)
  have hmem (j : κ) : D.col j ∈ E :=
    Algebra.Lattice.le_saturation (columnLattice D) (Submodule.subset_span ⟨j,rfl⟩)
  let C : Matrix (Fin (rationalRank D)) κ ℤ :=
    fun j l => b.equivFun ⟨D.col l, hmem l⟩ j
  let B : Matrix ι (Fin (rationalRank D)) ℤ := fun i j => (b j).val i
  have hDC (i : ι) (j : κ) : ∑ l, B i l * C l j = D i j :=
    Algebra.Lattice.basis_eval E b ⟨D.col j,hmem j⟩ i
  have hfactor : M = B.submatrix I id * C.submatrix id J := by
    ext i j
    exact (hDC (I i) (J j)).symm
  have hCmod : ((C.submatrix id J).det : ZMod p) ≠ 0 := by
    intro hz
    apply hmod
    rw [hfactor, Matrix.det_mul, Int.cast_mul, hz, mul_zero]
  let Cₚ := (C.submatrix id J).map (Int.castRingHom (ZMod p))
  have hCdet : Cₚ.det ≠ 0 := by
    have h := (Int.castRingHom (ZMod p)).map_det (C.submatrix id J)
    exact fun hz => hCmod (h.trans hz)
  let α : Fin (rationalRank D) → ZMod p := fun j => ∑ i, z i * ((b j).val i : ZMod p)
  have hrel : α ᵥ* Cₚ = 0 := by
    funext j
    change ∑ l, (∑ i, z i * ((b l).val i : ZMod p)) * (C l (J j) : ZMod p) = 0
    calc
      _ = ∑ i, z i * ((∑ l, B i l * C l (J j) : ℤ) : ZMod p) := by
        simp only [Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro l _
        dsimp [B]
        ring
      _ = 0 := by simp only [hDC]; exact hkill (J j)
  have hα : α = 0 := by
    apply (Matrix.vecMul_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hCdet)))
    simpa using hrel
  intro x hx
  have hexp (i : ι) : ∑ j, B i j * b.equivFun ⟨x,hx⟩ j = x i :=
    Algebra.Lattice.basis_eval E b ⟨x,hx⟩ i
  calc
    _ = ∑ j, (∑ i, z i * ((b j).val i : ZMod p)) *
        (b.equivFun ⟨x,hx⟩ j : ZMod p) := by
      conv_lhs => arg 2; ext i; rw [← hexp i]
      simp only [Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      dsimp [B]
      ring
    _ = 0 := by
      change ∑ j, α j * (b.equivFun ⟨x,hx⟩ j : ZMod p) = 0
      rw [hα]
      simp

end Praxis.Analysis
