import Praxis.Proofs.Classification.Quadratic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Praxis.Proofs.Classification.Annihilate

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {F : Type*} [Field F] {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

def familyLin {M : Type*} [AddCommGroup M] [Module F M] (u : J → M) : (J → F) →ₗ[F] M where
  toFun a := ∑ j, a j • u j
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, smul_smul, smul_eq_mul, Finset.smul_sum, RingHom.id_apply]

theorem familyLin_apply {M : Type*} [AddCommGroup M] [Module F M] (u : J → M) (a : J → F) :
    familyLin u a = ∑ j, a j • u j := rfl

theorem familyLin_range (h : J → Fin d → F) :
    LinearMap.range (familyLin h) = Submodule.span F (Set.range h) := by
  classical
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    simp [familyLin]

theorem matrix_family_mulVec (M : J → Matrix (Fin d) (Fin d) F) (a : J → F) (v : Fin d → F) :
    (familyLin M a).mulVec v = familyLin (fun j => (M j).mulVec v) a := by
  change ((Matrix.mulVecBilin F F) (∑ j, a j • M j)) v = _
  rw [map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, familyLin_apply]
  rfl

theorem compatible_relation (h : J → Fin d → F)
    (M : J → Matrix (Fin d) (Fin d) F)
    (hspan : Submodule.span F (Set.range h) = ⊤)
    (hcompat : ∀ r s, (M r).mulVec (h s) = (M s).mulVec (h r))
    (a : J → F) (ha : familyLin h a = 0) : familyLin M a = 0 := by
  have hk : Submodule.span F (Set.range h) ≤ LinearMap.ker (familyLin M a).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change (familyLin M a).mulVec (h s) = 0
    rw [matrix_family_mulVec]
    simp_rw [hcompat]
    change (∑ j, a j • (M s).mulVecLin (h j)) = 0
    simp_rw [← map_smul]
    rw [← map_sum]
    change (M s).mulVecLin (familyLin h a) = 0
    rw [ha, map_zero]
  rw [hspan] at hk
  ext i j
  have hv : (familyLin M a).mulVec (Pi.single j 1) = 0 := hk Submodule.mem_top
  have hi := congrFun hv i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply, Matrix.zero_apply] using hi

theorem compatible_slice_map (h : J → Fin d → F)
    (M : J → Matrix (Fin d) (Fin d) F)
    (hspan : Submodule.span F (Set.range h) = ⊤)
    (hcompat : ∀ r s, (M r).mulVec (h s) = (M s).mulVec (h r)) :
    ∃ C : (Fin d → F) →ₗ[F] Matrix (Fin d) (Fin d) F, ∀ j, C (h j) = M j := by
  classical
  have hsur : LinearMap.range (familyLin h) = ⊤ := (familyLin_range h).trans hspan
  obtain ⟨T, hT⟩ := (familyLin h).exists_rightInverse_of_surjective hsur
  refine ⟨familyLin M ∘ₗ T, fun j => ?_⟩
  have hker : familyLin h (T (h j) - Pi.single j 1) = 0 := by
    rw [map_sub]
    have ht := LinearMap.congr_fun hT (h j)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ht
    rw [ht]
    simp [familyLin]
  have hm := compatible_relation h M hspan hcompat _ hker
  rw [map_sub] at hm
  simpa [LinearMap.comp_apply, familyLin, sub_eq_zero] using hm

abbrev Tri (F : Type*) [Field F] (d : ℕ) :=
  (Fin d → F) →ₗ[F] (Fin d → F) →ₗ[F] (Fin d → F) →ₗ[F] F

def SymTri (Ξ : Tri F d) : Prop :=
  (∀ h u w, Ξ h u w = Ξ w u h) ∧ (∀ h u w, Ξ h u w = Ξ h w u)

def slice (Ξ : Tri F d) (h : Fin d → F) : Matrix (Fin d) (Fin d) F :=
  LinearMap.toMatrix₂' F (Ξ h)

def cubicOfSlices (C : (Fin d → F) →ₗ[F] Matrix (Fin d) (Fin d) F) : Tri F d :=
  (Matrix.toLinearMap₂' F).toLinearMap ∘ₗ C

@[simp] theorem slice_cubicOfSlices
    (C : (Fin d → F) →ₗ[F] Matrix (Fin d) (Fin d) F) (h : Fin d → F) :
    slice (cubicOfSlices C) h = C h := by
  exact (LinearMap.toMatrix₂' F).apply_symm_apply (C h)

theorem cubicOfSlices_apply
    (C : (Fin d → F) →ₗ[F] Matrix (Fin d) (Fin d) F) (h u w : Fin d → F) :
    cubicOfSlices C h u w = dotProduct u ((C h).mulVec w) :=
  Matrix.toLinearMap₂'_apply' _ _ _

theorem tri_slice_eval (Ξ : Tri F d) (h u w : Fin d → F) :
    Ξ h u w = rowForm u (slice Ξ h) w := by
  have heq : Matrix.toLinearMap₂' F (slice Ξ h) = Ξ h :=
    (LinearMap.toMatrix₂' F).symm_apply_apply (Ξ h)
  have heval := congrArg (fun f : (Fin d → F) →ₗ[F] (Fin d → F) →ₗ[F] F => f u w) heq
  rw [Matrix.toLinearMap₂'_apply', ← rowForm_apply] at heval
  exact heval.symm

theorem tri_vanish_on_span (Ξ : Tri F d) (h : J → Fin d → F)
    (hspan : Submodule.span F (Set.range h) = ⊤) (u w : Fin d → F)
    (hz : ∀ j, Ξ (h j) u w = 0) : ∀ x, Ξ x u w = 0 := by
  let f : (Fin d → F) →ₗ[F] F :=
    { toFun := fun x => Ξ x u w
      map_add' x y := by simp only [map_add, LinearMap.add_apply]
      map_smul' r x := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hk : Submodule.span F (Set.range h) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hz j
  rw [hspan] at hk
  exact fun x => hk Submodule.mem_top

theorem tri_ext {Ξ Ψ : Tri F d}
    (h : ∀ i j k : Fin d, Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) =
      Ψ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)) : Ξ = Ψ := by
  apply (Pi.basisFun F (Fin d)).ext
  intro i
  apply (Pi.basisFun F (Fin d)).ext
  intro j
  apply (Pi.basisFun F (Fin d)).ext
  intro k
  simpa only [Pi.basisFun_apply] using h i j k

def cube (ξ : Fin d → F) : Tri F d :=
  cubicOfSlices (((dotProductBilin F F) ξ).smulRight (Matrix.vecMulVec ξ ξ))

theorem slice_cube (ξ h : Fin d → F) :
    slice (cube ξ) h = dotProduct h ξ • Matrix.vecMulVec ξ ξ := by
  rw [cube, slice_cubicOfSlices, LinearMap.smulRight_apply, dotProductBilin_apply_apply]
  rw [dotProduct_comm]

theorem cube_apply (ξ h u w : Fin d → F) :
    cube ξ h u w = dotProduct h ξ * dotProduct u ξ * dotProduct w ξ := by
  rw [cube, cubicOfSlices_apply, LinearMap.smulRight_apply, dotProductBilin_apply_apply]
  rw [← rowForm_apply]
  rw [← bilinEval_apply, map_smul, bilinEval_outer, smul_eq_mul]
  rw [dotProduct_comm ξ h]
  ring

theorem compatible_cubic (h : J → Fin d → F)
    (M : J → Matrix (Fin d) (Fin d) F)
    (hspan : Submodule.span F (Set.range h) = ⊤)
    (hsym : ∀ j, (M j).IsSymm)
    (hcompat : ∀ r s, (M r).mulVec (h s) = (M s).mulVec (h r)) :
    ∃ Ξ : Tri F d, SymTri Ξ ∧ ∀ j, slice Ξ (h j) = M j := by
  obtain ⟨C, hC⟩ := compatible_slice_map h M hspan hcompat
  let B : (Fin d → F) →ₗ[F] (Fin d → F) →ₗ[F] (Fin d → F) :=
    (Matrix.mulVecBilin F F) ∘ₗ C
  have hB : B = B.flip := by
    apply LinearMap.ext_on_range hspan
    intro r
    apply LinearMap.ext_on_range hspan
    intro s
    change (C (h r)).mulVec (h s) = (C (h s)).mulVec (h r)
    rw [hC, hC]
    exact hcompat r s
  have hsymC : ∀ x, (C x).IsSymm := by
    have heq : (Matrix.transposeLinearEquiv (Fin d) (Fin d) F F).toLinearMap ∘ₗ C = C := by
      apply LinearMap.ext_on_range hspan
      intro j
      simp only [LinearMap.comp_apply, hC]
      exact (hsym j).eq
    intro x
    exact LinearMap.congr_fun heq x
  refine ⟨cubicOfSlices C, ⟨?_, ?_⟩, ?_⟩
  · intro x u w
    rw [cubicOfSlices_apply, cubicOfSlices_apply]
    have hb := LinearMap.congr_fun (LinearMap.congr_fun hB x) w
    change (C x).mulVec w = (C w).mulVec x at hb
    rw [hb]
  · intro x u w
    rw [cubicOfSlices_apply, cubicOfSlices_apply]
    rw [← Matrix.dotProduct_transpose_mulVec, (hsymC x).eq]
  · intro j
    rw [slice_cubicOfSlices, hC]

end

end

end Praxis.Proofs.Classification
