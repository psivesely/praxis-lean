import Praxis.Proofs.Classification.Cubic

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {F : Type*} [Field F] {d : ℕ}

def elementaryTri (i j k : Fin d) : Tri F d :=
  (LinearMap.proj i).smulRight ((LinearMap.proj j).smulRight (LinearMap.proj k))

theorem elementaryTri_apply (i j k : Fin d) (h u w : Fin d → F) :
    elementaryTri i j k h u w = h i * u j * w k := by
  simp only [elementaryTri, LinearMap.smulRight_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, mul_assoc]

def triOfCoeff (t : Fin d → Fin d → Fin d → F) : Tri F d :=
  ∑ i, ∑ j, ∑ k, t i j k • elementaryTri i j k

theorem triOfCoeff_single (t : Fin d → Fin d → Fin d → F) (i j k : Fin d) :
    triOfCoeff t (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) = t i j k := by
  classical
  simp [triOfCoeff, LinearMap.sum_apply, LinearMap.smul_apply, elementaryTri_apply,
    Pi.single_apply, smul_eq_mul]

theorem tri_rebuild (Ξ : Tri F d) :
    triOfCoeff (fun i j k => Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)) = Ξ := by
  apply tri_ext
  intro i j k
  exact triOfCoeff_single _ i j k

theorem tri_eval (Ξ : Tri F d) (h u w : Fin d → F) :
    Ξ h u w = ∑ i, ∑ j, ∑ k,
      Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) * h i * u j * w k := by
  have heq := tri_rebuild Ξ
  conv_lhs => rw [← heq]
  simp only [triOfCoeff, LinearMap.sum_apply, LinearMap.smul_apply, elementaryTri_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

def mapTri (φ : F →+* F) (Ξ : Tri F d) : Tri F d :=
  triOfCoeff (fun i j k => φ (Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)))

theorem mapTri_single (φ : F →+* F) (Ξ : Tri F d) (i j k : Fin d) :
    mapTri φ Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) =
      φ (Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)) :=
  triOfCoeff_single _ i j k

theorem mapTri_apply (φ : F →+* F) (Ξ : Tri F d) (h u w : Fin d → F) :
    mapTri φ Ξ (fun i => φ (h i)) (fun i => φ (u i)) (fun i => φ (w i)) = φ (Ξ h u w) := by
  rw [tri_eval, tri_eval Ξ h u w]
  simp only [mapTri_single, map_sum, map_mul]

theorem slice_apply (Ξ : Tri F d) (h : Fin d → F) (i j : Fin d) :
    slice Ξ h i j = Ξ h (Pi.single i 1) (Pi.single j 1) := rfl

theorem map_single (φ : F →+* F) (i : Fin d) :
    (fun j => φ ((Pi.single i 1 : Fin d → F) j)) = Pi.single i 1 := by
  classical
  funext j
  by_cases hij : i = j <;> simp [Pi.single_apply, hij, Ne.symm]

theorem slice_mapTri (φ : F →+* F) (Ξ : Tri F d) (h : Fin d → F) :
    slice (mapTri φ Ξ) (fun i => φ (h i)) = (slice Ξ h).map φ := by
  ext i j
  rw [Matrix.map_apply, slice_apply, slice_apply]
  have h' := mapTri_apply φ Ξ h (Pi.single i 1) (Pi.single j 1)
  simpa only [map_single] using h'

theorem mapTri_sum {A : Type*} (φ : F →+* F) (s : Finset A) (Ξ : A → Tri F d) :
    mapTri φ (∑ a ∈ s, Ξ a) = ∑ a ∈ s, mapTri φ (Ξ a) := by
  apply tri_ext
  intro i j k
  simp only [mapTri_single, LinearMap.sum_apply, map_sum]

theorem mapTri_smul (φ : F →+* F) (r : F) (Ξ : Tri F d) :
    mapTri φ (r • Ξ) = φ r • mapTri φ Ξ := by
  apply tri_ext
  intro i j k
  simp only [mapTri_single, LinearMap.smul_apply, smul_eq_mul, map_mul]

theorem slice_sum {A : Type*} (s : Finset A) (Ξ : A → Tri F d) (h : Fin d → F) :
    slice (∑ a ∈ s, Ξ a) h = ∑ a ∈ s, slice (Ξ a) h := by
  ext i j
  simp only [slice_apply, Matrix.sum_apply, LinearMap.sum_apply]

theorem slice_smul (r : F) (Ξ : Tri F d) (h : Fin d → F) :
    slice (r • Ξ) h = r • slice Ξ h := by
  ext i j
  simp only [slice_apply, Matrix.smul_apply, LinearMap.smul_apply]

theorem slice_zero (h : Fin d → F) : slice (0 : Tri F d) h = 0 := by
  ext i j
  simp only [slice_apply, LinearMap.zero_apply, Matrix.zero_apply]

end

end

end Praxis.Proofs.Classification
