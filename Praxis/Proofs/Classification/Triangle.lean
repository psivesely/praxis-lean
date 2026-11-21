import Praxis.Proofs.Classification.Tensor
import Praxis.Proofs.Classification.Cubic

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {F : Type*} [Field F]

theorem standard_zero2 (Ξ : Tri F 2) (hsym : SymTri Ξ)
    (hb : ∀ h (j : Fin 2), Ξ h (Pi.single j 1) (Pi.single j 1) = 0) : Ξ = 0 := by
  let T : Fin 2 → Fin 2 → Fin 2 → F := fun i j k => Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)
  have hs (i j k : Fin 2) : T i j k = T k j i := hsym.1 _ _ _
  have ht (i j k : Fin 2) : T i j k = T i k j := hsym.2 _ _ _
  have h000 : T 0 0 0 = 0 := hb _ 0
  have h100 : T 1 0 0 = 0 := hb _ 0
  have h001 : T 0 0 1 = 0 := (hs 0 0 1).trans h100
  have h010 : T 0 1 0 = 0 := (ht 0 1 0).trans h001
  have h011 : T 0 1 1 = 0 := hb _ 1
  have h110 : T 1 1 0 = 0 := (hs 1 1 0).trans h011
  have h101 : T 1 0 1 = 0 := (ht 1 0 1).trans h110
  have h111 : T 1 1 1 = 0 := hb _ 1
  apply tri_ext
  intro i j k
  simp only [LinearMap.zero_apply]
  change T i j k = 0
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact h000 | exact h001 | exact h010 | exact h011 | exact h100 | exact h101 | exact h110 | exact h111

theorem standard_zero_small {d : ℕ} (hd : d ≤ 2) (Ξ : Tri F d) (hsym : SymTri Ξ)
    (hb : ∀ h (j : Fin d), Ξ h (Pi.single j 1) (Pi.single j 1) = 0) : Ξ = 0 := by
  interval_cases d
  · apply tri_ext
    intro i
    exact i.elim0
  · apply tri_ext
    intro i j k
    fin_cases i
    fin_cases j
    fin_cases k
    exact hb _ 0
  · exact standard_zero2 Ξ hsym hb

def triangle : Tri F 3 := triOfCoeff (fun i j k : Fin 3 => if i ≠ j ∧ i ≠ k ∧ j ≠ k then 1 else 0)

theorem triangle_single (i j k : Fin 3) :
    (triangle : Tri F 3) (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) =
      if i ≠ j ∧ i ≠ k ∧ j ≠ k then 1 else 0 := triOfCoeff_single _ i j k

set_option linter.unusedSimpArgs false in
theorem standard_zero3_shape (Ξ : Tri F 3) (hsym : SymTri Ξ)
    (hb : ∀ h (j : Fin 3), Ξ h (Pi.single j 1) (Pi.single j 1) = 0) :
    ∃ t : F, Ξ = t • triangle := by
  let T : Fin 3 → Fin 3 → Fin 3 → F := fun i j k => Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)
  have hs (i j k : Fin 3) : T i j k = T k j i := hsym.1 _ _ _
  have ht (i j k : Fin 3) : T i j k = T i k j := hsym.2 _ _ _
  have hd (i j : Fin 3) : T i j j = 0 := hb _ j
  have hp000 : T 0 0 0 = 0 := hd 0 0
  have hp001 : T 0 0 1 = 0 := (hs 0 0 1).trans (hd 1 0)
  have hp002 : T 0 0 2 = 0 := (hs 0 0 2).trans (hd 2 0)
  have hp010 : T 0 1 0 = 0 := (ht 0 1 0).trans ((hs 0 0 1).trans (hd 1 0))
  have hp011 : T 0 1 1 = 0 := hd 0 1
  have hp020 : T 0 2 0 = 0 := (ht 0 2 0).trans ((hs 0 0 2).trans (hd 2 0))
  have hp021 : T 0 2 1 = T 0 1 2 := ht 0 2 1
  have hp022 : T 0 2 2 = 0 := hd 0 2
  have hp100 : T 1 0 0 = 0 := (hs 1 0 0).trans ((hs 0 0 1).trans (hd 1 0))
  have hp101 : T 1 0 1 = 0 := (ht 1 0 1).trans ((hs 1 1 0).trans (hd 0 1))
  have hp102 : T 1 0 2 = T 0 1 2 := (hs 1 0 2).trans ((ht 2 0 1).trans (hs 2 1 0))
  have hp110 : T 1 1 0 = 0 := (hs 1 1 0).trans (hd 0 1)
  have hp111 : T 1 1 1 = 0 := hd 1 1
  have hp112 : T 1 1 2 = 0 := (hs 1 1 2).trans (hd 2 1)
  have hp120 : T 1 2 0 = T 0 1 2 := (hs 1 2 0).trans (ht 0 2 1)
  have hp121 : T 1 2 1 = 0 := (ht 1 2 1).trans ((hs 1 1 2).trans (hd 2 1))
  have hp122 : T 1 2 2 = 0 := hd 1 2
  have hp200 : T 2 0 0 = 0 := (hs 2 0 0).trans ((hs 0 0 2).trans (hd 2 0))
  have hp201 : T 2 0 1 = T 0 1 2 := (ht 2 0 1).trans (hs 2 1 0)
  have hp202 : T 2 0 2 = 0 := (ht 2 0 2).trans ((hs 2 2 0).trans (hd 0 2))
  have hp210 : T 2 1 0 = T 0 1 2 := hs 2 1 0
  have hp211 : T 2 1 1 = 0 := (hs 2 1 1).trans ((hs 1 1 2).trans (hd 2 1))
  have hp212 : T 2 1 2 = 0 := (ht 2 1 2).trans ((hs 2 2 1).trans (hd 1 2))
  have hp220 : T 2 2 0 = 0 := (hs 2 2 0).trans (hd 0 2)
  have hp221 : T 2 2 1 = 0 := (hs 2 2 1).trans (hd 1 2)
  have hp222 : T 2 2 2 = 0 := hd 2 2
  refine ⟨T 0 1 2, ?_⟩
  apply tri_ext
  intro i j k
  simp only [LinearMap.smul_apply, smul_eq_mul, triangle_single]
  change T i j k = _
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hp000, hp001, hp002, hp010, hp011, hp020, hp021, hp022, hp100, hp101, hp102, hp110, hp111, hp112, hp120, hp121, hp122, hp200, hp201, hp202, hp210, hp211, hp212, hp220, hp221, hp222]

theorem slice_triangle_12 (h : Fin 3 → F) : slice (triangle : Tri F 3) h 1 2 = h 0 := by
  rw [slice_apply, tri_eval]
  simp [triangle_single, Fin.sum_univ_succ, Pi.single_apply]

theorem slice_triangle_02 (h : Fin 3 → F) : slice (triangle : Tri F 3) h 0 2 = h 1 := by
  rw [slice_apply, tri_eval]
  simp [triangle_single, Fin.sum_univ_succ, Pi.single_apply]

theorem slice_triangle_01 (h : Fin 3 → F) : slice (triangle : Tri F 3) h 0 1 = h 2 := by
  rw [slice_apply, tri_eval]
  simp [triangle_single, Fin.sum_univ_succ, Pi.single_apply]

theorem slice_triangle_injective : Function.Injective (slice (triangle : Tri F 3)) := by
  intro h h' heq
  have h0 := congrFun (congrFun heq 1) 2
  have h1 := congrFun (congrFun heq 0) 2
  have h2 := congrFun (congrFun heq 0) 1
  rw [slice_triangle_12, slice_triangle_12] at h0
  rw [slice_triangle_02, slice_triangle_02] at h1
  rw [slice_triangle_01, slice_triangle_01] at h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem triangle_fixed (φ : F →+* F) : mapTri φ (triangle : Tri F 3) = triangle := by
  apply tri_ext
  intro i j k
  simp only [mapTri_single, triangle_single]
  split_ifs <;> simp only [map_zero, map_one]

end

end

end Praxis.Proofs.Classification
