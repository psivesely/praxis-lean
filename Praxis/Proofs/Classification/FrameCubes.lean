import Praxis.Proofs.Classification.Cubic

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section

variable {F : Type*} [Field F]

def point3 (s : Fin 4) : Fin 3 → F :=
  (![![1, 0, 0], ![1, 1, 0], ![1, 0, 1], ![1, 1, 1]] : Fin 4 → Fin 3 → F) s

set_option linter.unusedSimpArgs false in
theorem standard_frame3_cubes (Ξ : Tri F 3) (hsym : SymTri Ξ)
    (hb₁ : ∀ h, Ξ h (Pi.single 1 1) (Pi.single 1 1 - Pi.single 0 1) = 0)
    (hb₂ : ∀ h, Ξ h (Pi.single 2 1) (Pi.single 2 1 - Pi.single 0 1) = 0) :
    ∃ c : Fin 4 → F, Ξ = ∑ s, c s • cube (point3 s) := by
  let T : Fin 3 → Fin 3 → Fin 3 → F := fun i j k =>
    Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)
  have hs (i j k : Fin 3) : T i j k = T k j i := hsym.1 _ _ _
  have ht (i j k : Fin 3) : T i j k = T i k j := hsym.2 _ _ _
  have hb₁' (i : Fin 3) : T i 1 1 = T i 1 0 := by
    have h := hb₁ (Pi.single i 1)
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hb₂' (i : Fin 3) : T i 2 2 = T i 2 0 := by
    have h := hb₂ (Pi.single i 1)
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have h011 : T 0 1 1 = T 0 0 1 := (hb₁' 0).trans (ht 0 1 0)
  have h111 : T 1 1 1 = T 0 0 1 := (hb₁' 1).trans ((hs 1 1 0).trans h011)
  have h112 : T 1 1 2 = T 0 1 2 := (hs 1 1 2).trans ((hb₁' 2).trans (hs 2 1 0))
  have h022 : T 0 2 2 = T 0 0 2 := (hb₂' 0).trans (ht 0 2 0)
  have h122 : T 1 2 2 = T 0 1 2 := (hb₂' 1).trans ((hs 1 2 0).trans (ht 0 2 1))
  have h222 : T 2 2 2 = T 0 0 2 := (hb₂' 2).trans ((hs 2 2 0).trans h022)
  have hp010 : T 0 1 0 = T 0 0 1 := ht 0 1 0
  have hp011 : T 0 1 1 = T 0 0 1 := h011
  have hp020 : T 0 2 0 = T 0 0 2 := ht 0 2 0
  have hp021 : T 0 2 1 = T 0 1 2 := ht 0 2 1
  have hp022 : T 0 2 2 = T 0 0 2 := h022
  have hp100 : T 1 0 0 = T 0 0 1 := hs 1 0 0
  have hp101 : T 1 0 1 = T 0 0 1 := (ht 1 0 1).trans ((hs 1 1 0).trans (h011))
  have hp102 : T 1 0 2 = T 0 1 2 := (hs 1 0 2).trans ((ht 2 0 1).trans (hs 2 1 0))
  have hp110 : T 1 1 0 = T 0 0 1 := (hs 1 1 0).trans (h011)
  have hp111 : T 1 1 1 = T 0 0 1 := h111
  have hp112 : T 1 1 2 = T 0 1 2 := h112
  have hp120 : T 1 2 0 = T 0 1 2 := (hs 1 2 0).trans (ht 0 2 1)
  have hp121 : T 1 2 1 = T 0 1 2 := (ht 1 2 1).trans (h112)
  have hp122 : T 1 2 2 = T 0 1 2 := h122
  have hp200 : T 2 0 0 = T 0 0 2 := hs 2 0 0
  have hp201 : T 2 0 1 = T 0 1 2 := (ht 2 0 1).trans (hs 2 1 0)
  have hp202 : T 2 0 2 = T 0 0 2 := (ht 2 0 2).trans ((hs 2 2 0).trans (h022))
  have hp210 : T 2 1 0 = T 0 1 2 := hs 2 1 0
  have hp211 : T 2 1 1 = T 0 1 2 := (hs 2 1 1).trans (h112)
  have hp212 : T 2 1 2 = T 0 1 2 := (ht 2 1 2).trans ((hs 2 2 1).trans (h122))
  have hp220 : T 2 2 0 = T 0 0 2 := (hs 2 2 0).trans (h022)
  have hp221 : T 2 2 1 = T 0 1 2 := (hs 2 2 1).trans (h122)
  have hp222 : T 2 2 2 = T 0 0 2 := h222
  let c : Fin 4 → F :=
    ![T 0 0 0 - T 0 0 1 - T 0 0 2 + T 0 1 2,
      T 0 0 1 - T 0 1 2, T 0 0 2 - T 0 1 2, T 0 1 2]
  refine ⟨c, ?_⟩
  apply tri_ext
  intro i j k
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, cube_apply, single_dotProduct,
    one_mul, smul_eq_mul]
  change T i j k = _
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_succ, point3, c,
      hp010, hp011, hp020, hp021, hp022, hp100, hp101, hp102, hp110, hp111, hp112, hp120, hp121, hp122, hp200, hp201, hp202, hp210, hp211, hp212, hp220, hp221, hp222] <;> ring

def point2 (s : Fin 2) : Fin 2 → F := (![![1, 0], ![1, 1]] : Fin 2 → Fin 2 → F) s

set_option linter.unusedSimpArgs false in
theorem standard_frame2_cubes (Ξ : Tri F 2) (hsym : SymTri Ξ)
    (hb : ∀ h, Ξ h (Pi.single 1 1) (Pi.single 1 1 - Pi.single 0 1) = 0) :
    ∃ c : Fin 2 → F, Ξ = ∑ s, c s • cube (point2 s) := by
  let T : Fin 2 → Fin 2 → Fin 2 → F := fun i j k =>
    Ξ (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)
  have hs (i j k : Fin 2) : T i j k = T k j i := hsym.1 _ _ _
  have ht (i j k : Fin 2) : T i j k = T i k j := hsym.2 _ _ _
  have hb' (i : Fin 2) : T i 1 1 = T i 1 0 := by
    have h := hb (Pi.single i 1)
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have h011 : T 0 1 1 = T 0 0 1 := (hb' 0).trans (ht 0 1 0)
  have h111 : T 1 1 1 = T 0 0 1 := (hb' 1).trans ((hs 1 1 0).trans h011)
  have h010 : T 0 1 0 = T 0 0 1 := ht 0 1 0
  have h100 : T 1 0 0 = T 0 0 1 := hs 1 0 0
  have h101 : T 1 0 1 = T 0 0 1 := (ht 1 0 1).trans ((hs 1 1 0).trans h011)
  have h110 : T 1 1 0 = T 0 0 1 := (hs 1 1 0).trans h011
  let c : Fin 2 → F := ![T 0 0 0 - T 0 0 1, T 0 0 1]
  refine ⟨c, ?_⟩
  apply tri_ext
  intro i j k
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, cube_apply, single_dotProduct,
    one_mul, smul_eq_mul]
  change T i j k = _
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_succ, point2, c, h010, h011, h100, h101, h110, h111] <;> ring

def point1 : Fin 1 → F := ![1]

theorem standard_frame1_cube (Ξ : Tri F 1) : ∃ c : F, Ξ = c • cube (point1) := by
  refine ⟨Ξ (Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1), ?_⟩
  apply tri_ext
  intro i j k
  fin_cases i
  fin_cases j
  fin_cases k
  simp [LinearMap.smul_apply, cube_apply, single_dotProduct, point1]

def boolPoint {d : ℕ} (s : Fin (2 ^ (d - 1))) (i : Fin d) : F :=
  if i.val = 0 then 1 else if s.val.testBit (i.val - 1) then 1 else 0

theorem boolPoint_one (s : Fin 1) : (boolPoint (d := 1) s : Fin 1 → F) = point1 := by
  ext i
  fin_cases s
  fin_cases i
  simp [boolPoint, point1]

theorem boolPoint_two (s : Fin 2) : (boolPoint (d := 2) s : Fin 2 → F) = point2 s := by
  ext i
  fin_cases s <;> fin_cases i <;> simp [boolPoint, point2]

theorem boolPoint_three (s : Fin 4) : (boolPoint (d := 3) s : Fin 3 → F) = point3 s := by
  ext i
  fin_cases s <;> fin_cases i <;> simp [boolPoint, point3] <;> decide

theorem standard_frame_cubes {d : ℕ} (hd : 0 < d) (hdim : d ≤ 3)
    (Ξ : Tri F d) (hsym : SymTri Ξ)
    (hb : ∀ h (j : Fin d), Ξ h (Pi.single j 1)
      (Pi.single j 1 - Pi.single ⟨0, hd⟩ 1) = 0) :
    ∃ c : Fin (2 ^ (d - 1)) → F, Ξ = ∑ s, c s • cube (boolPoint s) := by
  interval_cases d
  · norm_num only [Nat.reduceSub, Nat.reducePow]
    obtain ⟨c, hc⟩ := standard_frame1_cube Ξ
    refine ⟨fun _ => c, ?_⟩
    simpa [boolPoint_one, Fin.sum_univ_succ] using hc
  · norm_num only [Nat.reduceSub, Nat.reducePow]
    obtain ⟨c, hc⟩ := standard_frame2_cubes Ξ hsym (fun h => hb h 1)
    exact ⟨c, by simpa [boolPoint_two, Fin.sum_univ_succ] using hc⟩
  · norm_num only [Nat.reduceSub, Nat.reducePow]
    obtain ⟨c, hc⟩ := standard_frame3_cubes Ξ hsym (fun h => hb h 1) (fun h => hb h 2)
    exact ⟨c, by simpa [boolPoint_three, Fin.sum_univ_succ] using hc⟩

theorem standard_frame3_squares :
    LinearIndependent F (fun s : Fin 4 => Matrix.vecMulVec (point3 (F := F) s) (point3 s)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h (i j : Fin 3) := congrFun (congrFun hc i) j
  have h00 := h 0 0
  have h11 := h 1 1
  have h22 := h 2 2
  have h12 := h 1 2
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, point3,
    Fin.sum_univ_succ, smul_eq_mul] at h00 h11 h22 h12
  intro s
  fin_cases s
  · change c 0 = 0
    linear_combination h00 - h11 - h22 + h12
  · change c 1 = 0
    linear_combination h11 - h12
  · change c 2 = 0
    linear_combination h22 - h12
  · exact h12

theorem standard_frame2_squares :
    LinearIndependent F (fun s : Fin 2 => Matrix.vecMulVec (point2 (F := F) s) (point2 s)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, point2,
    Fin.sum_univ_succ, smul_eq_mul] at h00 h11
  intro s
  fin_cases s
  · change c 0 = 0
    linear_combination h00 - h11
  · exact h11

theorem standard_frame1_squares :
    LinearIndependent F (fun _ : Fin 1 => Matrix.vecMulVec (point1 : Fin 1 → F) point1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h00 := congrFun (congrFun hc 0) 0
  fin_cases i
  simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, point1,
    Fin.sum_univ_succ, smul_eq_mul] using h00

theorem standard_frame_squares {d : ℕ} (hd : 0 < d) (hdim : d ≤ 3) :
    LinearIndependent F (fun s : Fin (2 ^ (d - 1)) =>
      Matrix.vecMulVec (boolPoint (F := F) s) (boolPoint s)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  interval_cases d
  · have h : ∑ t : Fin 1, c t • Matrix.vecMulVec (point1 : Fin 1 → F) point1 = 0 := by
      simpa [boolPoint_one, Fin.sum_univ_succ] using hc
    exact Fintype.linearIndependent_iff.mp (standard_frame1_squares (F := F)) c h s
  · have h : ∑ t : Fin 2, c t • Matrix.vecMulVec (point2 (F := F) t) (point2 t) = 0 := by
      simpa [boolPoint_two, Fin.sum_univ_succ] using hc
    exact Fintype.linearIndependent_iff.mp (standard_frame2_squares (F := F)) c h s
  · have h : ∑ t : Fin 4, c t • Matrix.vecMulVec (point3 (F := F) t) (point3 t) = 0 := by
      simpa [boolPoint_three, Fin.sum_univ_succ] using hc
    exact Fintype.linearIndependent_iff.mp (standard_frame3_squares (F := F)) c h s

end

end

end Praxis.Proofs.Classification
