import Praxis.Algebra.Reg.Rank1Model
import Praxis.Algebra.Prefix.Chain
import Praxis.Algebra.Prefix.Height
import Praxis.Algebra.Prefix.Mono
import Praxis.Algebra.Prefix.Order
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

namespace Praxis.Algebra.Reg.Pivot1

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions Praxis.Algebra.Reg.Rank1Model

open scoped BigOperators Matrix

theorem mulVecLin_injective {k : ℕ} (B : Matrix (Fin k) (Fin 1) ℤ) (i : Fin k)
    (hi : B i 0 ≠ 0) : Function.Injective B.mulVecLin := by
  intro x y hxy
  have h := congrFun hxy i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one] at h
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact mul_left_cancel₀ hi h

theorem saturation_rank {k : ℕ} (B : Matrix (Fin k) (Fin 1) ℤ)
    (hB : Function.Injective B.mulVecLin) :
    ((Algebra.Lattice.saturation (LinearMap.range B.mulVecLin)).basisOfPid
      (Pi.basisFun ℤ (Fin k))).1 = 1 := by
  have h1 := Module.finrank_eq_card_basis
    ((Algebra.Lattice.saturation (LinearMap.range B.mulVecLin)).basisOfPid
      (Pi.basisFun ℤ (Fin k))).2
  rw [Algebra.Lattice.finrank_saturation, ← (LinearEquiv.ofInjective _ hB).finrank_eq,
    Module.finrank_fin_fun, Fintype.card_fin] at h1
  exact h1.symm

noncomputable def satLattice {k : ℕ} (B : Matrix (Fin k) (Fin 1) ℤ)
    (hB : Function.Injective B.mulVecLin) : IntLat (Fin k) 1 where
  carrier := Algebra.Lattice.saturation (LinearMap.range B.mulVecLin)
  basis := ((Algebra.Lattice.saturation (LinearMap.range B.mulVecLin)).basisOfPid
      (Pi.basisFun ℤ (Fin k))).2.reindex (finCongr (saturation_rank B hB))
  saturated := Algebra.Lattice.saturation_isSaturated _

theorem exists_nonzero_entry {n : ℕ} (L : IntLat (Fin n) 1) :
    ∃ i, L.matrix i 0 ≠ 0 := by
  have h0 : (L.basis 0 : Fin n → ℤ) ≠ 0 := fun h => L.basis.ne_zero 0 (Subtype.ext h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
  exact ⟨i, hi⟩

theorem height_eq_max {n : ℕ} (L : IntLat (Fin n) 1) (j : Fin n)
    (hj : ∀ i, (L.matrix i 0).natAbs ≤ (L.matrix j 0).natAbs) :
    (L.matrix j 0).natAbs = L.H := by
  unfold IntLat.H Algebra.Inverse.Definitions.height Algebra.VectorInverse.largestMinor
  apply le_antisymm
  · have h := Finset.le_sup (f := fun r : Fin 1 → Fin n =>
      (L.matrix.submatrix r id).det.natAbs) (mem_univ (fun _ => j))
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply, id_eq] using h
  · apply Finset.sup_le
    intro r _
    simp only [Matrix.det_fin_one, Matrix.submatrix_apply, id_eq]
    exact hj (r 0)

theorem unit_height (M : IntLat (Fin 1) 1) : M.H = 1 := by
  have h := Algebra.Prefix.saturated_minor_gcd M
  rw [Finset.univ_unique, Finset.gcd_singleton, normalize_eq] at h
  unfold IntLat.H Algebra.Inverse.Definitions.height Algebra.VectorInverse.largestMinor
  rw [Finset.univ_unique, Finset.sup_singleton]
  exact h

variable {n : ℕ}

theorem prefix_injective (L : IntLat (Fin n) 1) (e : Equiv.Perm (Fin n))
    (hn : 1 ≤ n) (hpiv : (L.matrix (e ⟨0, hn⟩) 0).natAbs = L.H) (hpos : 0 < L.H)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Function.Injective (L.matrix.submatrix
      (fun i : Fin k => e ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩) id).mulVecLin := by
  apply mulVecLin_injective _ ⟨0, hk⟩
  have h : L.matrix (e ⟨0, hn⟩) 0 ≠ 0 := Int.natAbs_pos.mp (by rw [hpiv]; exact hpos)
  exact h

noncomputable def pivotPrefix (L : IntLat (Fin n) 1) (e : Equiv.Perm (Fin n))
    (hn : 1 ≤ n) (hpiv : (L.matrix (e ⟨0, hn⟩) 0).natAbs = L.H) (hpos : 0 < L.H)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : PivotFirstPrefix 1 n k where
  rank_lower := le_rfl
  rank_upper := by norm_num
  rank_le_prefix := hk
  prefix_le_ambient := hkn
  original := L
  order := e
  maximal_pivot := by
    rw [Matrix.det_fin_one]
    exact hpiv
  pivot_nonzero := hpos
  rows := AddSubgroup.closure (Set.range
    (fun i : Fin k => L.matrix (e ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩)))
  rows_eq := rfl
  primitive := satLattice (L.matrix.submatrix
    (fun i : Fin k => e ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩) id)
    (prefix_injective L e hn hpiv hpos hk hkn)
  primitive_eq := rfl

theorem pivotPrefix_original (L : IntLat (Fin n) 1) (e : Equiv.Perm (Fin n))
    (hn : 1 ≤ n) (hpiv : (L.matrix (e ⟨0, hn⟩) 0).natAbs = L.H) (hpos : 0 < L.H)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (pivotPrefix L e hn hpiv hpos k hk hkn).original = L := rfl

theorem pivotPrefix_order (L : IntLat (Fin n) 1) (e : Equiv.Perm (Fin n))
    (hn : 1 ≤ n) (hpiv : (L.matrix (e ⟨0, hn⟩) 0).natAbs = L.H) (hpos : 0 < L.H)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (pivotPrefix L e hn hpiv hpos k hk hkn).order = e := rfl

theorem coord_injective {k : ℕ} (P : PivotFirstPrefix 1 n k) :
    Function.Injective P.coord := by
  intro a b h
  have h' := P.order.injective h
  exact Fin.ext (Fin.mk.inj h')

theorem budget_comp (Q : VITData) (G : Fin n → ℕ) {k : ℕ} (c : Fin k → Fin n)
    (hc : Function.Injective c) (hG : GridBudget Q G) : GridBudget Q (G ∘ c) := by
  unfold GridBudget at hG ⊢
  obtain ⟨h1, h2, h3⟩ := hG
  refine ⟨fun i => h1 (c i), ?_, fun i => h3 (c i)⟩
  have himg : ∑ x ∈ univ.image c, ((G x : ℕ) : ℝ)^2 = ∑ i, ((G (c i) : ℕ) : ℝ)^2 :=
    Finset.sum_image (fun x _ y _ h => hc h)
  have hsub : ∑ x ∈ univ.image c, ((G x : ℕ) : ℝ)^2 ≤ ∑ x, ((G x : ℕ) : ℝ)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  calc (∑ i, (((G ∘ c) i : ℕ) : ℝ)^2) = ∑ i, ((G (c i) : ℕ) : ℝ)^2 := rfl
    _ = ∑ x ∈ univ.image c, ((G x : ℕ) : ℝ)^2 := himg.symm
    _ ≤ ∑ x, ((G x : ℕ) : ℝ)^2 := hsub
    _ ≤ _ := h2

theorem map_saturated {d : ℕ} (L : IntLat (Fin n) d) (e : Equiv.Perm (Fin n)) :
    Algebra.Lattice.IsSaturated (L.carrier.map (coordinateMap e)) := by
  intro a ha x hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
  have hy' : a • (x ∘ e.symm) = y := by
    funext i
    have h := congrFun hyx (e.symm i)
    change y (e (e.symm i)) = a • x (e.symm i) at h
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  refine Submodule.mem_map.mpr ⟨x ∘ e.symm, L.saturated a ha _ (by rw [hy']; exact hy), ?_⟩
  funext i
  change x (e.symm (e i)) = x i
  rw [Equiv.symm_apply_apply]

theorem saturation_eq_self (S : Submodule ℤ (Fin n → ℤ))
    (hS : Algebra.Lattice.IsSaturated S) : Algebra.Lattice.saturation S = S := by
  apply le_antisymm
  · rintro x ⟨a, ha, hx⟩
    exact hS a ha x hx
  · exact Algebra.Lattice.le_saturation S

theorem full_range (L : IntLat (Fin n) 1) (e : Equiv.Perm (Fin n)) (hnn : n ≤ n) :
    LinearMap.range (L.matrix.submatrix
      (fun i : Fin n => e ⟨i.val, lt_of_lt_of_le i.isLt hnn⟩) id).mulVecLin =
      L.carrier.map (coordinateMap e) := by
  have h : (L.matrix.submatrix
      (fun i : Fin n => e ⟨i.val, lt_of_lt_of_le i.isLt hnn⟩) id).mulVecLin =
      (coordinateMap e).comp L.matrix.mulVecLin := by
    apply LinearMap.ext
    intro c
    first
    | rfl
    | (funext i
       simp [Matrix.mulVecLin_apply, LinearMap.comp_apply, Matrix.mulVec, dotProduct,
         coordinateMap])
  rw [h, LinearMap.range_comp, Algebra.Prefix.basis_matrix_range]

end Praxis.Algebra.Reg.Pivot1
