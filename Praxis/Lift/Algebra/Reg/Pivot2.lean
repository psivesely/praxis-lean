import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Algebra.Prefix.Chain
import Praxis.Algebra.Prefix.Height
import Praxis.Algebra.Prefix.Mono
import Praxis.Algebra.Prefix.Order
import Praxis.Lift.Record
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.IntegerLift
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Pivot2

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open scoped BigOperators Matrix

variable {n : ℕ}

def coordinateMap {ι κ : Type*} (e : κ ≃ ι) :
    (ι → ℤ) →ₗ[ℤ] (κ → ℤ) where
  toFun x := x ∘ e
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem map_saturated {ι κ : Type*} [Fintype ι] {d : ℕ}
    (L : IntLat ι d) (e : κ ≃ ι) :
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

theorem saturation_eq_self {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Submodule ℤ (ι → ℤ))
    (hS : Algebra.Lattice.IsSaturated S) : Algebra.Lattice.saturation S = S := by
  apply le_antisymm
  · rintro x ⟨a, ha, hx⟩
    exact hS a ha x hx
  · exact Algebra.Lattice.le_saturation S

theorem budget_comp {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Q : VITData) (G : ι → ℕ) (c : κ → ι)
    (hc : Function.Injective c) (hG : GridBudget Q G) : GridBudget Q (G ∘ c) := by
  obtain ⟨h1, h2, h3⟩ := hG
  refine ⟨fun i => h1 (c i), ?_, fun i => h3 (c i)⟩
  have himg : ∑ x ∈ univ.image c, ((G x : ℕ) : ℝ)^2 = ∑ i, ((G (c i) : ℕ) : ℝ)^2 :=
    Finset.sum_image (fun x _ y _ h => hc h)
  have hsub : ∑ x ∈ univ.image c, ((G x : ℕ) : ℝ)^2 ≤ ∑ x, ((G x : ℕ) : ℝ)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  exact (himg.symm.le.trans hsub).trans h2

theorem saturation_rank {k : ℕ} (B : Matrix (Fin k) (Fin 2) ℤ)
    (hB : Function.Injective B.mulVecLin) :
    ((Algebra.Lattice.saturation B.mulVecLin.range).basisOfPid
      (Pi.basisFun ℤ (Fin k))).1 = 2 := by
  have h := Module.finrank_eq_card_basis
    ((Algebra.Lattice.saturation B.mulVecLin.range).basisOfPid
      (Pi.basisFun ℤ (Fin k))).2
  rw [Algebra.Lattice.finrank_saturation, ← (LinearEquiv.ofInjective _ hB).finrank_eq,
    Module.finrank_fin_fun, Fintype.card_fin] at h
  exact h.symm

noncomputable def satLattice {k : ℕ} (B : Matrix (Fin k) (Fin 2) ℤ)
    (hB : Function.Injective B.mulVecLin) : IntLat (Fin k) 2 where
  carrier := Algebra.Lattice.saturation B.mulVecLin.range
  basis := ((Algebra.Lattice.saturation B.mulVecLin.range).basisOfPid
    (Pi.basisFun ℤ (Fin k))).2.reindex (finCongr (saturation_rank B hB))
  saturated := Algebra.Lattice.saturation_isSaturated _

theorem exists_pivot_order (L : IntLat (Fin n) 2) :
    ∃ (hn : 2 ≤ n) (e : Equiv.Perm (Fin n)),
      (L.matrix.submatrix (fun a : Fin 2 => e ⟨a.val, lt_of_lt_of_le a.isLt hn⟩)
        id).det.natAbs = L.H := by
  classical
  obtain ⟨r, hr, hmax⟩ :=
    Algebra.VectorInverse.exists_maximal_basis_minor L.carrier L.saturated L.basis
  have hinj := Algebra.VectorInverse.pivot_injective L.matrix r hr
  have hn : 2 ≤ n := by
    simpa using Fintype.card_le_of_injective r hinj
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (fun a : Fin 2 => (⟨a.val, lt_of_lt_of_le a.isLt hn⟩ : Fin n)) r
    (fun a b h => Fin.ext (Fin.mk.inj h)) hinj
  refine ⟨hn, e, ?_⟩
  have hf : (fun a : Fin 2 => e ⟨a.val, lt_of_lt_of_le a.isLt hn⟩) = r := funext he
  rw [hf]
  exact (Algebra.VectorInverse.largestMinor_eq_pivot L.matrix r hmax).symm

section Construction

variable (L : IntLat (Fin n) 2) (e : Equiv.Perm (Fin n)) (hn : 2 ≤ n)
  (hpiv : (L.matrix.submatrix
    (fun a : Fin 2 => e ⟨a.val, lt_of_lt_of_le a.isLt hn⟩) id).det.natAbs = L.H)

include hn hpiv in

theorem prefix_injective {k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    Function.Injective (L.matrix.submatrix
      (fun i : Fin k => e ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩) id).mulVecLin := by
  have hdet : (L.matrix.submatrix
      (fun a : Fin 2 => e ⟨a.val, lt_of_lt_of_le a.isLt hn⟩) id).det ≠ 0 := by
    apply Int.natAbs_ne_zero.mp
    rw [hpiv]
    exact ne_of_gt (Algebra.Prefix.height_pos L)
  intro x y hxy
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  ext a
  exact congrFun hxy ⟨a.val, lt_of_lt_of_le a.isLt hk⟩

noncomputable def pivotPrefix (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    PivotFirstPrefix 2 n k where
  rank_lower := by decide
  rank_upper := by decide
  rank_le_prefix := hk
  prefix_le_ambient := hkn
  original := L
  order := e
  maximal_pivot := hpiv
  pivot_nonzero := Algebra.Prefix.height_pos L
  rows := AddSubgroup.closure (Set.range
    (fun i : Fin k => L.matrix (e ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩)))
  rows_eq := rfl
  primitive := satLattice (L.matrix.submatrix
    (fun i : Fin k => e ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩) id)
    (prefix_injective L e hn hpiv hk hkn)
  primitive_eq := rfl

theorem unit_height (M : IntLat (Fin 2) 2) : M.H = 1 := by
  have hminor (r : Fin 2 → Fin 2) :
      (M.matrix.submatrix r id).det.natAbs = 0 ∨
      (M.matrix.submatrix r id).det.natAbs = M.matrix.det.natAbs := by
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, id_eq]
    generalize r 0 = a
    generalize r 1 = b
    fin_cases a <;> fin_cases b
    · left; simp [mul_comm]
    · right; rfl
    · right
      have h : M.matrix 1 0 * M.matrix 0 1 - M.matrix 1 1 * M.matrix 0 0 =
          -(M.matrix 0 0 * M.matrix 1 1 - M.matrix 0 1 * M.matrix 1 0) := by ring
      change (M.matrix 1 0 * M.matrix 0 1 - M.matrix 1 1 * M.matrix 0 0).natAbs = _
      rw [h, Int.natAbs_neg]
    · left; simp [mul_comm]

  have hg : (univ.gcd fun r : Fin 2 → Fin 2 =>
      (M.matrix.submatrix r id).det.natAbs) = M.matrix.det.natAbs := by
    apply Nat.dvd_antisymm
    · simpa using (Finset.gcd_dvd (s := (univ : Finset (Fin 2 → Fin 2)))
        (f := fun r => (M.matrix.submatrix r id).det.natAbs) (mem_univ id))
    · apply Finset.dvd_gcd
      intro r _
      rcases hminor r with h | h <;> simp [h]
  have hdet : M.matrix.det.natAbs = 1 := hg.symm.trans (Algebra.Prefix.saturated_minor_gcd M)
  apply le_antisymm
  · change (univ.sup fun r : Fin 2 → Fin 2 => (M.matrix.submatrix r id).det.natAbs) ≤ 1
    apply Finset.sup_le
    intro r _
    rcases hminor r with h | h <;> rw [h] <;> omega
  · exact Algebra.Prefix.height_pos M

theorem full_carrier :
    (pivotPrefix L e hn hpiv n hn le_rfl).primitive.carrier =
      L.carrier.map (coordinateMap e) := by
  have hr : (L.matrix.submatrix (fun i : Fin n => e i) id).mulVecLin =
      (coordinateMap e).comp L.matrix.mulVecLin := by
    ext x i
    rfl
  change Algebra.Lattice.saturation
    (L.matrix.submatrix (fun i : Fin n => e i) id).mulVecLin.range = _
  rw [hr, LinearMap.range_comp, Algebra.Prefix.basis_matrix_range,
    saturation_eq_self _ (map_saturated L e)]

theorem full_mass (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) :
    (pivotPrefix L e hn hpiv n hn le_rfl).primitive.mZ
      ((pivotPrefix L e hn hpiv n hn le_rfl).grids G) = L.mZ G := by
  let P := pivotPrefix L e hn hpiv n hn le_rfl
  rw [Algebra.Prefix.primitive_mass_eq (P.grids G) (fun i => hG (P.coord i))
    P.matrix P.primitive P.primitive_eq]
  change Algebra.FiniteProbability.atomMass (imageZ (G ∘ e) (L.matrix.submatrix e id)) =
    Algebra.FiniteProbability.atomMass (imageZ G L.matrix)
  have hcomp : imageZ (G ∘ e) (L.matrix.submatrix e id) =
      imageZ G L.matrix ∘ (Equiv.piCongrLeft (fun i : Fin n => Fin (G i)) e) := by
    funext r j
    change (∑ i : Fin n, L.matrix (e i) j * (r i : ℤ)) =
      ∑ i : Fin n, L.matrix i j *
        ((Equiv.piCongrLeft (fun i : Fin n => Fin (G i)) e) r i : ℤ)
    refine Fintype.sum_equiv e _ _ (fun i => ?_)
    exact congrArg (fun x : Fin (G (e i)) => L.matrix (e i) j * (x : ℤ))
      (Equiv.piCongrLeft_apply_apply (fun i : Fin n => Fin (G i)) e r i).symm
  rw [hcomp]
  exact Algebra.Prefix.mass_precomp_equiv
    (Equiv.piCongrLeft (fun i : Fin n => Fin (G i)) e) (imageZ G L.matrix)

theorem full_height : (pivotPrefix L e hn hpiv n hn le_rfl).primitive.H = L.H := by
  let P := pivotPrefix L e hn hpiv n hn le_rfl
  have hdiv : P.divisor = 1 := by
    have hd : P.divisor ∣ univ.gcd
        (fun r : Fin 2 → Fin n => (L.matrix.submatrix r id).det.natAbs) := by
      apply Finset.dvd_gcd
      intro r _
      have h := Finset.gcd_dvd (s := (univ : Finset (Fin 2 → Fin n)))
        (f := fun r => (P.matrix.submatrix r id).det.natAbs)
        (mem_univ (fun a => e.symm (r a)))
      have hm : P.matrix.submatrix (fun a => e.symm (r a)) id = L.matrix.submatrix r id := by
        ext a b
        change L.matrix (e ⟨(e.symm (r a)).val, _⟩) b = L.matrix (r a) b
        simp only [Fin.eta, Equiv.apply_symm_apply]
      rwa [hm] at h
    rw [Algebra.Prefix.saturated_minor_gcd] at hd
    exact Nat.dvd_one.mp hd
  have h := Algebra.Prefix.prefix_height P
  change P.divisor * P.primitive.H = L.H at h
  simpa [hdiv] using h

set_option maxHeartbeats 800000 in

noncomputable def pivotStep (G : Fin n → ℕ) (hG : ∀ i, 0 < G i)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k + 1 ≤ n) : PivotFirstStep 2 n k where
  old := pivotPrefix L e hn hpiv k hk ((Nat.le_succ k).trans hkn)
  next := pivotPrefix L e hn hpiv (k+1) (hk.trans (Nat.le_succ k)) hkn
  same_original := by change L = L; rfl
  same_order := by change e = e; rfl
  grids := G
  grids_pos := hG
  residueOrder := addOrderOf (QuotientAddGroup.mk'
    (pivotPrefix L e hn hpiv k hk ((Nat.le_succ k).trans hkn)).rows
    (L.matrix (e ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hkn⟩)))
  quotient_order := rfl

theorem step_identities {k : ℕ} (S : PivotFirstStep 2 n k) :
    1 ≤ S.residueOrder ∧
    S.next.primitive.H = S.residueOrder * S.old.primitive.H ∧ PrefixMassMono S := by
  have hO := Algebra.Prefix.Order.prefix_order S
  have h1 := Algebra.Prefix.prefix_height S.old
  have h2 := Algebra.Prefix.prefix_height S.next
  change S.old.divisor = S.residueOrder * S.next.divisor at hO
  change S.old.divisor * S.old.primitive.H = S.old.original.H at h1
  change S.next.divisor * S.next.primitive.H = S.next.original.H at h2
  rw [S.same_original] at h2
  have hp := S.old.pivot_nonzero
  have hd : 0 < S.next.divisor := by nlinarith
  have hod : 0 < S.old.divisor := by nlinarith
  have ho : 1 ≤ S.residueOrder := by
    by_contra h
    have hz : S.residueOrder = 0 := by omega
    rw [hz, zero_mul] at hO
    omega
  refine ⟨ho, ?_, Algebra.Prefix.prefix_mass_mono S⟩
  apply Nat.eq_of_mul_eq_mul_left hd
  calc S.next.divisor * S.next.primitive.H = S.old.original.H := h2
    _ = S.old.divisor * S.old.primitive.H := h1.symm
    _ = S.next.divisor * (S.residueOrder * S.old.primitive.H) := by rw [hO]; ring

end Construction

structure Presentation {n : ℕ} (L : IntLat (Fin n) 2) where
  lower : 2 ≤ n
  order : Equiv.Perm (Fin n)
  maximal : (L.matrix.submatrix
    (fun a : Fin 2 => order ⟨a.val, lt_of_lt_of_le a.isLt lower⟩) id).det.natAbs = L.H

noncomputable def presentation {n : ℕ} (L : IntLat (Fin n) 2) : Presentation L :=
  let h := exists_pivot_order L
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

namespace Presentation

variable {n : ℕ} {L : IntLat (Fin n) 2} (R : Presentation L)

noncomputable def prefixes (k : Fin (n - 2 + 1)) : PivotFirstPrefix 2 n (k.val + 2) :=
  pivotPrefix L R.order R.lower R.maximal (k.val + 2) (by omega)
    (by have := k.isLt; have := R.lower; omega)

noncomputable def lattices (k : Fin (n - 2 + 1)) : IntLat (Fin (k.val + 2)) 2 :=
  (R.prefixes k).primitive

noncomputable def grids (G : Fin n → ℕ) (k : Fin (n - 2 + 1)) : Fin (k.val + 2) → ℕ :=
  (R.prefixes k).grids G

noncomputable def step (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) (k : Fin (n - 2)) :
    PivotFirstStep 2 n (k.val + 2) :=
  pivotStep L R.order R.lower R.maximal G hG (k.val + 2) (by omega)
    (by have := k.isLt; have := R.lower; omega)

theorem budget (Q : VITData) (G : Fin n → ℕ) (hG : GridBudget Q G)
    (k : Fin (n - 2 + 1)) : GridBudget Q (R.grids G k) := by
  apply budget_comp Q G (R.prefixes k).coord _ hG
  intro a b h
  exact Fin.ext (Fin.mk.inj (R.order.injective h))

theorem first (P : VITParameters) (G : Fin n → ℕ) (hG : GridBudget P.toVITData G) :
    (R.lattices 0).H = 1 ∧
      (R.lattices 0).mZ (R.grids G 0) ≤ 1 / (P.g : ℝ)^2 := by
  refine ⟨unit_height _, ?_⟩
  exact Algebra.Prefix.integer_mass_pivot _ _ P.g (by decide) (by decide)
    (Algebra.Reg.grid_lower_pos P) (R.budget P.toVITData G hG 0).1

theorem hfirst (P : VITParameters) (G : Fin n → ℕ) (hG : GridBudget P.toVITData G)
    (F : (k : Fin (n - 2 + 1)) → Finset (Grid (R.grids G k))) :
    ordinaryNormals (R.grids G 0) (F 0) = (R.lattices 0).carrier →
      (R.lattices 0).H = 1 ∧ (R.lattices 0).mZ (R.grids G 0) ≤ 1 / (P.g : ℝ)^2 :=
  fun _ => R.first P G hG

theorem hmono (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) (k : Fin (n - 2)) :
    (R.lattices k.succ).mZ (R.grids G k.succ) ≤
      (R.lattices k.castSucc).mZ (R.grids G k.castSucc) :=
  (step_identities (R.step G hG k)).2.2

theorem last_height : (R.lattices (Fin.last (n - 2))).H = L.H := by
  have hh (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (he : k = n) :
      (pivotPrefix L R.order R.lower R.maximal k hk hkn).primitive.H = L.H := by
    subst k
    exact full_height L R.order R.lower R.maximal
  exact hh _ _ _ (Nat.sub_add_cancel R.lower)

theorem last_mass (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) :
    (R.lattices (Fin.last (n - 2))).mZ (R.grids G (Fin.last (n - 2))) = L.mZ G := by
  have hh (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (he : k = n) :
      (pivotPrefix L R.order R.lower R.maximal k hk hkn).primitive.mZ
        ((pivotPrefix L R.order R.lower R.maximal k hk hkn).grids G) = L.mZ G := by
    subst k
    exact full_mass L R.order R.lower R.maximal G hG
  exact hh _ _ _ (Nat.sub_add_cancel R.lower)

def lastOrder : Fin (n - 2 + 2) ≃ Fin n :=
  (finCongr (Nat.sub_add_cancel R.lower)).trans R.order

theorem last_carrier : (R.lattices (Fin.last (n - 2))).carrier =
    L.carrier.map (coordinateMap R.lastOrder) := by
  have hh (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (he : k = n) :
      (pivotPrefix L R.order R.lower R.maximal k hk hkn).primitive.carrier =
        L.carrier.map (coordinateMap ((finCongr he).trans R.order)) := by
    subst k
    exact full_carrier L R.order R.lower R.maximal
  exact hh _ _ _ (Nat.sub_add_cancel R.lower)

end Presentation

def pairTypes (k : ℕ) : Fin 2 → Type :=
  Fin.cases (Fin k) (fun _ => Fin (k+1))

instance pairFintype (k : ℕ) (j : Fin 2) : Fintype (pairTypes k j) :=
  Fin.cases (inferInstance : Fintype (Fin k))
    (fun _ => (inferInstance : Fintype (Fin (k+1)))) j

instance pairDecidableEq (k : ℕ) (j : Fin 2) : DecidableEq (pairTypes k j) :=
  Fin.cases (inferInstance : DecidableEq (Fin k))
    (fun _ => (inferInstance : DecidableEq (Fin (k+1)))) j

noncomputable def pairLattices {n k : ℕ} (S : PivotFirstStep 2 n k) :
    (j : Fin 2) → IntLat (pairTypes k j) 2 :=
  Fin.cases S.old.primitive (fun _ => S.next.primitive)

noncomputable def pairGrids {n k : ℕ} (S : PivotFirstStep 2 n k) :
    (j : Fin 2) → pairTypes k j → ℕ :=
  Fin.cases (S.old.grids S.grids) (fun _ => S.next.grids S.grids)

theorem pair_hheight {n k : ℕ} (S : PivotFirstStep 2 n k) :
    (pairLattices S 1).H = S.residueOrder * (pairLattices S 0).H :=
  (step_identities S).2.1

theorem pair_hmono {n k : ℕ} (S : PivotFirstStep 2 n k) :
    (pairLattices S 1).mZ (pairGrids S 1) ≤
      (pairLattices S 0).mZ (pairGrids S 0) :=
  (step_identities S).2.2

theorem pair_positive {n k : ℕ} (S : PivotFirstStep 2 n k) :
    ∀ j i, 0 < pairGrids S j i := by
  intro j
  refine Fin.cases ?_ (fun _ => ?_) j
  · exact fun i => S.grids_pos (S.old.coord i)
  · exact fun i => S.grids_pos (S.next.coord i)

def coordinateEquiv {ι κ : Type*} (c : κ ≃ ι) : (ι → ℤ) ≃ₗ[ℤ] (κ → ℤ) where
  toLinearMap := coordinateMap c
  invFun y := y ∘ c.symm
  left_inv := by intro x; ext i; exact congrArg x (c.apply_symm_apply i)
  right_inv := by intro y; ext i; exact congrArg y (c.symm_apply_apply i)

noncomputable def transport {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (L : IntLat ι d) (c : κ ≃ ι) : IntLat κ d where
  carrier := L.carrier.map (coordinateMap c)
  basis := L.basis.map ((coordinateEquiv c).submoduleMap L.carrier)
  saturated := map_saturated L c

theorem transport_matrix {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (L : IntLat ι d) (c : κ ≃ ι) : (transport L c).matrix = L.matrix.submatrix c id := by
  ext i j
  rfl

theorem transport_height {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (L : IntLat ι d) (c : κ ≃ ι) : (transport L c).H = L.H := by
  classical
  unfold IntLat.H height Algebra.VectorInverse.largestMinor
  rw [transport_matrix]
  apply le_antisymm
  · apply Finset.sup_le
    intro r _
    exact Finset.le_sup (f := fun r : Fin d → ι =>
      (L.matrix.submatrix r id).det.natAbs) (mem_univ (c ∘ r))
  · apply Finset.sup_le
    intro r _
    have h := Finset.le_sup (f := fun r : Fin d → κ =>
      ((L.matrix.submatrix c id).submatrix r id).det.natAbs) (mem_univ (c.symm ∘ r))
    have he : (L.matrix.submatrix c id).submatrix (c.symm ∘ r) id =
        L.matrix.submatrix r id := by ext a b; simp
    rwa [he] at h

theorem transport_mass {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {d : ℕ} (L : IntLat ι d) (c : κ ≃ ι) (G : ι → ℕ) :
    (transport L c).mZ (G ∘ c) = L.mZ G := by
  unfold IntLat.mZ
  rw [transport_matrix]
  have he : imageZ (G ∘ c) (L.matrix.submatrix c id) =
      imageZ G L.matrix ∘ (Equiv.piCongrLeft (fun i => Fin (G i)) c) := by
    funext r j
    change (∑ i : κ, L.matrix (c i) j * (r i : ℤ)) =
      ∑ i : ι, L.matrix i j *
        ((Equiv.piCongrLeft (fun i => Fin (G i)) c) r i : ℤ)
    refine Fintype.sum_equiv c _ _ (fun i => ?_)
    exact congrArg (fun x : Fin (G (c i)) => L.matrix (c i) j * (x : ℤ))
      (Equiv.piCongrLeft_apply_apply (fun i => Fin (G i)) c r i).symm
  change Algebra.FiniteProbability.atomMass _ = Algebra.FiniteProbability.atomMass _
  rw [he]
  exact Algebra.Prefix.mass_precomp_equiv
    (Equiv.piCongrLeft (fun i => Fin (G i)) c) (imageZ G L.matrix)

theorem last_transport {ι : Type*} [Fintype ι] (L : IntLat ι 2)
    (c : Fin (Fintype.card ι) ≃ ι) (R : Presentation (transport L c)) :
    (R.lattices (Fin.last (Fintype.card ι - 2))).carrier =
      L.carrier.map (coordinateMap (R.lastOrder.trans c)) := by
  rw [R.last_carrier]
  change (L.carrier.map (coordinateMap c)).map (coordinateMap R.lastOrder) = _
  rw [← Submodule.map_comp]
  rfl

end Algebra.Reg.Pivot2

end Praxis.Lift
