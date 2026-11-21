import Praxis.Lift.Algebra.Reg.Step1Geometry
import Praxis.Algebra.Reg.Pivot1
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Reg.Pivot2
import Praxis.Lift.Algebra.Reg.Regularize1
import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Algebra.Reg.Step1
import Praxis.Lift.Algebra.Reg.Step2Geometry
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Prefix.Chain
import Praxis.Algebra.Prefix.Height
import Praxis.Algebra.Prefix.Mono
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Reg.Rank1Model
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Assemble1

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions Praxis.Lift.Algebra.Reg.Rank1Model

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Algebra.Reg.Rank1Model hiding Rank1Promotion Rank1Return21 Rank1Return31 Rank1NestedCall

open scoped BigOperators Matrix

variable {n : ℕ}

section Construction

variable (L : IntLat (Fin n) 1) (e : Equiv.Perm (Fin n)) (hn : 1 ≤ n)
  (hpiv : (L.matrix (e ⟨0, hn⟩) 0).natAbs = L.H)

noncomputable def pre (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : PivotFirstPrefix 1 n k :=
  Pivot1.pivotPrefix L e hn hpiv (Algebra.Prefix.height_pos L) k hk hkn

theorem full_divisor1 : (pre L e hn hpiv n hn le_rfl).divisor = 1 := by
  have hs := Algebra.Prefix.saturated_minor_gcd L
  have hd : (pre L e hn hpiv n hn le_rfl).divisor ∣
      univ.gcd (fun r : Fin 1 → Fin n => (L.matrix.submatrix r id).det.natAbs) := by
    apply Finset.dvd_gcd
    intro r _
    have h := Finset.gcd_dvd (s := (univ : Finset (Fin 1 → Fin n)))
      (f := fun r : Fin 1 → Fin n =>
        ((pre L e hn hpiv n hn le_rfl).matrix.submatrix r id).det.natAbs)
      (mem_univ (fun a => e.symm (r a)))
    have hm : (pre L e hn hpiv n hn le_rfl).matrix.submatrix (fun a => e.symm (r a)) id =
        L.matrix.submatrix r id := by
      ext a b
      change L.matrix (e ⟨(e.symm (r a)).val, _⟩) b = L.matrix (r a) b
      simp only [Fin.eta, Equiv.apply_symm_apply]
    simp only [hm] at h
    exact h
  rw [hs] at hd
  exact Nat.dvd_one.mp hd

theorem full_carrier1 :
    (pre L e hn hpiv n hn le_rfl).primitive.carrier = L.carrier.map (coordinateMap e) := by
  change Algebra.Lattice.saturation (LinearMap.range (L.matrix.submatrix
    (fun i : Fin n => e ⟨i.val, lt_of_lt_of_le i.isLt le_rfl⟩) id).mulVecLin) = _
  rw [Pivot1.full_range L e le_rfl, Pivot1.saturation_eq_self _ (Pivot1.map_saturated L e)]

theorem full_height1 : (pre L e hn hpiv n hn le_rfl).primitive.H = L.H := by
  have h := Algebra.Prefix.prefix_height (pre L e hn hpiv n hn le_rfl)
  unfold PrefixHeight at h
  rw [full_divisor1, one_mul] at h
  exact h

theorem full_mass1 (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) :
    (pre L e hn hpiv n hn le_rfl).primitive.mZ ((pre L e hn hpiv n hn le_rfl).grids G) =
      L.mZ G := by
  rw [Algebra.Prefix.primitive_mass_eq ((pre L e hn hpiv n hn le_rfl).grids G)
    (fun i => hG ((pre L e hn hpiv n hn le_rfl).coord i)) (pre L e hn hpiv n hn le_rfl).matrix
    (pre L e hn hpiv n hn le_rfl).primitive (pre L e hn hpiv n hn le_rfl).primitive_eq]
  have hcomp : imageZ ((pre L e hn hpiv n hn le_rfl).grids G)
      (pre L e hn hpiv n hn le_rfl).matrix =
      imageZ G L.matrix ∘ (Equiv.piCongrLeft (fun i : Fin n => Fin (G i)) e) := by
    funext r j
    simp only [imageZ]
    refine Fintype.sum_equiv e _ _ (fun i => ?_)
    have hr : (((Equiv.piCongrLeft (fun i : Fin n => Fin (G i)) e) r (e i) : Fin (G (e i))) :
        ℕ) = ((r i : Fin (G (e i))) : ℕ) :=
      congrArg Fin.val (Equiv.piCongrLeft_apply_apply (P := fun i : Fin n => Fin (G i)) e
        (r : ∀ a, Fin (G (e a))) i)
    change L.matrix (e ⟨i.val, _⟩) j * ((r i : ℕ) : ℤ) = _
    rw [hr]
  calc mass ((pre L e hn hpiv n hn le_rfl).grids G) (imageZ ((pre L e hn hpiv n hn le_rfl).grids G)
        (pre L e hn hpiv n hn le_rfl).matrix)
      = Algebra.FiniteProbability.atomMass (imageZ G L.matrix ∘
          (Equiv.piCongrLeft (fun i : Fin n => Fin (G i)) e)) :=
        congrArg (mass ((pre L e hn hpiv n hn le_rfl).grids G)) hcomp
    _ = Algebra.FiniteProbability.atomMass (imageZ G L.matrix) :=
        Algebra.Prefix.mass_precomp_equiv
          (Equiv.piCongrLeft (fun i : Fin n => Fin (G i)) e) (imageZ G L.matrix)
    _ = L.mZ G := rfl

noncomputable def pivotStep1 (G : Fin n → ℕ) (hG : ∀ i, 0 < G i)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) : PivotFirstStep 1 n k where
  old := pre L e hn hpiv k hk (by omega)
  next := pre L e hn hpiv (k+1) (by omega) hkn
  same_original := (Pivot1.pivotPrefix_original L e hn hpiv _ (k+1) (by omega) hkn).trans
    (Pivot1.pivotPrefix_original L e hn hpiv _ k hk (by omega)).symm
  same_order := (Pivot1.pivotPrefix_order L e hn hpiv _ (k+1) (by omega) hkn).trans
    (Pivot1.pivotPrefix_order L e hn hpiv _ k hk (by omega)).symm
  grids := G
  grids_pos := hG
  residueOrder := addOrderOf (QuotientAddGroup.mk' (pre L e hn hpiv k hk (by omega)).rows
    (L.matrix (e ⟨k, by omega⟩)))
  quotient_order := rfl

end Construction

theorem exists_pivot_order1 (L : IntLat (Fin n) 1) :
    ∃ (hn : 1 ≤ n) (e : Equiv.Perm (Fin n)), (L.matrix (e ⟨0, hn⟩) 0).natAbs = L.H := by
  obtain ⟨i0, -⟩ := Pivot1.exists_nonzero_entry L
  have hn : 1 ≤ n := by
    have := i0.isLt
    omega
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image (univ : Finset (Fin n))
    (fun i => (L.matrix i 0).natAbs) ⟨⟨0, hn⟩, mem_univ _⟩
  refine ⟨hn, Equiv.swap ⟨0, hn⟩ j0, ?_⟩
  apply Pivot1.height_eq_max L _
  intro i
  rw [Equiv.swap_apply_left]
  exact hj0 i (mem_univ _)

structure RankOnePresentation (L : IntLat (Fin n) 1) where
  lower : 1 ≤ n
  order : Equiv.Perm (Fin n)
  maximal : (L.matrix (order ⟨0, lower⟩) 0).natAbs = L.H

noncomputable def rankOnePresentation (L : IntLat (Fin n) 1) : RankOnePresentation L :=
  let h := exists_pivot_order1 L
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

namespace RankOnePresentation

variable {L : IntLat (Fin n) 1} (R : RankOnePresentation L)

noncomputable def prefixes (k : Fin (n - 1 + 1)) : PivotFirstPrefix 1 n (k.val + 1) :=
  pre L R.order R.lower R.maximal (k.val + 1) (by omega)
    (by have := k.isLt; have := R.lower; omega)

noncomputable def lattices (k : Fin (n - 1 + 1)) : IntLat (Fin (k.val + 1)) 1 :=
  (R.prefixes k).primitive

noncomputable def grids (G : Fin n → ℕ) (k : Fin (n - 1 + 1)) : Fin (k.val + 1) → ℕ :=
  (R.prefixes k).grids G

noncomputable def step (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) (k : Fin (n - 1)) :
    PivotFirstStep 1 n (k.val + 1) :=
  pivotStep1 L R.order R.lower R.maximal G hG (k.val + 1) (by omega)
    (by have := k.isLt; have := R.lower; omega)

theorem budget (Q : VITData) (G : Fin n → ℕ) (hG : GridBudget Q G)
    (k : Fin (n - 1 + 1)) : GridBudget Q (R.grids G k) :=
  Pivot1.budget_comp Q G (R.prefixes k).coord (Pivot1.coord_injective _) hG

theorem first (P : VITParameters) (G : Fin n → ℕ) (hG : GridBudget P.toVITData G) :
    (R.lattices 0).H = 1 ∧ (R.lattices 0).mZ (R.grids G 0) ≤ 1 / (P.g : ℝ) := by
  refine ⟨Pivot1.unit_height _, ?_⟩
  simpa only [pow_one] using Algebra.Reg.mass_le_pivot (R.grids G 0) (R.lattices 0)
    (Algebra.Reg.grid_lower_pos P) (R.budget P.toVITData G hG 0).1

theorem hmono (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) (k : Fin (n - 1)) :
    (R.lattices k.succ).mZ (R.grids G k.succ) ≤
      (R.lattices k.castSucc).mZ (R.grids G k.castSucc) :=
  (Step1.step_identities1 (R.step G hG k)).2.2

theorem last_height : (R.lattices (Fin.last (n - 1))).H = L.H := by
  have hh (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (he : k = n) :
      (pre L R.order R.lower R.maximal k hk hkn).primitive.H = L.H := by
    subst k
    exact full_height1 L R.order R.lower R.maximal
  exact hh _ _ _ (Nat.sub_add_cancel R.lower)

theorem last_mass (G : Fin n → ℕ) (hG : ∀ i, 0 < G i) :
    (R.lattices (Fin.last (n - 1))).mZ (R.grids G (Fin.last (n - 1))) = L.mZ G := by
  have hh (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (he : k = n) :
      (pre L R.order R.lower R.maximal k hk hkn).primitive.mZ
        ((pre L R.order R.lower R.maximal k hk hkn).grids G) = L.mZ G := by
    subst k
    exact full_mass1 L R.order R.lower R.maximal G hG
  exact hh _ _ _ (Nat.sub_add_cancel R.lower)

def lastOrder : Fin (n - 1 + 1) ≃ Fin n :=
  (finCongr (Nat.sub_add_cancel R.lower)).trans R.order

theorem last_carrier : (R.lattices (Fin.last (n - 1))).carrier =
    L.carrier.map (Pivot2.coordinateMap R.lastOrder) := by
  have hh (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (he : k = n) :
      (pre L R.order R.lower R.maximal k hk hkn).primitive.carrier =
        L.carrier.map (Pivot2.coordinateMap ((finCongr he).trans R.order)) := by
    subst k
    rw [full_carrier1]
    rfl
  exact hh _ _ _ (Nat.sub_add_cancel R.lower)

theorem domain (P : VITParameters) (G : Fin n → ℕ) (hG : ∀ i, 0 < G i)
    (hm : P.theta0 - 20 * P.eps ≤ L.mZ G) :
    ∀ j, P.theta0 - 20 * P.eps ≤ (R.lattices j).mZ (R.grids G j) := by
  have ha : Antitone (fun j => (R.lattices j).mZ (R.grids G j)) :=
    Fin.antitone_iff_succ_le.mpr (R.hmono G hG)
  intro j
  exact hm.trans ((R.last_mass G hG).symm.le.trans (ha (Fin.le_last j)))

theorem exists_presentation_events1 (P : VITParameters) (G : Fin n → ℕ)
    (hG : GridBudget P.toVITData G) (hpos : ∀ i, 0 < G i)
    (hm : P.theta0 - 20 * P.eps ≤ L.mZ G) :
    ∃ C : (j : Fin (n - 1 + 1)) → Step1.Geometry.CurrentEvent1 P (R.grids G j) (R.lattices j),
      ∀ j : Fin (n - 1),
        ordinaryNormals (R.grids G j.succ) (C j.succ).event = (R.lattices j.succ).carrier →
        ordinaryNormals (R.grids G j.castSucc) (C j.castSucc).event ≠
          (R.lattices j.castSucc).carrier →
        Step1.DescentGeometry1 P (R.step G hpos j) 2 ∨
          Step1.DescentGeometry1 P (R.step G hpos j) 3 := by
  apply Algebra.Reg.Step2.Geometry.exists_dependent_chain
    (fun j => Step1.Geometry.CurrentEvent1 P (R.grids G j) (R.lattices j))
    (fun j old new =>
      ordinaryNormals (R.grids G j.succ) new.event = (R.lattices j.succ).carrier →
      ordinaryNormals (R.grids G j.castSucc) old.event ≠ (R.lattices j.castSucc).carrier →
      Step1.DescentGeometry1 P (R.step G hpos j) 2 ∨
        Step1.DescentGeometry1 P (R.step G hpos j) 3)
  · exact Step1.Geometry.exists_current_event1 P _ _
      (fun i => hpos ((R.prefixes 0).coord i))
  · intro j C
    exact Step1.Geometry.exists_next_event1 P (R.step G hpos j)
      (R.budget P.toVITData G hG j.castSucc) (R.budget P.toVITData G hG j.succ)
      (R.domain P G hpos hm j.castSucc) (R.domain P G hpos hm j.succ) C

end RankOnePresentation

theorem regularize1_fin (P : VITParameters) (G : Fin n → ℕ) (L : IntLat (Fin n) 1)
    (R : RankOnePresentation L) (hG : GridBudget P.toVITData G)
    (hm : P.theta0 - 20 * P.eps ≤ L.mZ G) :
    Regularize1 P (R.grids G (Fin.last (n - 1))) (R.lattices (Fin.last (n - 1))) := by
  have hpos : ∀ i, 0 < G i := fun i => lt_of_lt_of_le (Algebra.Reg.grid_lower_pos P) (hG.1 i)
  obtain ⟨C, hC⟩ := R.exists_presentation_events1 P G hG hpos hm
  refine Algebra.Reg.Regularize1.regularize1_of_prefix_recurrence_closed P (R.grids G) R.lattices
    (fun j => (C j).event) (C (Fin.last (n - 1))).target (C (Fin.last (n - 1))).maximal
    (C (Fin.last (n - 1))).subset_fibre (C (Fin.last (n - 1))).retained
    (fun _ => R.first P G hG) ?_
  intro j hn
  exact Step1.step_recurrence1 P (R.step G hpos j) (R.budget P.toVITData G hG j.castSucc)
    (P.g_lower.trans (hG.1 _)) (R.domain P G hpos hm j.succ)
    (C j.castSucc).event (C j.succ).event (C j.succ).target (C j.succ).subset_fibre
    (C j.succ).retained (fun ho => hC j hn ho) hn

theorem last_grids {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → ℕ) (L : IntLat ι 1)
    (R : RankOnePresentation (Pivot2.transport L (Fintype.equivFin ι).symm)) :
    R.grids (G ∘ (Fintype.equivFin ι).symm) (Fin.last (Fintype.card ι - 1)) ∘
        (R.lastOrder.trans (Fintype.equivFin ι).symm).symm = G := by
  funext x
  have hx : ∀ i, R.grids (G ∘ (Fintype.equivFin ι).symm) (Fin.last (Fintype.card ι - 1)) i =
      G ((R.lastOrder.trans (Fintype.equivFin ι).symm) i) := fun _ => rfl
  simp only [Function.comp_apply, hx, Equiv.apply_symm_apply]

theorem last_transport {ι : Type*} [Fintype ι] (L : IntLat ι 1)
    (c : Fin (Fintype.card ι) ≃ ι) (R : RankOnePresentation (Pivot2.transport L c)) :
    (R.lattices (Fin.last (Fintype.card ι - 1))).carrier =
      L.carrier.map (Pivot2.coordinateMap (R.lastOrder.trans c)) := by
  rw [R.last_carrier]
  change (L.carrier.map (Pivot2.coordinateMap c)).map (Pivot2.coordinateMap R.lastOrder) = _
  rw [← Submodule.map_comp]
  rfl

theorem regularize1 (P : VITParameters) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ℕ) (L : IntLat ι 1) : Regularize1 P G L := by
  intro hG hm
  let c : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let G' : Fin (Fintype.card ι) → ℕ := G ∘ c
  have hG' : GridBudget P.toVITData G' :=
    Pivot2.budget_comp P.toVITData G c c.injective hG
  have hpos : ∀ i, 0 < G' i := fun i =>
    lt_of_lt_of_le (Algebra.Reg.grid_lower_pos P) (hG.1 (c i))
  have hmass' : (Pivot2.transport L c).mZ G' = L.mZ G := Pivot2.transport_mass L c G
  have hm' : P.theta0 - 20 * P.eps ≤ (Pivot2.transport L c).mZ G' := by
    rw [hmass']; exact hm
  let R := rankOnePresentation (Pivot2.transport L c)
  let N := Fintype.card ι - 1
  have hkey := regularize1_fin P G' (Pivot2.transport L c) R hG' hm'
  have hlast_mass : (R.lattices (Fin.last N)).mZ (R.grids G' (Fin.last N)) = L.mZ G :=
    (R.last_mass G' hpos).trans hmass'
  have hlast_H : (R.lattices (Fin.last N)).H = L.H :=
    R.last_height.trans (Pivot2.transport_height L c)
  have hmN : P.theta0 - 20 * P.eps ≤
      (R.lattices (Fin.last N)).mZ (R.grids G' (Fin.last N)) := by
    rw [hlast_mass]; exact hm
  let e : Fin (N + 1) ≃ ι := R.lastOrder.trans c
  have hGe : R.grids G' (Fin.last N) ∘ e.symm = G := last_grids G L R
  have hcontain : ∀ {d : ℕ} (M : IntLat (Fin (N + 1)) d),
      (R.lattices (Fin.last N)).carrier ≤ M.carrier →
      L.carrier ≤ (Pivot2.transport M e.symm).carrier := by
    intro d M hle x hx
    have hy : x ∘ e ∈ (R.lattices (Fin.last N)).carrier := by
      rw [last_transport L c R]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    refine Submodule.mem_map.mpr ⟨x ∘ e, hle hy, ?_⟩
    funext i
    change x (e (e.symm i)) = x i
    rw [Equiv.apply_symm_apply]
  have hmassT : ∀ {d : ℕ} (M : IntLat (Fin (N + 1)) d),
      (Pivot2.transport M e.symm).mZ G = M.mZ (R.grids G' (Fin.last N)) := by
    intro d M
    have h := Pivot2.transport_mass M e.symm (R.grids G' (Fin.last N))
    rw [hGe] at h
    exact h
  rcases hkey (R.budget P.toVITData G' hG' (Fin.last N)) hmN with
      hreg | ⟨L2, hle, hL2m, hL2r⟩ | ⟨L3, hle, hL3m, hL3H, hL3r⟩
  · left
    unfold Regular at hreg ⊢
    rw [hlast_mass, hlast_H] at hreg
    exact hreg
  · right; left
    refine ⟨Pivot2.transport L2 e.symm, hcontain L2 hle, ?_, ?_⟩
    · rw [hmassT, ← hlast_mass]
      exact hL2m
    · unfold Regular at hL2r ⊢
      rw [hmassT, Pivot2.transport_height L2 e.symm]
      exact hL2r
  · right; right
    refine ⟨Pivot2.transport L3 e.symm, hcontain L3 hle, ?_, ?_, ?_⟩
    · rw [hmassT, ← hlast_mass]
      exact hL3m
    · rw [Pivot2.transport_height]
      exact hL3H
    · unfold Regular at hL3r ⊢
      rw [hmassT, Pivot2.transport_height L3 e.symm]
      exact hL3r

end Algebra.Reg.Assemble1

end Praxis.Lift
