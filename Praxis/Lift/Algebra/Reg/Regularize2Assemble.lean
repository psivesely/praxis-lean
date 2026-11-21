import Praxis.Lift.Algebra.Reg.Step2Actual
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Reg.Pivot2
import Praxis.Lift.Algebra.Reg.Promote2
import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Algebra.Reg.Step2Geometry
import Praxis.Lift.Algebra.Trans.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Assemble2

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

theorem last_grids {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → ℕ) (L : IntLat ι 2)
    (R : Pivot2.Presentation (Pivot2.transport L (Fintype.equivFin ι).symm)) :
    R.grids (G ∘ (Fintype.equivFin ι).symm) (Fin.last (Fintype.card ι - 2)) ∘
        (R.lastOrder.trans (Fintype.equivFin ι).symm).symm = G := by
  funext x
  have hx : ∀ i, R.grids (G ∘ (Fintype.equivFin ι).symm) (Fin.last (Fintype.card ι - 2)) i =
      G ((R.lastOrder.trans (Fintype.equivFin ι).symm) i) := fun _ => rfl
  simp only [Function.comp_apply, hx, Equiv.apply_symm_apply]

theorem regularize2 (P : VITParameters) (hT : Algebra.Trans.Transition32 P)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → ℕ) (L : IntLat ι 2) :
    Regularize2 P G L := by
  intro hG hm
  let c : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let G' : Fin (Fintype.card ι) → ℕ := G ∘ c
  have hG' : GridBudget P.toVITData G' :=
    Pivot2.budget_comp P.toVITData G c c.injective hG
  have hpos : ∀ i, 0 < G' i := fun i =>
    lt_of_lt_of_le (Algebra.Reg.grid_lower_pos P) (hG.1 (c i))
  have hmass' : (Pivot2.transport L c).mZ G' = L.mZ G := Pivot2.transport_mass L c G
  have hm' : P.theta0 - 30 * P.eps ≤ (Pivot2.transport L c).mZ G' := by
    rw [hmass']; exact hm
  let R := Pivot2.presentation (Pivot2.transport L c)
  let C := Step2.Actual.events R P G' hG' hpos hm'
  let N := Fintype.card ι - 2
  have hkey : Regularize2 P (R.grids G' (Fin.last N)) (R.lattices (Fin.last N)) :=
    regularize2_of_normal_prefix_recurrence P (R.grids G') R.lattices
      (fun j => (C j).event) (C (Fin.last N)).target
      (Promote2.rank2_promotion P _ _ _ _ (fun L3 => Step2.Actual.rank3 P _ L3))
      (C (Fin.last N)).maximal (C (Fin.last N)).subset_fibre (C (Fin.last N)).retained
      (R.hfirst P G' hG' (fun j => (C j).event))
      (Step2.Actual.hstep_actual_of_transition R P G' hG' hpos hm' hT)
  have hlast_mass : (R.lattices (Fin.last N)).mZ (R.grids G' (Fin.last N)) = L.mZ G :=
    (R.last_mass G' hpos).trans hmass'
  have hlast_H : (R.lattices (Fin.last N)).H = L.H :=
    R.last_height.trans (Pivot2.transport_height L c)
  have hmN : P.theta0 - 30 * P.eps ≤
      (R.lattices (Fin.last N)).mZ (R.grids G' (Fin.last N)) := by
    rw [hlast_mass]; exact hm
  rcases hkey (R.budget P.toVITData G' hG' (Fin.last N)) hmN with hreg | ⟨L3, hle, hL3m, hL3H, hL3r⟩
  · left
    unfold Regular at hreg ⊢
    rw [hlast_mass, hlast_H] at hreg
    exact hreg
  · right
    let e : Fin (N + 2) ≃ ι := R.lastOrder.trans c
    have hGe : R.grids G' (Fin.last N) ∘ e.symm = G := last_grids G L R
    have hmass3 : (Pivot2.transport L3 e.symm).mZ G = L3.mZ (R.grids G' (Fin.last N)) := by
      have h := Pivot2.transport_mass L3 e.symm (R.grids G' (Fin.last N))
      rw [hGe] at h
      exact h
    have hH3 : (Pivot2.transport L3 e.symm).H = L3.H := Pivot2.transport_height L3 e.symm
    refine ⟨Pivot2.transport L3 e.symm, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hy : x ∘ e ∈ (R.lattices (Fin.last N)).carrier := by
        rw [Pivot2.last_transport L c R]
        exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      refine Submodule.mem_map.mpr ⟨x ∘ e, hle hy, ?_⟩
      funext i
      change x (e (e.symm i)) = x i
      rw [Equiv.apply_symm_apply]
    · rw [hmass3, ← hlast_mass]
      exact hL3m
    · rw [hH3]
      exact hL3H
    · unfold Regular at hL3r ⊢
      rw [hmass3, hH3]
      exact hL3r

end Algebra.Reg.Assemble2

end Praxis.Lift
