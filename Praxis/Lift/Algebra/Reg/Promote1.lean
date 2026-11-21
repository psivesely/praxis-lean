import Praxis.Lift.Algebra.Reg.Rank1Model
import Praxis.Lift.Algebra.Reg.Promote2
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Reg.Rank1Model
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Promote1

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Lift.Algebra.Reg.Rank1Model

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Algebra.Reg.Rank1Model hiding Rank1Promotion Rank1Return21 Rank1Return31 Rank1NestedCall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem independent_extension1 (L : IntLat ι 1) (w : ι → ℤ)
    (hw : w ∉ L.carrier) :
    LinearIndependent ℤ (Fin.cons w (fun j => (L.basis j : ι → ℤ))) := by
  apply LinearIndependent.finCons' w _
    (L.basis.linearIndependent.map' L.carrier.subtype (by simp))
  intro c y hy hzero
  by_contra hc
  apply hw
  apply L.saturated c hc w
  have hyL : y ∈ L.carrier := by
    apply (Submodule.span_le.mpr ?_ :
      Submodule.span ℤ (Set.range (fun j => (L.basis j : ι → ℤ))) ≤ L.carrier) hy
    rintro _ ⟨j, rfl⟩
    exact (L.basis j).property
  have he : c • w = -y := eq_neg_of_add_eq_zero_left hzero
  rw [he]
  exact L.carrier.neg_mem hyL

theorem extend_in_normals1 {G : ι → ℕ} (L : IntLat ι 1)
    (F : Finset (Grid G)) (hL : L.carrier ≤ ordinaryNormals G F)
    (w : ι → ℤ) (hw : w ∈ ordinaryNormals G F) (hind : w ∉ L.carrier) :
    ∃ L2 : IntLat ι 2, L.carrier ≤ L2.carrier ∧
      L2.carrier ≤ ordinaryNormals G F := by
  let v : Fin 2 → (ι → ℤ) := Fin.cons w (fun j => (L.basis j : ι → ℤ))
  have hv : LinearIndependent ℤ v := independent_extension1 L w hind
  let S := Submodule.span ℤ (Set.range v)
  let N := Algebra.Lattice.saturation S
  have hr : Module.finrank ℤ N = 2 := by
    rw [Algebra.Lattice.finrank_saturation]
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (Basis.span hv)
  let L2 : IntLat ι 2 :=
    ⟨N, Module.finBasisOfFinrankEq ℤ N hr, Algebra.Lattice.saturation_isSaturated S⟩
  refine ⟨L2, ?_, ?_⟩
  · apply Promote2.carrier_le_of_basis_mem L
    intro j
    apply Algebra.Lattice.le_saturation S
    exact Submodule.subset_span ⟨j.succ, rfl⟩
  · have hS : S ≤ ordinaryNormals G F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Fin.cases hw (fun j => hL (L.basis j).property) j
    rintro x ⟨c, hc, hx⟩
    exact Algebra.VectorInverse.normalLattice_saturated _ c hc x (hS hx)

noncomputable def normalLattice {G : ι → ℕ} (F : Finset (Grid G)) {e : ℕ}
    (he : Module.finrank ℤ (ordinaryNormals G F) = e) : IntLat ι e :=
  ⟨ordinaryNormals G F, Module.finBasisOfFinrankEq ℤ _ he,
    Algebra.VectorInverse.normalLattice_saturated _⟩

theorem rank1_promotion (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 1)
    (t : Fin 1 → ℤ) (F : Finset (Grid G))
    (hheight : ∀ L3 : IntLat ι 3, Rank3Height P G L3) :
    Rank1Promotion P G L t F := by
  intro hbudget _hmax hnonempty hsubset hloss hheavy htrigger
  have hL : L.carrier ≤ ordinaryNormals G F := Promote2.carrier_le_normals L t F hsubset
  rcases htrigger with h2 | h3 | ⟨i, a, hfixed, hind⟩
  · left
    exact ⟨normalLattice F h2, hL,
      hloss.trans (Promote2.density_le_mass (normalLattice F h2) F hnonempty le_rfl)⟩
  · right
    have hmass := Promote2.density_le_mass (normalLattice F h3) F hnonempty le_rfl
    obtain ⟨hH, hreg⟩ := hheight (normalLattice F h3) hbudget (hheavy.trans hmass)
    exact ⟨normalLattice F h3, hL, hloss.trans hmass, hH, hreg⟩
  · left
    have hu : (Pi.single i 1 : ι → ℤ) ∈ ordinaryNormals G F := by
      apply Promote2.mem_normals_of_constant _ a
      intro r hr
      simpa [Pi.single_apply] using hfixed r hr
    obtain ⟨L2, hc, hn⟩ := extend_in_normals1 L F hL (Pi.single i 1) hu hind
    exact ⟨L2, hc, hloss.trans (Promote2.density_le_mass L2 F hnonempty hn)⟩

end Algebra.Reg.Promote1

end Praxis.Lift
