import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Record
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.DifferenceLattice.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Promote2

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem mem_normals_of_constant {G : ι → ℕ} {F : Finset (Grid G)}
    (w : ι → ℤ) (a : ℤ)
    (hw : ∀ r ∈ F, (∑ i, w i * ((r i : ℕ) : ℤ)) = a) :
    w ∈ ordinaryNormals G F := by
  let f : (ι → ℤ) →ₗ[ℤ] ℤ := {
    toFun := fun v => ∑ i, w i * v i
    map_add' := by intro v v'; simp [mul_add, sum_add_distrib]
    map_smul' := by
      intro c v
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
      apply sum_congr rfl
      intro i _
      ring }
  have hker : Algebra.DifferenceLattice.differenceLattice 0 F ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro v ⟨r, hr, s, hs, rfl⟩
    change (∑ i, w i * (Algebra.DifferenceLattice.ival 0 r - Algebra.DifferenceLattice.ival 0 s) i) = 0
    simp only [Pi.sub_apply, Algebra.DifferenceLattice.ival, Pi.zero_apply, zero_add,
      mul_sub, sum_sub_distrib, hw r hr, hw s hs, sub_self]
  exact fun v hv => hker hv

omit [DecidableEq ι] in

theorem normal_constant {G : ι → ℕ} {F : Finset (Grid G)}
    {w : ι → ℤ} (hw : w ∈ ordinaryNormals G F)
    {r s : Grid G} (hr : r ∈ F) (hs : s ∈ F) :
    (∑ i, w i * ((r i : ℕ) : ℤ)) = ∑ i, w i * ((s i : ℕ) : ℤ) := by
  have hd : Algebra.DifferenceLattice.ival 0 r - Algebra.DifferenceLattice.ival 0 s ∈
      Algebra.DifferenceLattice.differenceLattice 0 F :=
    Submodule.subset_span ⟨r, hr, s, hs, rfl⟩
  have h := hw _ hd
  apply sub_eq_zero.mp
  simpa only [Pi.sub_apply, Algebra.DifferenceLattice.ival, Pi.zero_apply, zero_add,
    mul_sub, sum_sub_distrib] using h

theorem carrier_le_of_basis_mem {d : ℕ} (L : IntLat ι d)
    (N : Submodule ℤ (ι → ℤ)) (hb : ∀ j, (L.basis j : ι → ℤ) ∈ N) :
    L.carrier ≤ N := by
  intro w hw
  have he : ∑ j, L.basis.equivFun ⟨w, hw⟩ j • (L.basis j : ι → ℤ) = w := by
    ext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
      Algebra.Lattice.basis_eval L.carrier L.basis ⟨w, hw⟩ i
  rw [← he]
  exact N.sum_mem fun j _ => N.smul_mem _ (hb j)

theorem carrier_le_normals {G : ι → ℕ} {d : ℕ} (L : IntLat ι d)
    (t : Fin d → ℤ) (F : Finset (Grid G))
    (hF : F ⊆ ordinaryFibre G L t) : L.carrier ≤ ordinaryNormals G F := by
  apply carrier_le_of_basis_mem L
  intro j
  apply mem_normals_of_constant _ (t j)
  intro r hr
  have h := (mem_filter.mp (hF hr)).2
  exact congrFun h j

theorem density_le_mass {G : ι → ℕ} {d : ℕ} (L : IntLat ι d)
    (F : Finset (Grid G)) (hF : F.Nonempty)
    (hL : L.carrier ≤ ordinaryNormals G F) : density G F ≤ L.mZ G := by
  classical
  obtain ⟨r, hr⟩ := hF
  have hc : F.card ≤ Algebra.FiniteProbability.fibreCount (imageZ G L.matrix)
      (imageZ G L.matrix r) := by
    apply card_le_card
    intro s hs
    simp only [mem_filter, mem_univ, true_and]
    funext j
    exact normal_constant (hL (L.basis j).property) hs hr
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (Nat.cast_nonneg _)).trans
      (Algebra.FiniteProbability.pointProb_le_mass (imageZ G L.matrix) (imageZ G L.matrix r))

omit [DecidableEq ι] in

theorem independent_extension (L : IntLat ι 2) (w : ι → ℤ)
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

theorem extend_in_normals {G : ι → ℕ} (L : IntLat ι 2)
    (F : Finset (Grid G)) (hL : L.carrier ≤ ordinaryNormals G F)
    (w : ι → ℤ) (hw : w ∈ ordinaryNormals G F) (hind : w ∉ L.carrier) :
    ∃ L3 : IntLat ι 3, L.carrier ≤ L3.carrier ∧
      L3.carrier ≤ ordinaryNormals G F := by
  let v : Fin 3 → (ι → ℤ) := Fin.cons w (fun j => (L.basis j : ι → ℤ))
  have hv : LinearIndependent ℤ v := independent_extension L w hind
  let S := Submodule.span ℤ (Set.range v)
  let N := Algebra.Lattice.saturation S
  have hr : Module.finrank ℤ N = 3 := by
    rw [Algebra.Lattice.finrank_saturation]
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (Basis.span hv)
  let L3 : IntLat ι 3 :=
    ⟨N, Module.finBasisOfFinrankEq ℤ N hr, Algebra.Lattice.saturation_isSaturated S⟩
  refine ⟨L3, ?_, ?_⟩
  · apply carrier_le_of_basis_mem L
    intro j
    apply Algebra.Lattice.le_saturation S
    exact Submodule.subset_span ⟨j.succ, rfl⟩
  · have hS : S ≤ ordinaryNormals G F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Fin.cases hw (fun j => hL (L.basis j).property) j
    rintro x ⟨c, hc, hx⟩
    exact Algebra.VectorInverse.normalLattice_saturated _ c hc x (hS hx)

theorem rank2_promotion (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 2)
    (t : Fin 2 → ℤ) (F : Finset (Grid G))
    (hheight : ∀ L3 : IntLat ι 3, Rank3Height P G L3) :
    Rank2Promotion P G L t F := by
  intro hbudget _hmax hnonempty hsubset hloss hheavy htrigger
  have hL : L.carrier ≤ ordinaryNormals G F := carrier_le_normals L t F hsubset
  have hout : ∃ L3 : IntLat ι 3, L.carrier ≤ L3.carrier ∧
      L3.carrier ≤ ordinaryNormals G F := by
    rcases htrigger with hrank | ⟨i, a, hfixed, hind⟩
    · exact ⟨⟨ordinaryNormals G F,
        Module.finBasisOfFinrankEq ℤ (ordinaryNormals G F) hrank,
        Algebra.VectorInverse.normalLattice_saturated _⟩, hL, le_rfl⟩
    · apply extend_in_normals L F hL (Pi.single i 1) _ hind
      apply mem_normals_of_constant _ a
      intro r hr
      simpa [Pi.single_apply] using hfixed r hr
  obtain ⟨L3, hcontain, hnormal⟩ := hout
  have hmass : density G F ≤ L3.mZ G := density_le_mass L3 F hnonempty hnormal
  obtain ⟨hH, hregular⟩ := hheight L3 hbudget (hheavy.trans hmass)
  exact ⟨L3, hcontain, hloss.trans hmass, hH, hregular⟩

end Algebra.Reg.Promote2

end Praxis.Lift
