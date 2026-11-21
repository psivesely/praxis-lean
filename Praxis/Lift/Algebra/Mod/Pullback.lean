import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Algebra.Sat.Definitions
import Praxis.Algebra.InverseBranches.NormalRank
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

noncomputable section

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.Pullback

open Praxis.Algebra Praxis.Algebra.Mod

open Finset Module Matrix

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions Praxis.Algebra.VectorInverse

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem step_evaluation_surjective {d : ℕ} (L : IntLat ι d) :
    Function.Surjective (stepMatrix L.matrix).transpose.mulVecLin := by
  intro y
  obtain ⟨x, hx⟩ := basis_evaluation_surjective L.carrier L.saturated L.basis
    (fun j => y (some j))
  refine ⟨extend x (y none), ?_⟩
  ext j
  change (∑ i, stepMatrix L.matrix i j * extend x (y none) i) = y j
  cases j with
  | none => simp [stepMatrix, extend, Fintype.sum_option]
  | some j =>
    have hh := congrFun hx j
    change (∑ i, (L.basis j : ι → ℤ) i * x i) = y (some j) at hh
    simpa [IntLat.matrix, stepMatrix, extend, Fintype.sum_option] using hh

theorem step_left_inverse {d : ℕ} (L : IntLat ι d) :
    ∃ C : Matrix (Option (Fin d)) (Option ι) ℤ, C * stepMatrix L.matrix = 1 := by
  let A := stepMatrix L.matrix
  obtain ⟨s, hs⟩ := (Module.Projective.iff_split_of_projective
    A.transpose.mulVecLin (step_evaluation_surjective L)).mp
    (inferInstance : Module.Projective ℤ (Option (Fin d) → ℤ))
  refine ⟨(LinearMap.toMatrix' s).transpose, ?_⟩
  have hm := congrArg LinearMap.toMatrix' hs
  change LinearMap.toMatrix' ((Matrix.toLin' A.transpose).comp s) = _ at hm
  have hprod : A.transpose * LinearMap.toMatrix' s = 1 := by
    simpa only [LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hm
  have ht := congrArg Matrix.transpose hprod
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using ht

omit [DecidableEq ι] [DecidableEq κ] in

theorem dot_mulVec (A : Matrix ι κ ℤ) (u : κ → ℤ) (x : ι → ℤ) :
    dotProduct (A *ᵥ u) x = dotProduct u (A.transpose *ᵥ x) := by
  exact (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec A u x).symm

theorem map_normal_eq (A : Matrix ι κ ℤ) (C : Matrix κ ι ℤ)
    (hCA : C * A = 1) (E : Submodule ℤ (κ → ℤ)) :
    (normalLattice E).map A.mulVecLin = normalLattice (E.comap A.transpose.mulVecLin) := by
  have hsplit (y : κ → ℤ) : A.transpose *ᵥ (C.transpose *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hCA, Matrix.transpose_one,
      Matrix.one_mulVec]
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩ x hx
    exact (dot_mulVec A u x).trans (hu _ hx)
  · intro w hw
    have hu : C *ᵥ w ∈ normalLattice E := by
      intro y hy
      change dotProduct (C *ᵥ w) y = 0
      rw [dot_mulVec C]
      exact hw _ (by change A.transpose *ᵥ (C.transpose *ᵥ y) ∈ E; rwa [hsplit])
    refine ⟨C *ᵥ w, hu, ?_⟩
    change A *ᵥ (C *ᵥ w) = w
    have hrecon (x : ι → ℤ) : dotProduct w x = dotProduct w (C.transpose *ᵥ (A.transpose *ᵥ x)) := by
      have hx : x - C.transpose *ᵥ (A.transpose *ᵥ x) ∈ E.comap A.transpose.mulVecLin := by
        change A.transpose *ᵥ (x - C.transpose *ᵥ (A.transpose *ᵥ x)) ∈ E
        rw [Matrix.mulVec_sub, hsplit, sub_self]
        exact E.zero_mem
      have hh := hw _ hx
      change dotProduct w (x - C.transpose *ᵥ (A.transpose *ᵥ x)) = 0 at hh
      rw [dotProduct_sub] at hh
      exact sub_eq_zero.mp hh
    ext i
    have hh := hrecon (Pi.single i 1)
    rw [← dot_mulVec C, ← dot_mulVec A] at hh
    simpa using hh.symm

omit [DecidableEq ι] in

theorem pull_redSpan {d p : ℕ} (L : IntLat ι d)
    (E : Submodule ℤ (Option (Fin d) → ℤ)) (c : Option (Fin d) → ZMod p)
    (hc : c ∈ Algebra.Sat.redSpan p E) :
    pullMod L.matrix c ∈ Algebra.Sat.redSpan p (E.map (stepMatrix L.matrix).mulVecLin) := by
  let f := ((stepMatrix L.matrix).map (Int.castRingHom (ZMod p))).mulVecLin
  have hle : Algebra.Sat.redSpan p E ≤
      (Algebra.Sat.redSpan p (E.map (stepMatrix L.matrix).mulVecLin)).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    apply Submodule.subset_span
    refine ⟨(stepMatrix L.matrix) *ᵥ w, ⟨w, hw, rfl⟩, ?_⟩
    ext i
    simp [f, Algebra.Sat.redVec, Matrix.mulVec, dotProduct]
  exact hle hc

theorem modPullback {d p : ℕ} (L : IntLat ι d)
    (E : Submodule ℤ (Option (Fin d) → ℤ)) (c : Option (Fin d) → ZMod p)
    (hAnn : Algebra.Sat.SatAnnihilatorEq (Option (Fin d))) : ModPullback L E c := by
  intro hp hE hc
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hC⟩ := step_left_inverse L
  let M := (normalLattice E).map (stepMatrix L.matrix).mulVecLin
  have hM : M = normalLattice (E.comap (stepMatrix L.matrix).transpose.mulVecLin) :=
    map_normal_eq _ C hC E
  have hsat : Algebra.Lattice.IsSaturated M := by
    rw [hM]
    exact normalLattice_saturated _
  obtain ⟨q, b⟩ := M.basisOfPid (Pi.basisFun ℤ (Option ι))
  let N : IntLat (Option ι) q := ⟨M, b, hsat⟩
  refine ⟨q, N, ?_, hM, ?_, ?_⟩
  · exact (Algebra.Sat.isSaturated_iff_saturation_eq M).mp hsat |>.symm
  · have hinj : Function.Injective (stepMatrix L.matrix).mulVecLin := by
      intro x y h
      have hh := congrArg (C *ᵥ ·) h
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] using hh
    have he := (Submodule.equivMapOfInjective (stepMatrix L.matrix).mulVecLin hinj
      (normalLattice E)).finrank_eq
    change finrank ℤ (normalLattice E) = finrank ℤ M at he
    have hb : finrank ℤ M = q := by simpa using finrank_eq_card_basis b
    have hr := normal_rank_saturated E hE
    simp only [Fintype.card_option, Fintype.card_fin] at hr
    change q + finrank ℤ E = d + 1
    calc
      q + finrank ℤ E = finrank ℤ M + finrank ℤ E := by rw [hb]
      _ = finrank ℤ (normalLattice E) + finrank ℤ E := by rw [← he]
      _ = d + 1 := hr
  · have hc' : c ∈ Algebra.Sat.redSpan p (normalLattice E) := by
      have ha := hAnn p E hE
      change Algebra.Sat.modAnnihilator p E = Algebra.Sat.redSpan p (normalLattice E) at ha
      rw [← ha]
      exact hc
    have hh := pull_redSpan L (normalLattice E) c hc'
    have hred : redSpan p N = Algebra.Sat.redSpan p M := by
      unfold redSpan Algebra.Sat.redSpan
      congr 1
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
    rw [hred]
    exact hh

end Algebra.Mod.Pullback

end Praxis.Lift
