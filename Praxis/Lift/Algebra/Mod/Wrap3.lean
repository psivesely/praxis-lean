import Praxis.Lift.Algebra.Mod.WrapCount
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Lift.Algebra.Mod.WrapSupport
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trans.AlgModel
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.GridTrim

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

open Finset Praxis.Algebra.Inverse.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

set_option linter.ambiguousOpen false

universe u

namespace Praxis.Lift

namespace Algebra.Mod.Wrap3

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Lift.Algebra.Mod.Definitions

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem covariance_posDef {d : ℕ} (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (L : IntLat ι d) :
    (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).PosDef := by
  have hZ : LinearIndependent ℤ L.matrix.col :=
    L.basis.linearIndependent.map' L.carrier.subtype (Submodule.ker_subtype L.carrier)
  have hR : LinearIndependent ℝ (L.matrix.map (Int.castRingHom ℝ)).col := by
    have h := (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (v := L.matrix.col)).mpr hZ
    exact h
  let B := L.matrix.map (Int.castRingHom ℝ)
  have hi : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.mpr hR
  have hD : (Matrix.diagonal (fun i => (G i : ℝ)^2 / 12)).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    have h : (0 : ℝ) < G i := by exact_mod_cast hG i
    positivity
  have he : Analysis.gridCovariance G B =
      Bᴴ * Matrix.diagonal (fun i => (G i : ℝ)^2 / 12) * B := by
    ext j k
    change (∑ i, (G i : ℝ)^2 / 12 * B i j * B i k) =
      ∑ i, (Bᴴ * Matrix.diagonal (fun i => (G i : ℝ)^2 / 12) : Matrix (Fin d) ι ℝ) j i * B i k
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact hD.conjTranspose_mul_mul_same hi

theorem fullImageExclusion
    (hsection : Algebra.Point.SectionCount4)
    (hcb : ∀ (κ : Type u) [Fintype κ] [DecidableEq κ] [LinearOrder κ]
      (B : Matrix κ (Fin 3) ℝ) (sigma : κ → ℝ), Algebra.Trans.CauchyBinet3 B sigma)
    (he : ∀ (κ : Type u) [Fintype κ] [DecidableEq κ]
      (w : κ → ℝ) (S : ℝ), Algebra.Trans.ESymBounds w S)
    (_htrim : Algebra.Trim.TrimForIntLat)
    (P : VITParameters) (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι 3)
    (c : Option (Fin 3) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) : FullImageExclusion 3 P G Gx L c t F := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  intro _ _ hbudget hreg hc hne hf ht hr
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hG : ∀ i, 0 < G i := fun i => hg.trans_le (hbudget.1 (some i))
  have hGx : 0 < Gx := hg.trans_le (hbudget.1 none)
  have hSigma := covariance_posDef G hG L
  have hdet := covariance_determinant_le G L.matrix
    (hcb ι _ _) (he ι _ _)
  have hsum : (∑ i, (G i : ℝ)^2) ≤ (P.g : ℝ)^2 * P.S := by
    have h := hbudget.2.1
    rw [Fintype.sum_option] at h
    change (Gx : ℝ)^2 + (∑ i, (G i : ℝ)^2) ≤ _ at h
    linarith [sq_nonneg (Gx : ℝ)]
  have hcub := pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => sq_nonneg (G i : ℝ))) hsum 3
  have hbound : (Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ))).det ≤
      (L.H : ℝ)^2 * ((P.g : ℝ)^2 * P.S)^3 / (12^3 * 6) :=
    hdet.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcub (sq_nonneg _)) (by norm_num))
  have hcount := WrapCount.trimmed_image_count hsection P G Gx L c hc t F hne hf ht hr hSigma
  obtain ⟨hindex, hcoset⟩ := index_and_coset P G Gx L c t F hc hne hf
  refine ⟨hindex, hcoset, ?_, wrap3_lt P⟩
  change density F ≤ P.F * P.C3 / (P.p : ℝ)
  exact density_bound_of_image_count P G Gx L F hGx hreg _ hSigma.det_pos.le hbound hcount

end Algebra.Mod.Wrap3

end Praxis.Lift
