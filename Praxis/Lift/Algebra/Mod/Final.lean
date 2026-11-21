import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Algebra.Rank3Branch.VectorInverse
import Praxis.Combinatorics.Mass
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Praxis.Combinatorics.Chain
import Praxis.Lift.Record
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Rank3Branch.RankThreeBranch
import Praxis.Algebra.Rank3Branch.RankThreeLattice
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

noncomputable section

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.Final

open Praxis.Algebra Praxis.Algebra.Mod

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem grid_lower_pos (P : VITParameters) : 0 < P.g :=
  lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower

theorem mu_pos (P : VITParameters) : 0 < P.toVITData.mu :=
  P.eps_pos.trans P.eps_lt_mu

theorem redSpan_coordinates {p d : ℕ} (L : IntLat ι d) (z : ι → ZMod p)
    (hz : z ∈ redSpan p L) :
    ∃ c : Fin d → ZMod p, ∀ i, z i = ∑ j, (L.matrix i j : ZMod p) * c j := by
  let A := L.matrix.map (Int.castRingHom (ZMod p))
  have hle : redSpan p L ≤ LinearMap.range A.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨fun j => (L.basis.equivFun ⟨w, hw⟩ j : ZMod p), ?_⟩
    ext i
    have h := congrArg (fun a : ℤ => (a : ZMod p))
      (Algebra.Lattice.basis_eval L.carrier L.basis ⟨w, hw⟩ i)
    simpa only [A, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.map_apply, Int.coe_castRingHom, IntLat.matrix, Int.cast_sum,
      Int.cast_mul] using h
  obtain ⟨c, hc⟩ := hle hz
  exact ⟨c, fun i => (congrFun hc i).symm⟩

theorem lattice_maximal_minor {d : ℕ} (L : IntLat ι d) :
    ∃ r : Fin d → ι, (L.matrix.submatrix r id).det.natAbs = L.H ∧
      0 < L.H ∧ ∀ s : Fin d → ι, (L.matrix.submatrix s id).det.natAbs ≤ L.H := by
  obtain ⟨r, hdet, hmax⟩ := Algebra.VectorInverse.exists_maximal_basis_minor
    L.carrier L.saturated L.basis
  have heq : L.H = (L.matrix.submatrix r id).det.natAbs :=
    Algebra.VectorInverse.largestMinor_eq_pivot L.matrix r hmax
  exact ⟨r, heq.symm, heq ▸ Int.natAbs_pos.mpr hdet,
    fun s => (hmax s).trans_eq heq.symm⟩

theorem witness_mass_gt_mu (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) {d : ℕ} (L : IntLat ι d)
    (hm : P.theta0 < mass G (scalar G z))
    (hW : RegularWitness P.toVITData G z d L) :
    P.toVITData.mu < L.mZ G := by
  have he := P.eps_pos
  have hc := hW.2.2.2.2
  dsimp [VITData.mu]
  linarith

theorem regular_height_le (P : VITParameters) (G : ι → ℕ)
    {d : ℕ} (L : IntLat ι d) (hm : P.toVITData.mu < L.mZ G)
    (hreg : Regular P.toVITData G L) :
    (L.H : ℝ) ≤ P.toVITData.C d / ((P.g : ℝ)^d * P.toVITData.mu) := by
  have hg : (0 : ℝ) < P.g := by exact_mod_cast grid_lower_pos P
  have hmu := mu_pos P
  apply (le_div_iff₀ (mul_pos (pow_pos hg _) hmu)).mpr
  have hmul : P.toVITData.mu * (L.H : ℝ) ≤
      P.toVITData.C d / (P.g : ℝ)^d :=
    (mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg L.H)).trans hreg
  have h := (le_div_iff₀ (pow_pos hg d)).mp hmul
  nlinarith

theorem image_mass_le_of_fibBd (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin 3) ℤ) (b : ℝ)
    (hb : Combinatorics.FibBd G (Algebra.RankThree.rowVector B) univ b) :
    mass G (imageZ G B) ≤ b := by
  classical
  let r0 : Grid G := fun i => ⟨0, hG i⟩
  have hcard : (Fintype.card (Grid G) : ℝ) = ∏ i, (G i : ℝ) := by
    simp [Grid, Combinatorics.Mass.Grid, Fintype.card_pi, Nat.cast_prod]
  have hden : 0 < ∏ i, (G i : ℝ) :=
    prod_pos fun i _ => by exact_mod_cast hG i
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  have heq : Algebra.FiniteProbability.fibreCount (imageZ G B) t =
      (Combinatorics.fib G (Algebra.RankThree.rowVector B) univ r0 t).card := by
    unfold Algebra.FiniteProbability.fibreCount
    congr 1
    ext r
    rw [Combinatorics.fib_univ]
    simp only [mem_filter, mem_univ, true_and]
    have hmap : imageZ G B r =
        ∑ i, B i * (fun _ : Fin 3 => ((r i : ℕ) : ℤ)) := by
      ext j
      simp [imageZ, Finset.sum_apply]
    rw [hmap]
    rfl
  unfold Algebra.FiniteProbability.pointProb
  rw [heq, hcard]
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm] using hb r0 t

theorem rank_three_height_lt (P : VITParameters) (G : ι → ℕ)
    (hG : GridBudget P.toVITData G) (L : IntLat ι 3)
    (hm : P.toVITData.mu < L.mZ G) : (L.H : ℝ) < P.toVITData.H3 := by
  obtain ⟨r, hr, hH, _⟩ := lattice_maximal_minor L
  have hdet : (L.matrix.submatrix r id).det ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hr
    omega
  have hg := grid_lower_pos P
  have hgR : (0 : ℝ) < P.g := by exact_mod_cast hg
  have hb := Algebra.RankThree.integer_fibBd hg hG.1 P.g_upper.le
    (Algebra.VectorInverse.primitive_of_saturated_basis L.carrier L.saturated L.basis)
    r hdet
  have hmass := image_mass_le_of_fibBd G (fun i => hg.trans_le (hG.1 i)) L.matrix _ hb
  change L.mZ G ≤ (1 / (P.g : ℝ)^3) * Algebra.RankThree.xi P.g *
    (1 / ((L.matrix.submatrix r id).det.natAbs : ℝ) + 1 / (P.g : ℝ)) at hmass
  rw [hr] at hmass
  have hdelta : Algebra.RankThree.xi P.g / (P.g : ℝ) <
      (P.g : ℝ)^3 * P.toVITData.mu := by
    simpa only [Algebra.RankThree.xi, Combinatorics.UnequalChain.correction,
      VITData.xi] using (sub_pos.mp P.denominator_pos)
  have hthreshold : ((P.g : ℝ)^3 * P.toVITData.mu) / (P.g : ℝ)^3 < L.mZ G := by
    rwa [mul_div_cancel_left₀ _ (ne_of_gt (pow_pos hgR 3))]
  exact Algebra.RankThree.height_lt_of_chain hg (by exact_mod_cast hH) hdelta
    (hthreshold.trans_le hmass)

end Algebra.Mod.Final

end Praxis.Lift
