import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Lift.Algebra.Mod.SatApp
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Algebra.Prefix.Chain
import Praxis.Algebra.Basis.Rank1
import Praxis.Algebra.Basis.Rank2
import Praxis.Algebra.Basis.Rank3
import Praxis.Algebra.Basis.Gram3
import Praxis.Algebra.Basis.SizeReduce3
import Praxis.Algebra.Basis.MinPotential3
import Praxis.Algebra.Basis.Pivot
import Praxis.Algebra.Trim.Coeff
import Praxis.Algebra.Trim.UniformMGF
import Praxis.Algebra.Trim.Tensor
import Praxis.Algebra.Trim.Assemble
import Praxis.Combinatorics.Chain
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Algebra.Basis.Definitions
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Trim.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.IntegerLift
import Praxis.Algebra.InverseBranches.NormalBranches
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.NumericTrim
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation

set_option autoImplicit false

set_option maxHeartbeats 800000

universe u

noncomputable section

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.Induct

open Praxis.Algebra Praxis.Algebra.Mod

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

open Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem prime_mul_mu_gt (P : VITParameters) (G : ι → ℕ)
    (hG : GridBudget P.toVITData G) (i : ι) :
    54 < (P.p : ℝ) * P.toVITData.mu := by
  have hgN : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hg : (0 : ℝ) < P.g := by exact_mod_cast hgN
  have hmu : 0 < P.toVITData.mu := P.eps_pos.trans P.eps_lt_mu
  have hgi : (P.g : ℝ) ≤ G i := by exact_mod_cast hG.1 i
  have hsingle : (G i : ℝ)^2 ≤ ∑ j, (G j : ℝ)^2 :=
    single_le_sum (fun j _ => sq_nonneg (G j : ℝ)) (mem_univ i)
  have hS : 1 ≤ P.S := by
    have hsq := sq_le_sq₀ hg.le (hg.le.trans hgi) |>.mpr hgi
    have hbudget := hG.2.1
    nlinarith [sq_pos_of_pos hg]
  have hT : (P.g : ℝ)^2 ≤ P.toVITData.T2 := by
    unfold VITData.T2

    have hR2 : (400 : ℝ) ≤ P.R^2 := by nlinarith [P.trim.1]
    have hgS : 0 ≤ (P.g : ℝ)^2 * P.S := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [mul_nonneg (sq_nonneg (P.g : ℝ)) (sub_nonneg.mpr hS),
      mul_le_mul_of_nonneg_right hR2 hgS]
  have hxi : 1 ≤ P.toVITData.xi := by
    apply one_le_pow₀
    have : 0 ≤ 2 / (P.g : ℝ) := by positivity
    linarith
  have hH : 0 < P.toVITData.H3 := div_pos (by linarith) P.denominator_pos
  have hden : P.toVITData.H3 *
      ((P.g : ℝ)^3 * P.toVITData.mu - P.toVITData.xi / (P.g : ℝ)) =
      P.toVITData.xi := div_mul_cancel₀ _ (ne_of_gt P.denominator_pos)
  have hprod : 1 ≤ P.toVITData.H3 * (P.g : ℝ)^3 * P.toVITData.mu := by
    have hxg : 0 ≤ P.toVITData.xi / (P.g : ℝ) := by positivity
    nlinarith [mul_nonneg hH.le hxg]
  have hs : (54 * P.toVITData.H3 * (P.g : ℝ)^3)^2 < (P.p : ℝ)^2 := by
    calc
      _ = (54 * P.toVITData.H3)^2 * ((P.g : ℝ)^2)^3 := by ring
      _ ≤ (54 * P.toVITData.H3)^2 * P.toVITData.T2^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hT 3) (sq_nonneg _)
      _ < _ := P.minor3
  have hp := lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg P.p) hs
  have hmul := mul_lt_mul_of_pos_right hp hmu
  nlinarith only [hprod, hmul]

theorem redSpan_mono {p d e : ℕ} (L : IntLat ι d) (N : IntLat ι e)
    (h : L.carrier ≤ N.carrier) : redSpan p L ≤ redSpan p N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  exact Submodule.subset_span ⟨w, h hw, rfl⟩

def rebase {d : ℕ} (L : IntLat ι d) (b : Basis (Fin d) ℤ L.carrier) : IntLat ι d :=
  ⟨L.carrier, b, L.saturated⟩

theorem rebase_matrix {d : ℕ} (L : IntLat ι d) (b : Basis (Fin d) ℤ L.carrier) :
    (rebase L b).matrix = L.matrix * L.basis.toMatrix b := by
  ext i j
  exact (Algebra.Lattice.basis_eval L.carrier L.basis (b j) i).symm

theorem basis_change_det_natAbs {d : ℕ} (L : IntLat ι d)
    (b : Basis (Fin d) ℤ L.carrier) : (L.basis.toMatrix b).det.natAbs = 1 := by
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℤ => M.det.natAbs)
    (L.basis.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul, Int.natAbs_mul, Matrix.det_one, Int.natAbs_one] at h
  exact Nat.eq_one_of_mul_eq_one_right h

theorem rebase_height {d : ℕ} (L : IntLat ι d) (b : Basis (Fin d) ℤ L.carrier) :
    (rebase L b).H = L.H := by
  unfold IntLat.H height Algebra.VectorInverse.largestMinor
  rw [rebase_matrix]
  apply Finset.sup_congr rfl
  intro r _
  have heq : (L.matrix * L.basis.toMatrix b).submatrix r id =
      L.matrix.submatrix r id * L.basis.toMatrix b := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
  rw [heq, Matrix.det_mul, Int.natAbs_mul, basis_change_det_natAbs, mul_one]

theorem atomMass_comp_eq_of_injective {A B C : Type*} [Fintype A] [Nonempty A]
    [Nonempty B] (f : A → B) (φ : B → C) (hφ : Function.Injective φ) :
    Algebra.FiniteProbability.atomMass (φ ∘ f) = Algebra.FiniteProbability.atomMass f := by
  apply le_antisymm
  · exact Algebra.FiniteProbability.atomMass_comp_le f φ (fun _ _ h => hφ h)
  · apply Algebra.FiniteProbability.atomMass_le
    intro t
    exact (Algebra.FiniteProbability.pointProb_mono f (φ ∘ f) t (φ t)
      (fun x hx => congrArg φ hx)).trans (Algebra.FiniteProbability.pointProb_le_mass _ _)

theorem rebase_mass {d : ℕ} (L : IntLat ι d) (b : Basis (Fin d) ℤ L.carrier)
    (G : ι → ℕ) (hG : ∀ i, 0 < G i) : (rebase L b).mZ G = L.mZ G := by
  letI : Nonempty (Grid G) := ⟨fun i => ⟨0, hG i⟩⟩
  let U := L.basis.toMatrix b
  let V := b.toMatrix L.basis
  let φ : (Fin d → ℤ) → (Fin d → ℤ) := fun x => U.transpose *ᵥ x
  have hUV : U * V = 1 := L.basis.toMatrix_mul_toMatrix_flip b
  have hφ : Function.Injective φ := by
    intro x y h
    have he := congrArg (fun v => V.transpose *ᵥ v) h
    change V.transpose *ᵥ (U.transpose *ᵥ x) = V.transpose *ᵥ (U.transpose *ᵥ y) at he
    simpa only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hUV,
      Matrix.transpose_one, Matrix.one_mulVec] using he
  have hfun : imageZ G (rebase L b).matrix = φ ∘ imageZ G L.matrix := by
    funext r
    rw [rebase_matrix]
    change (L.matrix * U).transpose *ᵥ (fun i => ((r i : ℕ) : ℤ)) =
      U.transpose *ᵥ (L.matrix.transpose *ᵥ (fun i => ((r i : ℕ) : ℤ)))
    rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
  unfold IntLat.mZ
  rw [hfun]
  exact atomMass_comp_eq_of_injective _ φ hφ

theorem regularWitness_rebase (P : VITData) (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (z : ι → ZMod P.p) {d : ℕ} (L : IntLat ι d) (b : Basis (Fin d) ℤ L.carrier)
    (hW : RegularWitness P G z d L) : RegularWitness P G z d (rebase L b) := by
  rcases hW with ⟨hd, hd3, hz, hreg, hmass⟩
  refine ⟨hd, hd3, ?_, ?_, ?_⟩
  · exact hz
  · simpa only [Regular, rebase_mass L b G hG, rebase_height] using hreg
  · simpa only [rebase_mass L b G hG] using hmass

theorem exists_controlled_basis {d : ℕ} (L : IntLat ι d) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ b : Basis (Fin d) ℤ L.carrier,
      (∏ j, (maxAbs (b j : ι → ℤ) : ℝ)) ≤ (Algebra.Basis.J d : ℝ) * (L.H : ℝ) := by
  interval_cases d
  · exact Algebra.Basis.controlledBasis_rank1 L (by decide) (by decide)
  · exact Algebra.Basis.Rank2.controlledBasis2_of_pivot Algebra.Basis.pivotProjectionBound_holds
      L (by decide) (by decide)
  · exact Algebra.Basis.controlledBasis3 Algebra.Basis.Gram3.gram3Identities
      (Algebra.Basis.MinPotential3.reducedPotential3 Algebra.Basis.Gram3.gram3Identities
        (Algebra.Basis.sizeReduce3 Algebra.Basis.Gram3.gram3Identities))
      Algebra.Basis.pivotProjectionBound_holds L (by decide) (by decide)

theorem basis_maxAbs_pos {d : ℕ} (L : IntLat ι d)
    (b : Basis (Fin d) ℤ L.carrier) (j : Fin d) : 1 ≤ maxAbs (b j : ι → ℤ) := by
  by_contra h
  have hz : maxAbs (b j : ι → ℤ) = 0 := by omega
  apply b.ne_zero j
  apply Subtype.ext
  ext i
  apply Int.natAbs_eq_zero.mp
  have hi : ((b j : ι → ℤ) i).natAbs ≤ maxAbs (b j : ι → ℤ) :=
    Finset.le_sup (f := fun i => ((b j : ι → ℤ) i).natAbs) (mem_univ i)
  rw [hz] at hi
  exact Nat.eq_zero_of_le_zero hi

theorem witness_height_bound (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) {d : ℕ} (L : IntLat ι d)
    (hm : P.theta0 < mass G (scalar G z))
    (hG : GridBudget P.toVITData G) (hW : RegularWitness P.toVITData G z d L)
    (h3 : ∀ N : IntLat ι 3, Rank3Height P G N) :
    (L.H : ℝ) ≤ heightBound P.toVITData d := by
  have he := P.eps_pos
  have hmu : P.toVITData.mu ≤ L.mZ G := by
    have hretain := hW.2.2.2.2
    dsimp [VITData.mu]
    linarith
  have hmuPos : 0 < P.toVITData.mu := P.eps_pos.trans P.eps_lt_mu
  have hg : (0 : ℝ) < P.g := by
    exact_mod_cast lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hbound : (L.H : ℝ) ≤ P.toVITData.C d / ((P.g : ℝ)^d * P.toVITData.mu) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hg d) hmuPos)).mpr
    have hmul : P.toVITData.mu * (L.H : ℝ) ≤
        P.toVITData.C d / (P.g : ℝ)^d :=
      (mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)).trans hW.2.2.2.1
    have hc := (le_div_iff₀ (pow_pos hg d)).mp hmul
    nlinarith
  have hd := hW.1
  have hd3 := hW.2.1
  interval_cases d
  · simpa [heightBound, VITData.C, VITData.H1] using hbound
  · simpa [heightBound, VITData.C, VITData.H2] using hbound
  · simpa [heightBound] using (h3 L hG hmu).1

theorem exists_controlled_rebase (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) {d : ℕ} (L : IntLat ι d)
    (hm : P.theta0 < mass G (scalar G z))
    (hG : GridBudget P.toVITData G) (hW : RegularWitness P.toVITData G z d L)
    (h3 : ∀ N : IntLat ι 3, Rank3Height P G N) :
    ∃ b : Basis (Fin d) ℤ L.carrier,
      (∀ j, 1 ≤ maxAbs (b j : ι → ℤ)) ∧
      (∏ j, (maxAbs (b j : ι → ℤ) : ℝ)) ≤
        basisConstant d * heightBound P.toVITData d ∧
      RegularWitness P.toVITData G z d (rebase L b) := by
  obtain ⟨b, hb⟩ := exists_controlled_basis L hW.1 hW.2.1
  have hheight := witness_height_bound P G z L hm hG hW h3
  have hJ : (Algebra.Basis.J d : ℝ) = basisConstant d := by
    have hd := hW.1
    have hd3 := hW.2.1
    interval_cases d <;> norm_num [Algebra.Basis.J, basisConstant]
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  refine ⟨b, basis_maxAbs_pos L b, ?_,
    regularWitness_rebase P.toVITData G (fun i => hg.trans_le (hG.1 i)) z L b hW⟩
  rw [← hJ]
  exact hb.trans (mul_le_mul_of_nonneg_left hheight (Nat.cast_nonneg _))

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

theorem exists_step_congruence {p d : ℕ} (L : IntLat ι d)
    (z : ι → ZMod p) (a : ZMod p) (hz : z ∈ redSpan p L) (hne : z ≠ 0) :
    ∃ c : Option (Fin d) → ZMod p, c ≠ 0 ∧ pullMod L.matrix c = extend z a := by
  obtain ⟨v, hv⟩ := redSpan_coordinates L z hz
  let c := extend v a
  have heq : pullMod L.matrix c = extend z a := by
    ext i
    cases i with
    | none => simp [pullMod, stepMatrix, Matrix.mulVec, dotProduct, c, extend, Fintype.sum_option]
    | some i => simpa [pullMod, stepMatrix, Matrix.mulVec, dotProduct, c, extend,
        Fintype.sum_option] using (hv i).symm
  refine ⟨c, ?_, heq⟩
  intro hc
  apply hne
  ext i
  have hh := congrFun heq (some i)
  simpa [hc, pullMod, Matrix.mulVec, dotProduct, extend] using hh.symm

theorem scalar_pullMod {d p : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (c : Option (Fin d) → ZMod p)
    (r : Grid (extend G Gx)) :
    scalar (extend G Gx) (pullMod B c) r =
      ∑ i, c i * (stepImage G Gx B r i : ZMod p) := by
  simp only [scalar, pullMod, stepImage, Matrix.mulVec, dotProduct,
    Matrix.map_apply, Int.coe_castRingHom, Matrix.transpose_apply,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem largest_scalar_fibre (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) (hG : GridBudget P.toVITData G)
    (hm : P.theta0 < mass G (scalar G z)) :
    ∃ t : ZMod P.p, ∃ F : Finset (Grid G), F.Nonempty ∧
      (∀ r ∈ F, scalar G z r = t) ∧
      Algebra.Mod.Definitions.density F = mass G (scalar G z) := by
  classical
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  obtain ⟨t, _, ht⟩ := exists_max_image (univ : Finset (ZMod P.p))
    (Algebra.FiniteProbability.pointProb (scalar G z)) univ_nonempty
  have hmass : mass G (scalar G z) = Algebra.FiniteProbability.pointProb (scalar G z) t := by
    apply le_antisymm
    · exact Algebra.FiniteProbability.atomMass_le _ (fun s => ht s (mem_univ s))
    · exact Algebra.FiniteProbability.pointProb_le_mass _ _
  let F : Finset (Grid G) := univ.filter fun r => scalar G z r = t
  have hden : Algebra.Mod.Definitions.density F = mass G (scalar G z) := by
    rw [hmass]
    simp [Algebra.Mod.Definitions.density, Algebra.FiniteProbability.pointProb, Algebra.FiniteProbability.fibreCount, F]
    congr 3
    ext r
    simp
  refine ⟨t, F, ?_, ?_, hden⟩
  · by_contra h
    have hempty : F = ∅ := not_nonempty_iff_eq_empty.mp h
    have hzero : Algebra.Mod.Definitions.density F = 0 := by simp [hempty, Algebra.Mod.Definitions.density]
    have he := P.eps_pos
    have hmu := P.eps_lt_mu
    dsimp [VITData.mu] at hmu
    linarith
  · intro r hr
    exact (mem_filter.mp hr).2

theorem regularize_current (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) (hG : GridBudget P.toVITData G)
    (hm : P.theta0 < mass G (scalar G z))
    (h3 : ∀ L : IntLat ι 3, Rank3Height P G L)
    (h2 : ∀ L : IntLat ι 2, Regularize2 P G L)
    (h1 : ∀ L : IntLat ι 1, Regularize1 P G L)
    {d : ℕ} (L : IntLat ι d) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hz : z ∈ redSpan P.p L)
    (hretain : mass G (scalar G z) - P.eps ≤ L.mZ G) :
    ∃ q : ℕ, ∃ N : IntLat ι q, RegularWitness P.toVITData G z q N := by
  have he := P.eps_pos
  have hmu : P.toVITData.mu ≤ L.mZ G := by
    dsimp [VITData.mu]
    linarith
  interval_cases d
  · have hdomain : P.theta0 - 20 * P.eps ≤ L.mZ G := by linarith
    rcases h1 L hG hdomain with hreg | ⟨N, hLN, hmass, hreg⟩ |
      ⟨N, hLN, hmass, _, hreg⟩
    · exact ⟨1, L, by decide, by decide, hz, hreg, by linarith⟩
    · exact ⟨2, N, by decide, by decide, redSpan_mono L N hLN hz, hreg, by linarith⟩
    · exact ⟨3, N, by decide, by decide, redSpan_mono L N hLN hz, hreg, by linarith⟩
  · have hdomain : P.theta0 - 30 * P.eps ≤ L.mZ G := by linarith
    rcases h2 L hG hdomain with hreg | ⟨N, hLN, hmass, _, hreg⟩
    · exact ⟨2, L, by decide, by decide, hz, hreg, by linarith⟩
    · exact ⟨3, N, by decide, by decide, redSpan_mono L N hLN hz, hreg, by linarith⟩
  · obtain ⟨_, hreg⟩ := h3 L hG hmu
    exact ⟨3, L, by decide, by decide, hz, hreg, by linarith⟩

theorem image_rank_ne_full (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι d)
    (c : Option (Fin d) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx)))
    (hwrap : FullImageExclusion d P G Gx L c t F)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) (hG : GridBudget P.toVITData (extend G Gx))
    (hreg : Regular P.toVITData G L) (hc : c ≠ 0) (hF : F.Nonempty)
    (hfibre : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t)
    (htrim : Trimmed P.toVITData G Gx L.matrix F)
    (hheavy : P.toVITData.mu ≤ Algebra.Mod.Definitions.density F) :
    Analysis.rationalRank (imageDifferences (stepImage G Gx L.matrix) F) ≠ d + 1 := by
  intro hrank
  obtain ⟨_, _, hbound, hstrict⟩ := hwrap hd hd3 hG hreg hc hF hfibre htrim hrank
  exact (not_lt_of_ge hheavy) (hbound.trans_lt hstrict)

theorem imageDifferences_killed {d p : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (c : Option (Fin d) → ZMod p) (t : ZMod p)
    (F : Finset (Grid (extend G Gx)))
    (hf : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx B r i : ZMod p) = t) :
    Analysis.KillsColumns p c (imageDifferences (stepImage G Gx B) F) := by
  intro s
  simp only [imageDifferences, Int.cast_sub, mul_sub, sum_sub_distrib,
    hf s.1.val s.1.property, hf s.2.val s.2.property, sub_self]

theorem image_saturation_killed (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (B : Matrix ι (Fin d) ℤ)
    (c : Option (Fin d) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx)))
    (hf : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx B r i : ZMod P.p) = t)
    (hsmall : ∀ (I : Fin (Analysis.rationalRank
        (imageDifferences (stepImage G Gx B) F)) → Option (Fin d))
      (J : Fin (Analysis.rationalRank
        (imageDifferences (stepImage G Gx B) F)) → F × F),
      |((imageDifferences (stepImage G Gx B) F).submatrix I J).det| < (P.p : ℤ)) :
    Analysis.KillsSubmodule P.p c (Analysis.saturation
      (Analysis.columnLattice (imageDifferences (stepImage G Gx B) F))) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  exact Analysis.kills_saturation_of_small_minors _ _ rfl
    (imageDifferences_killed G Gx B c t F hf) hsmall

theorem pullback_event_mass (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι d)
    (E : Submodule ℤ (Option (Fin d) → ℤ))
    (c : Option (Fin d) → ZMod P.p)
    (F : Finset (Grid (extend G Gx)))
    (hpb : ModPullback L E c) (hsat : Saturated E)
    (hkill : Analysis.KillsSubmodule P.p c E) (hF : F.Nonempty)
    (hE : ∀ r ∈ F, ∀ s ∈ F,
      stepImage G Gx L.matrix r - stepImage G Gx L.matrix s ∈ E) :
    ∃ q : ℕ, ∃ N : IntLat (Option ι) q,
      q + Module.finrank ℤ E = d + 1 ∧
      pullMod L.matrix c ∈ redSpan P.p N ∧
      Algebra.Mod.Definitions.density F ≤ N.mZ (extend G Gx) := by
  classical
  obtain ⟨q, N, _, hnormal, hdim, hz⟩ := hpb P.p_prime hsat hkill
  refine ⟨q, N, hdim, hz, ?_⟩
  obtain ⟨r, hr⟩ := hF
  have hconst : ∀ s ∈ F, imageZ (extend G Gx) N.matrix s =
      imageZ (extend G Gx) N.matrix r := by
    intro s hs
    ext j
    have hw : (N.basis j : Option ι → ℤ) ∈ Algebra.VectorInverse.normalLattice
        (E.comap (stepMatrix L.matrix).transpose.mulVecLin) :=
      (congrArg (fun S : Submodule ℤ (Option ι → ℤ) =>
        (N.basis j : Option ι → ℤ) ∈ S) hnormal).mp (N.basis j).property
    let vs : Option ι → ℤ := fun i => ((s i : ℕ) : ℤ)
    let vr : Option ι → ℤ := fun i => ((r i : ℕ) : ℤ)
    have hv : vs - vr ∈ E.comap (stepMatrix L.matrix).transpose.mulVecLin := by
      change (stepMatrix L.matrix).transpose *ᵥ (vs - vr) ∈ E
      rw [Matrix.mulVec_sub]
      exact hE s hs r hr
    have he := hw (vs - vr) hv
    apply sub_eq_zero.mp
    simpa only [imageZ, IntLat.matrix, vs, vr, Pi.sub_apply, mul_sub,
      sum_sub_distrib] using he
  have hc : F.card ≤ Algebra.FiniteProbability.fibreCount (imageZ (extend G Gx) N.matrix)
      (imageZ (extend G Gx) N.matrix r) := by
    apply card_le_card
    intro s hs
    simp only [mem_filter, mem_univ, true_and]
    exact hconst s hs
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (Nat.cast_nonneg _)).trans (Algebra.FiniteProbability.pointProb_le_mass _ _)

theorem integer_mass_pivot_any_rank {d : ℕ} (L : IntLat ι d)
    (G : ι → ℕ) (g : ℕ) (hg : 0 < g) (hG : ∀ i, g ≤ G i) :
    L.mZ G ≤ 1 / (g : ℝ)^d := by
  obtain ⟨r, hdet, _⟩ := Algebra.VectorInverse.exists_maximal_basis_minor
    L.carrier L.saturated L.basis
  have hGp : ∀ i, 0 < G i := fun i => hg.trans_le (hG i)
  have hb := (Algebra.VectorInverse.pivot_fibBd G L.matrix r hGp hdet).extend (subset_univ _)
  apply (Algebra.Prefix.mass_le_of_fibBd hGp hb).trans
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (g : ℝ)^d = ∏ _ : Fin d, (g : ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => by positivity)
      (fun i _ => by exact_mod_cast hG (r i))

theorem rank_le_three_of_heavy_lattice (P : VITParameters) (G : ι → ℕ)
    (hG : GridBudget P.toVITData G) {d : ℕ} (L : IntLat ι d)
    (hm : P.toVITData.mu ≤ L.mZ G) : d ≤ 3 := by
  have hgN : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hg : (0 : ℝ) < P.g := by exact_mod_cast hgN
  by_contra hd
  have hfour : 4 ≤ d := by omega
  have hg1 : (1 : ℝ) ≤ P.g := by exact_mod_cast hgN
  have hpow : (P.g : ℝ)^4 ≤ (P.g : ℝ)^d := pow_le_pow_right₀ hg1 hfour
  have hbound := (integer_mass_pivot_any_rank L G P.g hgN hG.1).trans
    (one_div_le_one_div_of_le (pow_pos hg 4) hpow)
  have hlight : 1 / (P.g : ℝ)^4 < P.toVITData.mu := by
    simpa only [zpow_neg, zpow_ofNat, one_div] using P.rank4_light
  exact (not_lt_of_ge hm) (hbound.trans_lt hlight)

theorem regularWitness_of_current_span (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι d)
    (E : Submodule ℤ (Option (Fin d) → ℤ))
    (c : Option (Fin d) → ZMod P.p) (w : Option ι → ZMod P.p)
    (F : Finset (Grid (extend G Gx)))
    (hG : GridBudget P.toVITData (extend G Gx))
    (hm : P.theta0 < mass (extend G Gx) (scalar (extend G Gx) w))
    (hpb : ModPullback L E c) (hsat : Saturated E)
    (hkill : Analysis.KillsSubmodule P.p c E) (hF : F.Nonempty)
    (hE : ∀ r ∈ F, ∀ s ∈ F,
      stepImage G Gx L.matrix r - stepImage G Gx L.matrix s ∈ E)
    (hw : w = pullMod L.matrix c)
    (hrank : Module.finrank ℤ E ≤ d)
    (hretain : mass (extend G Gx) (scalar (extend G Gx) w) - P.eps ≤
      Algebra.Mod.Definitions.density F)
    (h3 : ∀ N : IntLat (Option ι) 3, Rank3Height P (extend G Gx) N)
    (h2 : ∀ N : IntLat (Option ι) 2, Regularize2 P (extend G Gx) N)
    (h1 : ∀ N : IntLat (Option ι) 1, Regularize1 P (extend G Gx) N) :
    ∃ q : ℕ, ∃ N : IntLat (Option ι) q,
      RegularWitness P.toVITData (extend G Gx) w q N := by
  obtain ⟨q, N, hdim, hz, hmass⟩ := pullback_event_mass P G Gx L E c F hpb hsat hkill hF hE
  have hq : 1 ≤ q := by omega
  have hmu : P.toVITData.mu ≤ N.mZ (extend G Gx) := by
    have he := P.eps_pos
    dsimp [VITData.mu]
    linarith
  have hq3 : q ≤ 3 := rank_le_three_of_heavy_lattice P (extend G Gx) hG N hmu
  have hwN : w ∈ redSpan P.p N := by simpa only [hw] using hz
  exact regularize_current P (extend G Gx) w hG hm h3 h2 h1 N hq hq3 hwN
    (hretain.trans hmass)

theorem regularWitness_of_small_trimmed_fibre (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι d)
    (c : Option (Fin d) → ZMod P.p) (w : Option ι → ZMod P.p)
    (t : ZMod P.p) (F : Finset (Grid (extend G Gx)))
    (hd : 1 ≤ d) (hd3 : d ≤ 3) (hG : GridBudget P.toVITData (extend G Gx))
    (hm : P.theta0 < mass (extend G Gx) (scalar (extend G Gx) w))
    (hreg : Regular P.toVITData G L) (hc : c ≠ 0) (hF : F.Nonempty)
    (hfibre : ∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t)
    (htrim : Trimmed P.toVITData G Gx L.matrix F)
    (hretain : mass (extend G Gx) (scalar (extend G Gx) w) - P.eps ≤
      Algebra.Mod.Definitions.density F)
    (hw : w = pullMod L.matrix c)
    (hsmall : ∀ e : ℕ, e ≤ d →
      ∀ (I : Fin e → Option (Fin d)) (J : Fin e → F × F),
        |((imageDifferences (stepImage G Gx L.matrix) F).submatrix I J).det| < (P.p : ℤ))
    (hwrap : FullImageExclusion d P G Gx L c t F)
    (hpb : ∀ E : Submodule ℤ (Option (Fin d) → ℤ), ModPullback L E c)
    (h3 : ∀ N : IntLat (Option ι) 3, Rank3Height P (extend G Gx) N)
    (h2 : ∀ N : IntLat (Option ι) 2, Regularize2 P (extend G Gx) N)
    (h1 : ∀ N : IntLat (Option ι) 1, Regularize1 P (extend G Gx) N) :
    ∃ q : ℕ, ∃ N : IntLat (Option ι) q,
      RegularWitness P.toVITData (extend G Gx) w q N := by
  let D := imageDifferences (stepImage G Gx L.matrix) F
  let E := Analysis.saturation (Analysis.columnLattice D)
  have hheavy : P.toVITData.mu ≤ Algebra.Mod.Definitions.density F := by
    have he := P.eps_pos
    dsimp [VITData.mu]
    linarith
  have hne := image_rank_ne_full P G Gx L c t F hwrap hd hd3 hG hreg hc hF
    hfibre htrim hheavy
  have hle : Analysis.rationalRank D ≤ d + 1 := by
    simpa only [Analysis.rationalRank, Fintype.card_option, Fintype.card_fin] using
      Matrix.rank_le_card_height (D.map (Int.castRingHom ℚ))
  have hrank : Analysis.rationalRank D ≤ d := by
    change Analysis.rationalRank D ≠ d + 1 at hne
    omega
  have hEsat : Saturated E := Algebra.Lattice.saturation_isSaturated _
  have hEkill : Analysis.KillsSubmodule P.p c E :=
    image_saturation_killed P G Gx L.matrix c t F hfibre (hsmall _ hrank)
  have hEdiff : ∀ r ∈ F, ∀ s ∈ F,
      stepImage G Gx L.matrix r - stepImage G Gx L.matrix s ∈ E := by
    intro r hr s hs
    apply Algebra.Lattice.le_saturation (Analysis.columnLattice D)
    apply Submodule.subset_span
    exact ⟨(⟨r, hr⟩, ⟨s, hs⟩), rfl⟩
  have hErank : Module.finrank ℤ E = Analysis.rationalRank D := by
    rw [Analysis.rationalRank_eq_finrank]
    exact Algebra.Lattice.finrank_saturation _
  exact regularWitness_of_current_span P G Gx L E c w F hG hm (hpb E) hEsat
    hEkill hF hEdiff hw (hErank.trans_le hrank) hretain h3 h2 h1

def reindexLattice (e : ι ≃ κ) {d : ℕ} (L : IntLat ι d) : IntLat κ d :=
  let E := LinearEquiv.piCongrLeft' ℤ (fun _ : ι => ℤ) e
  { carrier := L.carrier.map E.toLinearMap
    basis := L.basis.map (E.submoduleMap L.carrier)
    saturated := by
      intro n hn x hx
      obtain ⟨y, hy, hxy⟩ := hx
      change E y = n • x at hxy
      have h : n • E.symm x ∈ L.carrier := by
        have he : n • E.symm x = y := by
          have h := congrArg E.symm hxy
          simpa only [LinearEquiv.symm_apply_apply, map_smul] using h.symm
        rw [he]
        exact hy
      exact ⟨E.symm x, L.saturated n hn _ h, E.apply_symm_apply x⟩ }

theorem reindexLattice_matrix (e : ι ≃ κ) {d : ℕ} (L : IntLat ι d) :
    (reindexLattice e L).matrix = fun i j => L.matrix (e.symm i) j := by
  rfl

theorem reindexLattice_height (e : ι ≃ κ) {d : ℕ} (L : IntLat ι d) :
    (reindexLattice e L).H = L.H := by
  unfold IntLat.H height Algebra.VectorInverse.largestMinor
  rw [reindexLattice_matrix]
  apply le_antisymm
  · apply Finset.sup_le
    intro r _
    exact Finset.le_sup (f := fun r : Fin d → ι =>
      (L.matrix.submatrix r id).det.natAbs) (mem_univ (e.symm ∘ r))
  · apply Finset.sup_le
    intro r _
    have h := Finset.le_sup (f := fun r : Fin d → κ =>
      (Matrix.submatrix (fun i j => L.matrix (e.symm i) j) r id).det.natAbs)
      (mem_univ (e ∘ r))
    have heq : Matrix.submatrix (fun i j => L.matrix (e.symm i) j) (e ∘ r) id =
        L.matrix.submatrix r id := by
      ext i j
      change L.matrix (e.symm (e (r i))) j = L.matrix (r i) j
      rw [e.symm_apply_apply]
    rw [heq] at h
    exact h

theorem atom_precomp_equiv {A B C : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → C) (t : C) :
    Algebra.FiniteProbability.pointProb (f ∘ e) t = Algebra.FiniteProbability.pointProb f t := by
  classical
  unfold Algebra.FiniteProbability.pointProb Algebra.FiniteProbability.fibreCount
  rw [Fintype.card_congr e]
  congr 1
  exact_mod_cast Finset.card_equiv e (by intro x; simp)

theorem mass_precomp_equiv {A B C : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → C) :
    Algebra.FiniteProbability.atomMass (f ∘ e) = Algebra.FiniteProbability.atomMass f := by
  unfold Algebra.FiniteProbability.atomMass
  congr 1
  funext t
  exact atom_precomp_equiv e f t

theorem atomMass_snd {A B C : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (f : B → C) : Algebra.FiniteProbability.atomMass (fun x : A × B => f x.2) =
      Algebra.FiniteProbability.atomMass f := by
  unfold Algebra.FiniteProbability.atomMass
  congr 1
  funext t
  rw [Algebra.FiniteProbability.pointProb_prod]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero)

theorem coordinate_mass {C : Type*} (G : ι → ℕ) (hG : ∀ j, 0 < G j)
    (i : ι) (f : Fin (G i) → C) :
    mass G (fun r => f (r i)) = Algebra.FiniteProbability.atomMass f := by
  let A := (j : {j : ι // j ≠ i}) → Fin (G j.val)
  letI : Nonempty A := ⟨fun j => ⟨0, hG j.val⟩⟩
  let E : Grid G ≃ A × Fin (G i) :=
    (Equiv.piSplitAt i (fun j => Fin (G j))).trans (Equiv.prodComm _ _)
  have h : (fun r : Grid G => f (r i)) ∘ E.symm = fun x : A × Fin (G i) => f x.2 := by
    funext x
    simp [E, Equiv.piSplitAt, Equiv.prodComm]
  exact (mass_precomp_equiv E.symm _).symm.trans
    ((congrArg Algebra.FiniteProbability.atomMass h).trans (atomMass_snd f))

def coordinateCarrier (i : ι) : Submodule ℤ (ι → ℤ) where
  carrier := {w | ∀ j, j ≠ i → w j = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro a x hx j hj; simp [hx j hj]

def coordinateEquiv (i : ι) : coordinateCarrier i ≃ₗ[ℤ] (Fin 1 → ℤ) where
  toFun w := fun _ => w.val i
  invFun w := ⟨Pi.single i (w 0), by intro j hj; simp [hj]⟩
  left_inv w := by
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h, w.property j h]
  right_inv w := by ext j; rw [Subsingleton.elim j 0]; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinateLattice (i : ι) : IntLat ι 1 where
  carrier := coordinateCarrier i
  basis := Basis.ofEquivFun (coordinateEquiv i)
  saturated := by
    intro n hn w hw j hj
    have h : n * w j = 0 := hw j hj
    exact (mul_eq_zero.mp h).resolve_left hn

theorem coordinateLattice_matrix (i : ι) : (coordinateLattice i).matrix =
    fun j _ => if j = i then 1 else 0 := by
  funext j k
  change ((Basis.ofEquivFun (coordinateEquiv i)) k).val j = _
  rw [Basis.coe_ofEquivFun]
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  simp [coordinateEquiv, Pi.single_apply]

theorem coordinateLattice_height (i : ι) : (coordinateLattice i).H = 1 := by
  unfold IntLat.H height Algebra.VectorInverse.largestMinor
  rw [coordinateLattice_matrix]
  apply le_antisymm
  · apply Finset.sup_le
    intro r _
    rw [Matrix.det_fin_one]
    change (if r 0 = i then (1 : ℤ) else 0).natAbs ≤ 1
    split_ifs <;> norm_num
  · apply Finset.le_sup_of_le (mem_univ (fun _ : Fin 1 => i))
    norm_num [Matrix.det_fin_one, Matrix.submatrix]

theorem coordinateLattice_image (i : ι) (G : ι → ℕ) (r : Grid G) :
    imageZ G (coordinateLattice i).matrix r = fun _ => ((r i : ℕ) : ℤ) := by
  rw [coordinateLattice_matrix]
  ext j
  simp [imageZ]

theorem coordinateLattice_redSpan (i : ι) {p : ℕ} (z : ι → ZMod p)
    (hz : ∀ j, j ≠ i → z j = 0) : z ∈ redSpan p (coordinateLattice i) := by
  let w : ι → ℤ := Pi.single i 1
  have hu : w ∈ (coordinateLattice i).carrier := by
    intro j hj
    simp [w, hj]
  have hcast : (fun j => (w j : ZMod p)) ∈
      redSpan p (coordinateLattice i) := by
    apply Submodule.subset_span
    exact ⟨w, hu, rfl⟩
  have heq : z = z i • (fun j => (w j : ZMod p)) := by
    ext j
    by_cases h : j = i
    · subst j; simp [w]
    · simp [w, h, hz j h]
  rw [heq]
  exact Submodule.smul_mem _ _ hcast

theorem atomMass_of_injective {A C : Type*} [Fintype A] (f : A → C)
    (a : A) (hf : Function.Injective f) :
    Algebra.FiniteProbability.atomMass f = 1 / (Fintype.card A : ℝ) := by
  classical
  letI : Nonempty C := ⟨f a⟩
  apply le_antisymm
  · apply Algebra.FiniteProbability.atomMass_le
    intro t
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hc : (univ.filter fun r => f r = t).card ≤ 1 :=
      Finset.card_le_one.mpr (by
        intro r hr s hs
        exact hf ((mem_filter.mp hr).2.trans (mem_filter.mp hs).2.symm))
    exact_mod_cast hc
  · have hc : Algebra.FiniteProbability.fibreCount f (f a) = 1 := by
      unfold Algebra.FiniteProbability.fibreCount
      have he : (univ.filter fun r => f r = f a) = {a} := by ext r; simp [hf.eq_iff]
      rw [he, card_singleton]
    simpa only [Algebra.FiniteProbability.pointProb, hc, Nat.cast_one] using
      Algebra.FiniteProbability.pointProb_le_mass f (f a)

theorem coordinateLattice_mass (i : ι) (G : ι → ℕ) (hG : ∀ j, 0 < G j) :
    (coordinateLattice i).mZ G = 1 / (G i : ℝ) := by
  unfold IntLat.mZ
  have hfun : imageZ G (coordinateLattice i).matrix =
      fun r => fun _ : Fin 1 => ((r i : ℕ) : ℤ) := funext (coordinateLattice_image i G)
  rw [hfun]
  rw [coordinate_mass G hG i (fun k : Fin (G i) => fun _ : Fin 1 => ((k : ℕ) : ℤ))]
  have hi : Function.Injective (fun k : Fin (G i) => fun _ : Fin 1 => ((k : ℕ) : ℤ)) := by
    intro a b h
    have hh := congrFun h 0
    change ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) at hh
    exact Fin.ext (by exact_mod_cast hh)
  simpa using atomMass_of_injective _ (⟨0, hG i⟩ : Fin (G i)) hi

theorem scalar_support_one_mass (P : VITData) (G : ι → ℕ) (hG : ∀ j, 0 < G j)
    (z : ι → ZMod P.p) (i : ι) (hz : ∀ j, j ≠ i → z j = 0) :
    mass G (scalar G z) = Algebra.FiniteProbability.atomMass
      (fun k : Fin (G i) => z i * ((k : ℕ) : ZMod P.p)) := by
  have heq : scalar G z = fun r => z i * ((r i : ℕ) : ZMod P.p) := by
    funext r
    change (∑ j, z j * ((r j : ℕ) : ZMod P.p)) = z i * ((r i : ℕ) : ZMod P.p)
    apply sum_eq_single i
    · intro j _ hji
      rw [hz j hji, zero_mul]
    · intro h
      exact (h (mem_univ i)).elim
  rw [heq]
  exact coordinate_mass G hG i (fun k : Fin (G i) => z i * ((k : ℕ) : ZMod P.p))

theorem wide_coordinate_mass_le (P : VITParameters) {G : ℕ} (hG : P.p ≤ G)
    (a : ZMod P.p) (ha : a ≠ 0) :
    Algebra.FiniteProbability.atomMass (fun k : Fin G => a * ((k : ℕ) : ZMod P.p)) ≤ 2 / (P.p : ℝ) := by
  classical
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hp : (0 : ℝ) < P.p := by exact_mod_cast P.p_prime.pos
  have hg : (0 : ℝ) < G := by exact_mod_cast (P.p_prime.pos.trans_le hG)
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  let F : Finset (Fin G) := univ.filter fun k => a * ((k : ℕ) : ZMod P.p) = t
  have hmod : ∀ r ∈ F, ∀ s ∈ F, (r : ℕ) ≡ (s : ℕ) [MOD P.p] := by
    intro r hr s hs
    have hcast : ((r : ℕ) : ZMod P.p) = ((s : ℕ) : ZMod P.p) :=
      mul_left_cancel₀ ha ((mem_filter.mp hr).2.trans (mem_filter.mp hs).2.symm)
    exact (ZMod.natCast_eq_natCast_iff' _ _ P.p).mp hcast
  have hc := Combinatorics.card_le_ceil P.p_prime.pos F hmod
  have hdiv : ((G + P.p - 1) / P.p) * P.p ≤ G + P.p :=
    (Nat.div_mul_le_self _ _).trans (by omega)
  have hcR : (F.card : ℝ) * P.p ≤ (G : ℝ) + P.p := by
    have hn := (Nat.mul_le_mul_right P.p hc).trans hdiv
    exact_mod_cast hn
  have hpg : (P.p : ℝ) ≤ G := by exact_mod_cast hG
  unfold Algebra.FiniteProbability.pointProb Algebra.FiniteProbability.fibreCount
  simp only [Fintype.card_fin]
  change (F.card : ℝ) / G ≤ 2 / (P.p : ℝ)
  apply (div_le_div_iff₀ hg hp).mpr
  linarith

theorem support_one_width_lt (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) (i : ι) (hs : ∀ j, j ≠ i → z j = 0)
    (hG : GridBudget P.toVITData G) (hz : z ≠ 0)
    (hm : P.theta0 < mass G (scalar G z)) : G i < P.p := by
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hpos : ∀ j, 0 < G j := fun j => hg.trans_le (hG.1 j)
  have hi : z i ≠ 0 := by
    intro hzero
    apply hz
    ext j
    by_cases hji : j = i
    · subst j; exact hzero
    · exact hs j hji
  by_contra h
  have hbound := wide_coordinate_mass_le P (by omega : P.p ≤ G i) (z i) hi
  rw [← scalar_support_one_mass P.toVITData G hpos z i hs] at hbound
  have hprime := prime_mul_mu_gt P G hG i
  have hp : (0 : ℝ) < P.p := by exact_mod_cast P.p_prime.pos
  have hlt : 2 / (P.p : ℝ) < P.toVITData.mu := by
    apply (div_lt_iff₀ hp).mpr
    linarith
  have he := P.eps_pos
  dsimp [VITData.mu] at hlt
  linarith

theorem modular_regularization_support_one (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) (i : ι) (hs : ∀ j, j ≠ i → z j = 0) :
    ModularRegularization P G z := by
  intro hG hz hm
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hgN : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hpos : ∀ j, 0 < G j := fun j => hgN.trans_le (hG.1 j)
  have hi : z i ≠ 0 := by
    intro hzero
    apply hz
    ext j
    by_cases hji : j = i
    · subst j; exact hzero
    · exact hs j hji
  have hwidth := support_one_width_lt P G z i hs hG hz hm
  have hinj : Function.Injective (fun k : Fin (G i) => z i * ((k : ℕ) : ZMod P.p)) := by
    intro a b hab
    have hc := mul_left_cancel₀ hi hab
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ P.p).mp hc
    apply Fin.ext
    simpa only [Nat.mod_eq_of_lt (a.isLt.trans hwidth),
      Nat.mod_eq_of_lt (b.isLt.trans hwidth)] using hmod
  have hmass : mass G (scalar G z) = 1 / (G i : ℝ) := by
    rw [scalar_support_one_mass P.toVITData G hpos z i hs]
    simpa only [Fintype.card_fin] using atomMass_of_injective _ (⟨0, hpos i⟩ : Fin (G i)) hinj
  have hg : (0 : ℝ) < P.g := by exact_mod_cast hgN
  have hmu : 0 < P.toVITData.mu := P.eps_pos.trans P.eps_lt_mu
  have hgi : (P.g : ℝ) ≤ G i := by exact_mod_cast hG.1 i
  have hrecip : 1 / (G i : ℝ) ≤ (P.g : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hg hgi
  have hmug : P.toVITData.mu < (P.g : ℝ)⁻¹ := by
    rw [hmass] at hm
    have he := P.eps_pos
    dsimp [VITData.mu]
    linarith
  have hC : 1 ≤ P.C1 := by
    by_contra h
    have hpow : P.C1^(P.L0 - 1) ≤ 1 := pow_le_one₀ P.C1_pos.le (by linarith)
    have hratio : 1 < (P.g : ℝ)⁻¹ / P.toVITData.mu := (one_lt_div hmu).mpr hmug
    linarith [P.C1_power]
  have hreg : Regular P.toVITData G (coordinateLattice i) := by
    simp only [Regular, coordinateLattice_mass i G hpos, coordinateLattice_height,
      Nat.cast_one, mul_one, VITData.C, reduceIte, pow_one]
    exact hrecip.trans (by simpa only [one_div] using div_le_div_of_nonneg_right hC hg.le)
  refine ⟨1, coordinateLattice i, by decide, by decide,
    coordinateLattice_redSpan i z hs, hreg, ?_⟩
  rw [hmass, coordinateLattice_mass i G hpos]
  exact sub_le_self _ (mul_nonneg (by norm_num) P.eps_pos.le)

theorem reindexLattice_mass (e : ι ≃ κ) {d : ℕ} (L : IntLat ι d)
    (G : ι → ℕ) :
    (reindexLattice e L).mZ (G ∘ e.symm) = L.mZ G := by
  let E : Grid G ≃ Grid (G ∘ e.symm) := Equiv.piCongrLeft' (fun i => Fin (G i)) e
  have h : (imageZ (G ∘ e.symm) (reindexLattice e L).matrix) ∘ E =
      imageZ G L.matrix := by
    funext r j
    change (∑ k, L.matrix (e.symm k) j * ((E r k : ℕ) : ℤ)) = _
    simpa [E, imageZ] using
      (Equiv.sum_comp e.symm (fun i => L.matrix i j * ((r i : ℕ) : ℤ)))
  exact (mass_precomp_equiv E _).symm.trans (congrArg Algebra.FiniteProbability.atomMass h)

theorem scalar_mass_reindex (e : ι ≃ κ) (P : VITData)
    (G : ι → ℕ) (z : ι → ZMod P.p) :
    mass (G ∘ e.symm) (scalar (G ∘ e.symm) (z ∘ e.symm)) =
      mass G (scalar G z) := by
  let E : Grid G ≃ Grid (G ∘ e.symm) := Equiv.piCongrLeft' (fun i => Fin (G i)) e
  have h : (scalar (G ∘ e.symm) (z ∘ e.symm)) ∘ E = scalar G z := by
    funext r
    simpa [E, scalar, Function.comp_def] using
      (Equiv.sum_comp e.symm (fun i => z i * ((r i : ℕ) : ZMod P.p)))
  exact (mass_precomp_equiv E _).symm.trans (congrArg Algebra.FiniteProbability.atomMass h)

theorem reindexLattice_redSpan (e : ι ≃ κ) {p d : ℕ} (L : IntLat ι d)
    {z : ι → ZMod p} (hz : z ∈ redSpan p L) :
    z ∘ e.symm ∈ redSpan p (reindexLattice e L) := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨w ∘ e.symm, ?_, rfl⟩
    exact ⟨w, hw, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

theorem regularWitness_reindex (e : ι ≃ κ) (P : VITData)
    (G : ι → ℕ) (z : ι → ZMod P.p) {d : ℕ} (L : IntLat ι d)
    (h : RegularWitness P G z d L) :
    RegularWitness P (G ∘ e.symm) (z ∘ e.symm) d (reindexLattice e L) := by
  rcases h with ⟨hd, hd3, hz, hreg, hmass⟩
  refine ⟨hd, hd3, reindexLattice_redSpan e L hz, ?_, ?_⟩
  · simpa only [Regular, reindexLattice_mass, reindexLattice_height] using hreg
  · simpa only [scalar_mass_reindex, reindexLattice_mass] using hmass

theorem gridBudget_reindex (e : ι ≃ κ) (P : VITData) (G : ι → ℕ)
    (h : GridBudget P G) : GridBudget P (G ∘ e.symm) := by
  refine ⟨fun i => h.1 _, ?_, fun i => h.2.2 _⟩
  change (∑ i, (G (e.symm i) : ℝ)^2) ≤ _
  exact (Equiv.sum_comp e.symm (fun i => (G i : ℝ)^2)).le.trans h.2.1

theorem gridBudget_old (P : VITData) (G : ι → ℕ) (Gx : ℕ)
    (h : GridBudget P (extend G Gx)) : GridBudget P G := by
  refine ⟨fun i => h.1 (some i), ?_, fun i => h.2.2 (some i)⟩
  have hs := h.2.1
  simp only [Fintype.sum_option, extend, Option.elim] at hs
  nlinarith [sq_nonneg (Gx : ℝ)]

theorem scalar_mass_extend_le (P : VITData) (G : ι → ℕ) (Gx : ℕ)
    (z : ι → ZMod P.p) (a : ZMod P.p) (hx : 0 < Gx) :
    mass (extend G Gx) (scalar (extend G Gx) (extend z a)) ≤
      mass G (scalar G z) := by
  let E : Grid (extend G Gx) ≃ Fin Gx × Grid G := Equiv.piOptionEquivProd
  let f := scalar (extend G Gx) (extend z a)
  have hE : Algebra.FiniteProbability.atomMass (f ∘ E.symm) = Algebra.FiniteProbability.atomMass f :=
    mass_precomp_equiv E.symm f
  rw [mass, ← hE]
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  rw [Algebra.FiniteProbability.pointProb_prod]
  have hxR : (0 : ℝ) < Fintype.card (Fin Gx) := by simpa using (Nat.cast_pos.mpr hx : (0 : ℝ) < Gx)
  apply (div_le_iff₀ hxR).mpr
  have hb : ∀ x : Fin Gx,
      Algebra.FiniteProbability.pointProb (fun r : Grid G => (f ∘ E.symm) (x, r)) t ≤
        mass G (scalar G z) := by
    intro x
    apply (Algebra.FiniteProbability.pointProb_mono _ (scalar G z) t
      (t - a * ((x : ℕ) : ZMod P.p)) ?_).trans
      (Algebra.FiniteProbability.pointProb_le_mass _ _)
    intro r hr
    change scalar (extend G Gx) (extend z a) (E.symm (x, r)) = t at hr
    simp only [scalar, Fintype.sum_option, extend, Option.elim,
      E] at hr
    exact eq_sub_of_add_eq' hr
  calc
    _ ≤ ∑ _x : Fin Gx, mass G (scalar G z) := sum_le_sum (fun x _ => hb x)
    _ = _ := by simp [mul_comm]

theorem modularRegularization_reindex (e : ι ≃ κ) (P : VITParameters)
    (G : ι → ℕ) (z : ι → ZMod P.p)
    (h : ModularRegularization P G z) :
    ModularRegularization P (G ∘ e.symm) (z ∘ e.symm) := by
  intro hG hz hm
  have hG' : GridBudget P.toVITData G := by
    simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using
      gridBudget_reindex e.symm P.toVITData (G ∘ e.symm) hG
  have hz' : z ≠ 0 := by
    intro hzero
    apply hz
    subst z
    rfl
  have hm' : P.theta0 < mass G (scalar G z) := by
    simpa only [scalar_mass_reindex] using hm
  obtain ⟨d, L, hL⟩ := h hG' hz' hm'
  exact ⟨d, reindexLattice e L, regularWitness_reindex e P.toVITData G z L hL⟩

set_option maxHeartbeats 800000 in

theorem modular_regularization_of_base_step (P : VITParameters)
    (hbase : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (G : α → ℕ) (z : α → ZMod P.p) (i : α),
      (∀ j, j ≠ i → z j = 0) → ModularRegularization P G z)
    (hstep : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (G : α → ℕ) (Gx : ℕ) (z : α → ZMod P.p) (a : ZMod P.p),
      ModStep P G Gx z a)
    (α : Type u) [Fintype α] [DecidableEq α]
    (G : α → ℕ) (z : α → ZMod P.p) : ModularRegularization P G z := by
  classical
  have hall : ∀ (α : Type u) [Fintype α],
      ∀ [DecidableEq α] (G : α → ℕ) (z : α → ZMod P.p),
        ModularRegularization P G z := by
    apply Fintype.induction_empty_option
    · intro A B _ e ih _ G z
      letI : Fintype A := Fintype.ofEquiv B e.symm
      have hi := @ih (Classical.decEq A) (G ∘ e) (z ∘ e)
      simpa only [Function.comp_def, Equiv.apply_symm_apply] using
        modularRegularization_reindex e P (G ∘ e) (z ∘ e) hi
    · intro _ G z _ hz _
      exact (hz (by ext i; exact PEmpty.elim i)).elim
    · intro A _ ih dopt
      letI : DecidableEq A := Classical.decEq A
      have hdopt : dopt = @Option.instDecidableEq A (Classical.decEq A) :=
        Subsingleton.elim _ _
      subst dopt
      intro G z hG hz hm
      let G' : A → ℕ := fun i => G (some i)
      let z' : A → ZMod P.p := fun i => z (some i)
      have hGeq : extend G' (G none) = G := by ext i; cases i <;> rfl
      have hzeq : extend z' (z none) = z := by ext i; cases i <;> rfl
      by_cases hold : z' = 0
      · apply hbase (Option A) G z none ?_ hG hz hm
        intro j hj
        cases j with
        | none => exact (hj rfl).elim
        | some i => exact congrFun hold i
      · have hGext : GridBudget P.toVITData (extend G' (G none)) := by
          simpa only [hGeq] using hG
        have hmext : P.theta0 <
            mass (extend G' (G none)) (scalar (extend G' (G none)) (extend z' (z none))) := by
          have heq := congrArg (fun H => mass H (scalar H (extend z' (z none)))) hGeq
          rw [heq, hzeq]
          exact hm
        have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
        have hx : 0 < G none := hg.trans_le (hG.1 none)
        have hmold : P.theta0 < mass G' (scalar G' z') :=
          hmext.trans_le (scalar_mass_extend_le P.toVITData G' (G none) z' (z none) hx)
        obtain ⟨d, L, hL⟩ := ih G' z' (gridBudget_old P.toVITData G' (G none) hGext)
          hold hmold
        have hout := hstep A G' (G none) z' (z none) hGext hold hmext d L hL
        simpa only [hGeq, hzeq] using hout
  exact hall α G z

theorem modular_regularization_of_step (P : VITParameters)
    (hstep : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (G : α → ℕ) (Gx : ℕ) (z : α → ZMod P.p) (a : ZMod P.p), ModStep P G Gx z a)
    (α : Type u) [Fintype α] [DecidableEq α]
    (G : α → ℕ) (z : α → ZMod P.p) : ModularRegularization P G z :=
  modular_regularization_of_base_step P
    (fun _ _ _ G z i hs => modular_regularization_support_one P G z i hs) hstep α G z

theorem grid_directional_mgf_proved {d : ℕ} (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin d) ℝ) :
    Analysis.DirectionalMGF (Analysis.gridLaw G hG) (Analysis.gridImage G B)
      ((Analysis.gridLaw G hG).mean (Analysis.gridImage G B))
      (Analysis.gridCovariance G B) := by
  intro u
  rw [Algebra.Trim.grid_directional_moment, Algebra.Trim.grid_covariance_direction, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    unfold Algebra.Trim.uniformGridMoment
    exact div_nonneg (sum_nonneg (fun k _ => (Real.exp_pos _).le)) (Nat.cast_nonneg _)
  · intro i _
    exact Algebra.Trim.uniform_grid_mgf Algebra.Trim.sinhDivLeExp (G i) (hG i) ((B *ᵥ u) i)

theorem gridCovariance_posDef_any {d : ℕ} (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin d) ℤ) (hB : LinearIndependent ℤ B.col) :
    (Analysis.gridCovariance G (B.map (Int.castRingHom ℝ))).PosDef := by
  let C := B.map (Int.castRingHom ℝ)
  have hreal : LinearIndependent ℝ C.col := by
    have h := (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (v := B.col)).mpr hB
    exact h
  have hC : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.mpr hreal
  have hD : (Matrix.diagonal (fun i => (G i : ℝ)^2 / 12)).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    have hi : (0 : ℝ) < G i := by exact_mod_cast hG i
    positivity
  have hgram : Analysis.gridCovariance G C =
      Cᴴ * Matrix.diagonal (fun i => (G i : ℝ)^2 / 12) * C := by
    rw [Algebra.Trim.grid_covariance_matrix]
    simp
  rw [hgram]
  exact hD.conjTranspose_mul_mul_same hC

def oldStepMatrix {d : ℕ} (B : Matrix ι (Fin d) ℤ) :
    Matrix (Option ι) (Fin d) ℤ := fun i j => i.elim 0 (fun k => B k j)

theorem oldStepMatrix_covariance {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) :
    Analysis.gridCovariance (extend G Gx) ((oldStepMatrix B).map (Int.castRingHom ℝ)) =
      Analysis.gridCovariance G (B.map (Int.castRingHom ℝ)) := by
  ext j k
  simp [Analysis.gridCovariance, Fintype.sum_option, oldStepMatrix, extend]

theorem oldStepMatrix_image {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) :
    Analysis.gridImage (extend G Gx) ((oldStepMatrix B).map (Int.castRingHom ℝ)) r =
      fun j => (stepImage G Gx B r (some j) : ℝ) := by
  ext j
  simp [Analysis.gridImage, stepImage, stepMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_option, oldStepMatrix, extend, Int.cast_sum, Int.cast_mul]

theorem oldStepMatrix_center {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (hG : ∀ i, 0 < extend G Gx i) :
    (Analysis.gridLaw (extend G Gx) hG).mean
      (Analysis.gridImage (extend G Gx) ((oldStepMatrix B).map (Int.castRingHom ℝ))) =
      imageCenter G B := by
  ext j
  rw [Algebra.Trim.grid_mean]
  simp [Fintype.sum_option, oldStepMatrix, extend, imageCenter]

theorem gridLaw_prob_density {α : Type*} [Fintype α] [DecidableEq α]
    (G : α → ℕ) (hG : ∀ i, 0 < G i) (E : Set (Grid G)) :
    (Analysis.gridLaw G hG).prob E =
      Algebra.Mod.Definitions.density (by classical exact univ.filter fun r => r ∈ E) := by
  classical
  simp only [Analysis.FiniteLaw.prob, Analysis.gridLaw, Analysis.FiniteLaw.uniform,
    Algebra.Mod.Definitions.density, ← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv,
    one_mul]

theorem exists_current_trimmed_fibre (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (z : ι → ZMod P.p) (a : ZMod P.p)
    (L : IntLat ι d) (hG : GridBudget P.toVITData (extend G Gx)) (hz : z ≠ 0)
    (hm : P.theta0 < mass (extend G Gx) (scalar (extend G Gx) (extend z a)))
    (hW : RegularWitness P.toVITData G z d L) :
    ∃ (c : Option (Fin d) → ZMod P.p) (t : ZMod P.p)
      (F : Finset (Grid (extend G Gx))),
      c ≠ 0 ∧ pullMod L.matrix c = extend z a ∧ F.Nonempty ∧
      (∀ r ∈ F, scalar (extend G Gx) (extend z a) r = t) ∧
      (∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t) ∧
      Trimmed P.toVITData G Gx L.matrix F ∧
      mass (extend G Gx) (scalar (extend G Gx) (extend z a)) - P.eps ≤
        Algebra.Mod.Definitions.density F ∧
      P.toVITData.mu ≤ Algebra.Mod.Definitions.density F := by
  classical
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hpos : ∀ i, 0 < extend G Gx i := fun i => hg.trans_le (hG.1 i)
  obtain ⟨c, hc, hcz⟩ := exists_step_congruence L z a hW.2.2.1 hz
  obtain ⟨t, F₀, _, hf₀, hden₀⟩ := largest_scalar_fibre P (extend G Gx) (extend z a) hG hm
  have hB : LinearIndependent ℤ (oldStepMatrix L.matrix).col := by
    let f : (Option ι → ℤ) →ₗ[ℤ] (ι → ℤ) :=
      { toFun := fun x i => x (some i), map_add' := by intros; rfl,
        map_smul' := by intros; rfl }
    apply LinearIndependent.of_comp f
    exact L.basis.linearIndependent.map' L.carrier.subtype (Submodule.ker_subtype _)
  let T : Analysis.GridImage d (extend G Gx)
      ((oldStepMatrix L.matrix).map (Int.castRingHom ℝ)) :=
    ⟨hpos, gridCovariance_posDef_any (extend G Gx) hpos (oldStepMatrix L.matrix) hB⟩

  have htrim := Praxis.Lift.GridImage.event_trim T ⟨hW.1, hW.2.1⟩
    (grid_directional_mgf_proved (extend G Gx) hpos _) P.trim.2
  let F := univ.filter fun r => r ∈ F₀ ∧ r ∈ T.ellipsoid P.R
  have hprob := htrim (F₀ : Set (Grid (extend G Gx)))
  simp only [Analysis.GridImage.law] at hprob
  rw [gridLaw_prob_density, gridLaw_prob_density] at hprob
  have hmass : mass (extend G Gx) (scalar (extend G Gx) (extend z a)) - P.eps ≤
      Algebra.Mod.Definitions.density F := by
    simpa [F, Set.mem_inter_iff, ← hden₀] using hprob
  have hmu : P.toVITData.mu ≤ Algebra.Mod.Definitions.density F := by
    dsimp [VITData.mu]
    linarith [P.eps_pos]
  have hne : F.Nonempty := by
    by_contra hn
    have he : Algebra.Mod.Definitions.density F = 0 := by
      simp [not_nonempty_iff_eq_empty.mp hn, Algebra.Mod.Definitions.density]
    have hp := P.eps_pos.trans P.eps_lt_mu
    linarith
  refine ⟨c, t, F, hc, hcz, hne, ?_, ?_, ?_, hmass, hmu⟩
  · intro r hr
    exact hf₀ r (mem_filter.mp hr).2.1
  · intro r hr
    rw [← scalar_pullMod, hcz]
    exact hf₀ r (mem_filter.mp hr).2.1
  · intro r hr
    have ht := (mem_filter.mp hr).2.2
    change Analysis.mahalanobisSq _ T.center _ ≤ P.R^2 at ht
    rw [Analysis.GridImage.center, Analysis.GridImage.law,
      oldStepMatrix_center, oldStepMatrix_covariance, oldStepMatrix_image] at ht
    exact ht

open scoped RealInnerProductSpace

theorem coordinate_sq_le_mahalanobis {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) (m x : Fin d → ℝ) (j : Fin d) :
    (x j - m j)^2 ≤ S j j * Analysis.mahalanobisSq S m x := by
  letI : SeminormedAddCommGroup (Fin d → ℝ) := S.toSeminormedAddCommGroup hS.posSemidef
  letI : InnerProductSpace ℝ (Fin d → ℝ) := S.toInnerProductSpace hS.posSemidef
  let v : Fin d → ℝ := Pi.single j 1
  let u := S⁻¹ *ᵥ (x - m)
  have hcancel : S *ᵥ u = x - m := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hS.det_pos.ne'),
      Matrix.one_mulVec]
  have hin (a b : Fin d → ℝ) : ⟪a, b⟫ = a ⬝ᵥ (S *ᵥ b) := by
    change (S *ᵥ b) ⬝ᵥ star a = _
    simp [dotProduct_comm]
  have h := real_inner_mul_inner_self_le v u
  simp only [hin, hcancel] at h
  have hcross : v ⬝ᵥ (x - m) = x j - m j := by simp [v]
  have hdiag : v ⬝ᵥ (S *ᵥ v) = S j j := by
    simp only [v, Matrix.mulVec_single_one, single_dotProduct, Matrix.col_apply, one_mul]
  rw [hcross, hdiag] at h
  simpa [pow_two, u, Analysis.mahalanobisSq, dotProduct_comm] using h

theorem covariance_diagonal_bound (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (L : IntLat ι d) (hG : GridBudget P.toVITData G) (j : Fin d) :
    12 * Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) j j ≤
      (maxAbs (L.basis j : ι → ℤ) : ℝ)^2 * (P.g : ℝ)^2 * P.S := by
  let n : ℝ := maxAbs (L.basis j : ι → ℤ)
  have hentry (i : ι) : |(L.matrix i j : ℝ)| ≤ n := by
    have hi : (L.matrix i j).natAbs ≤ maxAbs (L.basis j : ι → ℤ) :=
      Finset.le_sup (f := fun i => ((L.basis j : ι → ℤ) i).natAbs) (mem_univ i)
    have hiR : ((L.matrix i j).natAbs : ℝ) ≤ (maxAbs (L.basis j : ι → ℤ) : ℝ) :=
      by exact_mod_cast hi
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hiR
  have hsum : (∑ i, (G i : ℝ)^2 * (L.matrix i j : ℝ)^2) ≤
      (∑ i, (G i : ℝ)^2) * n^2 := by
    rw [sum_mul]
    apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr (hentry i)
  calc
    _ = ∑ i, (G i : ℝ)^2 * (L.matrix i j : ℝ)^2 := by
      simp only [Analysis.gridCovariance, Matrix.map_apply, Int.coe_castRingHom,
        mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ (∑ i, (G i : ℝ)^2) * n^2 := hsum
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_right hG.2.1 (sq_nonneg n)
      dsimp [n] at *
      nlinarith only [hb]

theorem trimmed_coordinate_bound (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι d)
    (hG : GridBudget P.toVITData (extend G Gx))
    (F : Finset (Grid (extend G Gx))) (ht : Trimmed P.toVITData G Gx L.matrix F)
    (r : Grid (extend G Gx)) (hr : r ∈ F) (j : Fin d) :
    |(stepImage G Gx L.matrix r (some j) : ℝ) - imageCenter G L.matrix j| ≤
      Real.sqrt P.toVITData.T2 * (maxAbs (L.basis j : ι → ℤ) : ℝ) / 2 := by
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hp : ∀ i, 0 < G i := fun i => hg.trans_le (hG.1 (some i))
  have hLI : LinearIndependent ℤ L.matrix.col :=
    L.basis.linearIndependent.map' L.carrier.subtype (Submodule.ker_subtype _)
  have hSigma := gridCovariance_posDef_any G hp L.matrix hLI
  have hdiag : 0 ≤ Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) j j :=
    hSigma.posSemidef.diag_nonneg
  have hcoord := coordinate_sq_le_mahalanobis _ hSigma (imageCenter G L.matrix)
    (fun k => (stepImage G Gx L.matrix r (some k) : ℝ)) j
  have hpoint := mul_le_mul_of_nonneg_left (ht r hr) hdiag
  have hcov := covariance_diagonal_bound P G L (gridBudget_old P.toVITData G Gx hG) j
  have hcovR := mul_le_mul_of_nonneg_left hcov (sq_nonneg P.R)
  have hT : 0 ≤ P.toVITData.T2 := by
    have hS := P.S_pos
    unfold VITData.T2
    positivity
  have hs := Real.sq_sqrt hT
  have hn : (0 : ℝ) ≤ maxAbs (L.basis j : ι → ℤ) := Nat.cast_nonneg _
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  have hform : 4 * P.R^2 *
      Analysis.gridCovariance G (L.matrix.map (Int.castRingHom ℝ)) j j ≤
      P.toVITData.T2 * (maxAbs (L.basis j : ι → ℤ) : ℝ)^2 := by
    unfold VITData.T2
    nlinarith only [hcovR]
  nlinarith only [hcoord, hpoint, hform,
    show (Real.sqrt P.toVITData.T2 * (maxAbs (L.basis j : ι → ℤ) : ℝ) / 2)^2 =
      P.toVITData.T2 * (maxAbs (L.basis j : ι → ℤ) : ℝ)^2 / 4 by
        rw [div_pow, mul_pow, hs]; ring]

theorem trimmed_difference_bounds (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (L : IntLat ι d)
    (hG : GridBudget P.toVITData (extend G Gx))
    (F : Finset (Grid (extend G Gx))) (ht : Trimmed P.toVITData G Gx L.matrix F) :
    (∀ j k, |(imageDifferences (stepImage G Gx L.matrix) F (some j) k : ℝ)| ≤
      Real.sqrt P.toVITData.T2 * (maxAbs (L.basis j : ι → ℤ) : ℝ)) ∧
    (∀ k, |(imageDifferences (stepImage G Gx L.matrix) F none k : ℝ)| ≤
      Real.sqrt P.toVITData.T2) := by
  constructor
  · intro j k
    have h₁ := trimmed_coordinate_bound P G Gx L hG F ht k.1.val k.1.property j
    have h₂ := trimmed_coordinate_bound P G Gx L hG F ht k.2.val k.2.property j
    have ha := abs_sub_le (stepImage G Gx L.matrix k.1.val (some j) : ℝ)
      (imageCenter G L.matrix j) (stepImage G Gx L.matrix k.2.val (some j) : ℝ)
    rw [abs_sub_comm (imageCenter G L.matrix j)] at ha
    change |((stepImage G Gx L.matrix k.1.val (some j) -
      stepImage G Gx L.matrix k.2.val (some j) : ℤ) : ℝ)| ≤ _
    rw [Int.cast_sub]
    linarith
  · intro k
    have hnone (r : Grid (extend G Gx)) : stepImage G Gx L.matrix r none = ((r none : ℕ) : ℤ) := by
      simp [stepImage, stepMatrix, Matrix.mulVec, dotProduct, Fintype.sum_option]
    have hT : (Gx : ℝ)^2 ≤ P.toVITData.T2 := (hG.2.2 none).le
    have hwidth : (Gx : ℝ) ≤ Real.sqrt P.toVITData.T2 :=
      Real.le_sqrt_of_sq_le hT
    have h₁ : (0 : ℝ) ≤ ((k.1.val none : ℕ) : ℝ) := Nat.cast_nonneg _
    have h₂ : (0 : ℝ) ≤ ((k.2.val none : ℕ) : ℝ) := Nat.cast_nonneg _
    have h₃ : ((k.1.val none : ℕ) : ℝ) ≤ Gx := by exact_mod_cast (k.1.val none).isLt.le
    have h₄ : ((k.2.val none : ℕ) : ℝ) ≤ Gx := by exact_mod_cast (k.2.val none).isLt.le
    change |((stepImage G Gx L.matrix k.1.val none -
      stepImage G Gx L.matrix k.2.val none : ℤ) : ℝ)| ≤ _
    rw [Int.cast_sub, hnone, hnone, Int.cast_natCast, Int.cast_natCast]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem saturation_radius_bounds (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (hG : GridBudget P.toVITData (extend G Gx)) :
    1 ≤ Real.sqrt P.toVITData.T2 ∧ (Real.sqrt P.toVITData.T2)^2 ≤ P.toVITData.T2 := by
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hx : 1 ≤ Gx := hg.trans_le (hG.1 none)
  have hxR : (1 : ℝ) ≤ Gx := by exact_mod_cast hx
  have hb := hG.2.2 none
  change (Gx : ℝ)^2 < P.toVITData.T2 at hb
  have hT : 1 ≤ P.toVITData.T2 := by nlinarith
  exact ⟨Real.one_le_sqrt.mpr hT, (Real.sq_sqrt (by linarith)).le⟩

theorem exists_step_preparation (P : VITParameters) {d : ℕ}
    (G : ι → ℕ) (Gx : ℕ) (z : ι → ZMod P.p) (a : ZMod P.p)
    (L : IntLat ι d) (hG : GridBudget P.toVITData (extend G Gx)) (hz : z ≠ 0)
    (hm : P.theta0 < mass (extend G Gx) (scalar (extend G Gx) (extend z a)))
    (hW : RegularWitness P.toVITData G z d L)
    (h3 : ∀ N : IntLat ι 3, Algebra.Reg.Definitions.Rank3Height P G N) :
    ∃ (b : Basis (Fin d) ℤ L.carrier) (c : Option (Fin d) → ZMod P.p)
      (t : ZMod P.p) (F : Finset (Grid (extend G Gx))),
      RegularWitness P.toVITData G z d (rebase L b) ∧
      (∀ j, 1 ≤ maxAbs (b j : ι → ℤ)) ∧
      (∏ j, (maxAbs (b j : ι → ℤ) : ℝ)) ≤ basisConstant d * heightBound P.toVITData d ∧
      c ≠ 0 ∧ pullMod (rebase L b).matrix c = extend z a ∧ F.Nonempty ∧
      (∀ r ∈ F, scalar (extend G Gx) (extend z a) r = t) ∧
      (∀ r ∈ F, ∑ i, c i * (stepImage G Gx (rebase L b).matrix r i : ZMod P.p) = t) ∧
      Trimmed P.toVITData G Gx (rebase L b).matrix F ∧
      mass (extend G Gx) (scalar (extend G Gx) (extend z a)) - P.eps ≤
        Algebra.Mod.Definitions.density F ∧
      P.toVITData.mu ≤ Algebra.Mod.Definitions.density F ∧
      1 ≤ Real.sqrt P.toVITData.T2 ∧ (Real.sqrt P.toVITData.T2)^2 ≤ P.toVITData.T2 ∧
      (∀ j k, |(imageDifferences (stepImage G Gx (rebase L b).matrix) F (some j) k : ℝ)| ≤
        Real.sqrt P.toVITData.T2 * (maxAbs (b j : ι → ℤ) : ℝ)) ∧
      (∀ k, |(imageDifferences (stepImage G Gx (rebase L b).matrix) F none k : ℝ)| ≤
        Real.sqrt P.toVITData.T2) := by
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hx : 0 < Gx := hg.trans_le (hG.1 none)
  have hmold := hm.trans_le (scalar_mass_extend_le P.toVITData G Gx z a hx)
  obtain ⟨b, hbpos, hbprod, hbW⟩ := exists_controlled_rebase P G z L hmold
    (gridBudget_old P.toVITData G Gx hG) hW h3
  obtain ⟨c, t, F, hc, hcz, hne, hscalar, hfibre, ht, hmass, hmu⟩ :=
    exists_current_trimmed_fibre P G Gx z a (rebase L b) hG hz hm hbW
  obtain ⟨hT, hT2⟩ := saturation_radius_bounds P G Gx hG
  obtain ⟨hrows, hnew⟩ := trimmed_difference_bounds P G Gx (rebase L b) hG F ht
  exact ⟨b, c, t, F, hbW, hbpos, hbprod, hc, hcz, hne, hscalar, hfibre, ht,
    hmass, hmu, hT, hT2, hrows, hnew⟩

theorem mod_step (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (z : ι → ZMod P.p) (a : ZMod P.p)
    (hwrap : ∀ (d : ℕ) (L : IntLat ι d) c t F,
      FullImageExclusion d P G Gx L c t F)
    (hpb : ∀ (d : ℕ) (L : IntLat ι d)
      (E : Submodule ℤ (Option (Fin d) → ℤ)) (c : Option (Fin d) → ZMod P.p),
      ModPullback L E c)
    (h3old : ∀ L : IntLat ι 3, Rank3Height P G L)
    (h3 : ∀ L : IntLat (Option ι) 3, Rank3Height P (extend G Gx) L)
    (h2 : ∀ L : IntLat (Option ι) 2, Regularize2 P (extend G Gx) L)
    (h1 : ∀ L : IntLat (Option ι) 1, Regularize1 P (extend G Gx) L) :
    ModStep P G Gx z a := by
  intro hG hz hm d L hW
  obtain ⟨b, c, t, F, hbW, hn, hprod, hc, hcz, hne, _, hfibre, ht,
    hretain, _, hT, hT2, hrows, hnew⟩ :=
    exists_step_preparation P G Gx z a L hG hz hm hW h3old
  have hsmall := Algebra.Mod.SatApp.saturationApplication d P
    (fun j => maxAbs (b j : ι → ℤ)) (Real.sqrt P.toVITData.T2)
    (imageDifferences (stepImage G Gx (rebase L b).matrix) F)
    hbW.1 hbW.2.1 hn hprod hT hT2 hrows hnew
  exact regularWitness_of_small_trimmed_fibre P G Gx (rebase L b) c
    (extend z a) t F hbW.1 hbW.2.1 hG hm hbW.2.2.2.1 hc hne hfibre ht
    hretain hcz.symm (fun e he I J => (hsmall e he I J).2)
    (hwrap d (rebase L b) c t F) (fun E => hpb d (rebase L b) E c) h3 h2 h1

theorem modular_regularization (P : VITParameters)
    (hwrap : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (d : ℕ) (G : α → ℕ) (Gx : ℕ) (L : IntLat α d) c t F,
      FullImageExclusion d P G Gx L c t F)
    (hpb : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (d : ℕ) (L : IntLat α d) (E : Submodule ℤ (Option (Fin d) → ℤ))
      (c : Option (Fin d) → ZMod P.p), ModPullback L E c)
    (h3 : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (G : α → ℕ) (L : IntLat α 3), Rank3Height P G L)
    (h2 : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (G : α → ℕ) (L : IntLat α 2), Regularize2 P G L)
    (h1 : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (G : α → ℕ) (L : IntLat α 1), Regularize1 P G L)
    (α : Type u) [Fintype α] [DecidableEq α]
    (G : α → ℕ) (z : α → ZMod P.p) : ModularRegularization P G z := by
  apply modular_regularization_of_step P ?_ α G z
  intro β _ _ H Hx w a
  exact mod_step P H Hx w a
    (fun d L c t F => hwrap β d H Hx L c t F)
    (fun d L E c => hpb β d L E c)
    (h3 β H) (h3 (Option β) (extend H Hx))
    (h2 (Option β) (extend H Hx)) (h1 (Option β) (extend H Hx))

end Algebra.Mod.Induct

end Praxis.Lift
