import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Combinatorics.Chain
import Praxis.Lift.Record
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.DifferenceLattice.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.IntegerLift
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem grid_lower_pos (P : VITParameters) : 0 < P.g :=
  lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) _) P.g_lower

theorem threshold_pos (P : VITParameters) : 0 < P.toVITData.mu :=
  P.eps_pos.trans P.eps_lt_mu

theorem mass_nonneg {d : ℕ} (G : ι → ℕ) (L : IntLat ι d) :
    0 ≤ L.mZ G :=
  (Algebra.FiniteProbability.pointProb_nonneg (imageZ G L.matrix) 0).trans
    (Algebra.FiniteProbability.pointProb_le_mass (imageZ G L.matrix) 0)

theorem rank2_slack (P : VITParameters) {m : ℝ}
    (hm : P.theta0 - 30 * P.eps ≤ m) :
    P.toVITData.mu + 70 * P.eps ≤ m ∧
      P.toVITData.mu < m - 2 * P.eps := by
  dsimp [VITData.mu]
  constructor <;> linarith [P.eps_pos]

theorem moment_bound {n : ℕ} {x m mu B Q : ℝ}
    (hmu : 0 < mu) (hx : 0 ≤ x) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hxB : x ≤ B) (hratio : m / mu ≤ Q ^ n) :
    x ^ n * m ≤ (B * Q) ^ n * mu := by
  have hstart : m ≤ mu * Q ^ n := by
    have hh := (div_le_iff₀ hmu).mp hratio
    linarith
  calc
    x ^ n * m ≤ B ^ n * m :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxB _) hm
    _ ≤ B ^ n * (mu * Q ^ n) :=
      mul_le_mul_of_nonneg_left hstart (pow_nonneg hB _)
    _ = (B * Q) ^ n * mu := by rw [mul_pow]; ring

theorem moment_mono {n : ℕ} {m m0 H : ℝ}
    (hm : 0 ≤ m) (hH : 0 ≤ H) (hmono : m ≤ m0) :
    (m * H) ^ n * m ≤ (m0 * H) ^ n * m0 := by
  have hm0 : 0 ≤ m0 := hm.trans hmono
  exact mul_le_mul
    (pow_le_pow_left₀ (mul_nonneg hm hH) (mul_le_mul_of_nonneg_right hmono hH) _)
    hmono hm (pow_nonneg (mul_nonneg hm0 hH) _)

theorem initial_moment_bound (P : VITParameters) {m : ℝ}
    (hm : 0 ≤ m) (hcap : m ≤ 1 / (P.g : ℝ) ^ 2) :
    m ^ (P.L0 - 1) * m ≤
      (P.C2 / (P.g : ℝ) ^ 2) ^ (P.L0 - 1) * P.toVITData.mu := by
  have hmu := threshold_pos P
  have hr : m / P.toVITData.mu ≤ P.C2 ^ (P.L0 - 1) := by
    apply le_trans (div_le_div_of_nonneg_right hcap hmu.le)
    simpa only [zpow_neg, zpow_ofNat, one_div] using P.C2_power
  have hh := moment_bound (n := P.L0 - 1) hmu hm hm
    (by positivity : (0 : ℝ) ≤ 1 / (P.g : ℝ) ^ 2) hcap hr
  convert hh using 1
  ring

theorem return_moment_bound (P : VITParameters) {m H : ℝ}
    (hm : 0 ≤ m) (hH : 0 ≤ H)
    (hbound : m * H ≤ P.A * P.D * P.C3 / (P.g : ℝ) ^ 2)
    (hcap : m ≤ (P.g : ℝ) ^ (-(3 : ℤ)) + P.eps) :
    (m * H) ^ (P.L0 - 1) * m ≤
      (P.C2 / (P.g : ℝ) ^ 2) ^ (P.L0 - 1) * P.toVITData.mu := by
  have hmu := threshold_pos P
  have hB : (0 : ℝ) ≤ P.A * P.D * P.C3 / (P.g : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg P.A_pos.le P.D_pos.le) P.C3_pos.le)
      (sq_nonneg _)
  have hr := (div_le_div_of_nonneg_right hcap hmu.le).trans P.Q2_power
  have hh := moment_bound (n := P.L0 - 1) hmu (mul_nonneg hm hH) hm hB hbound hr
  have hscale : P.A * P.D * P.C3 / (P.g : ℝ) ^ 2 * P.Q2 ≤
      P.C2 / (P.g : ℝ) ^ 2 := by
    calc
      _ = (P.A * P.D * P.C3 * P.Q2) / (P.g : ℝ) ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right P.C2_recursion (sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg hB P.Q2_pos.le) hscale _) hmu.le)

theorem ordinaryFibre_density {d : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (t : Fin d → ℤ) :
    density G (ordinaryFibre G L t) = atom G (imageZ G L.matrix) t := by
  classical
  have hc : Algebra.FiniteProbability.fibreCount (imageZ G L.matrix) t =
      (ordinaryFibre G L t).card := by
    unfold Algebra.FiniteProbability.fibreCount
    congr 1
    ext r
    simp [ordinaryFibre]
  exact congrArg (fun c : ℕ => (c : ℝ) / Fintype.card (Grid G)) hc.symm

theorem largest_fibre {d : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (hG : ∀ i, 0 < G i) :
    ∃ t, atom G (imageZ G L.matrix) t = L.mZ G ∧
      (ordinaryFibre G L t).Nonempty := by
  classical
  let r0 : Grid G := fun i => ⟨0, hG i⟩
  let f := imageZ G L.matrix
  obtain ⟨r, _, hr⟩ := (univ : Finset (Grid G)).exists_max_image
    (fun s => Algebra.FiniteProbability.fibreCount f (f s)) ⟨r0, mem_univ _⟩
  refine ⟨f r, le_antisymm (Algebra.FiniteProbability.pointProb_le_mass f (f r)) ?_, ?_⟩
  · apply Algebra.FiniteProbability.atomMass_le
    intro t
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    by_cases ht : ∃ s, f s = t
    · obtain ⟨s, rfl⟩ := ht
      exact_mod_cast hr s (mem_univ _)
    · have hz : Algebra.FiniteProbability.fibreCount f t = 0 := by
        simp [Algebra.FiniteProbability.fibreCount, show ∀ s, f s ≠ t by simpa using ht]
      rw [hz]
      exact_mod_cast Nat.zero_le (Algebra.FiniteProbability.fibreCount f (f r))
  · exact ⟨r, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

theorem density_le_mass {d : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (t : Fin d → ℤ) (F : Finset (Grid G)) (hF : F ⊆ ordinaryFibre G L t) :
    density G F ≤ L.mZ G := by
  calc
    density G F ≤ density G (ordinaryFibre G L t) :=
      div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hF) (Nat.cast_nonneg _)
    _ = atom G (imageZ G L.matrix) t := ordinaryFibre_density G L t
    _ ≤ L.mZ G := Algebra.FiniteProbability.pointProb_le_mass _ _

theorem carrier_le_normals {d : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (t : Fin d → ℤ) (F : Finset (Grid G)) (hF : F ⊆ ordinaryFibre G L t) :
    L.carrier ≤ ordinaryNormals G F := by
  classical
  have hb (j : Fin d) : (L.basis j : ι → ℤ) ∈ ordinaryNormals G F := by
    let ev : (ι → ℤ) →ₗ[ℤ] ℤ :=
      (LinearMap.proj j).comp L.matrix.transpose.mulVecLin
    have he : Algebra.DifferenceLattice.differenceLattice 0 F ≤ ev.ker := by
      apply Submodule.span_le.mpr
      rintro v ⟨r, hr, s, hs, rfl⟩
      have hr' := (mem_filter.mp (hF hr)).2
      have hs' := (mem_filter.mp (hF hs)).2
      have hi := congrFun (hr'.trans hs'.symm) j
      change ev (Algebra.DifferenceLattice.ival 0 r - Algebra.DifferenceLattice.ival 0 s) = 0
      simpa only [ev, LinearMap.comp_apply, LinearMap.proj_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
        Pi.sub_apply, Algebra.DifferenceLattice.ival, Pi.zero_apply, zero_add,
        imageZ, mul_sub, sum_sub_distrib] using sub_eq_zero.mpr hi
    intro v hv
    have hh := he hv
    change ev v = 0 at hh
    simpa only [ev, LinearMap.comp_apply, LinearMap.proj_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.transpose_apply,
      dotProduct, IntLat.matrix] using hh
  intro w hw
  have he : w = ∑ j, L.basis.repr ⟨w, hw⟩ j • (L.basis j : ι → ℤ) := by
    have hh := congrArg (fun z : L.carrier => (z : ι → ℤ)) (L.basis.sum_repr ⟨w, hw⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hh.symm
  rw [he]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hb j))

theorem event_in_normal_fibre {d : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (F : Finset (Grid G)) (hF : F.Nonempty)
    (hL : L.carrier ≤ ordinaryNormals G F) :
    ∃ t, F ⊆ ordinaryFibre G L t := by
  classical
  obtain ⟨s, hs⟩ := hF
  refine ⟨imageZ G L.matrix s, ?_⟩
  intro r hr
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  ext j
  have hd : Algebra.DifferenceLattice.ival 0 r - Algebra.DifferenceLattice.ival 0 s ∈
      Algebra.DifferenceLattice.differenceLattice 0 F :=
    Submodule.subset_span ⟨r, hr, s, hs, rfl⟩
  have hn := hL (L.basis j).property _ hd
  apply sub_eq_zero.mp
  simpa [imageZ, IntLat.matrix, Algebra.DifferenceLattice.ival, mul_sub, sum_sub_distrib] using hn

theorem nonempty_of_density_pos (G : ι → ℕ) (F : Finset (Grid G))
    (hF : 0 < density G F) : F.Nonempty := by
  apply Finset.card_pos.mp
  by_contra h
  have hz : F.card = 0 := by omega
  simp [density, hz] at hF

theorem mass_le_of_fibBd {d : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (hG : ∀ i, 0 < G i) {rho : ℝ}
    (hb : Combinatorics.FibBd G (fun i => L.matrix i) univ rho) : L.mZ G ≤ rho := by
  classical
  let r0 : Grid G := fun i => ⟨0, hG i⟩
  have hden : (0 : ℝ) < Fintype.card (Grid G) := by
    let : Nonempty (Grid G) := ⟨r0⟩
    exact_mod_cast Fintype.card_pos
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  have hfib : ordinaryFibre G L t = Combinatorics.fib G (fun i => L.matrix i) univ r0 t := by
    ext r
    rw [Combinatorics.fib_univ G (fun i => L.matrix i) r0 t]
    simp only [ordinaryFibre, mem_filter, mem_univ, true_and]
    have he : (∑ i, L.matrix i * ((r i : ℕ) : Fin d → ℤ)) = imageZ G L.matrix r := by
      ext j
      simp only [imageZ, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
    rw [he]
  have hcard : ((ordinaryFibre G L t).card : ℝ) ≤
      (Fintype.card (Grid G) : ℝ) * rho := by
    rw [hfib]
    simpa [Grid, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod] using hb r0 t
  change atom G (imageZ G L.matrix) t ≤ rho
  rw [← ordinaryFibre_density G L t]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcard)

theorem mass_le_pivot {d g : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (hg : 0 < g) (hG : ∀ i, g ≤ G i) : L.mZ G ≤ 1 / (g : ℝ) ^ d := by
  classical
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hpos : ∀ i, 0 < G i := fun i => hg.trans_le (hG i)
  obtain ⟨r, hdet, _⟩ := Algebra.VectorInverse.exists_maximal_basis_minor
    L.carrier L.saturated L.basis
  have hb := (Algebra.VectorInverse.pivot_fibBd G L.matrix r hpos hdet).extend
    (subset_univ _)
  apply mass_le_of_fibBd G L hpos
  apply hb.mono
  apply one_div_le_one_div_of_le (pow_pos hgR _)
  calc
    (g : ℝ) ^ d = ∏ _j : Fin d, (g : ℝ) := by simp
    _ ≤ ∏ j : Fin d, (G (r j) : ℝ) :=
      prod_le_prod (fun _ _ => hgR.le) (fun j _ => by exact_mod_cast hG (r j))

theorem return_mass_cap (P : VITParameters) (G3 : ι → ℕ) (L3 : IntLat ι 3)
    (hG3 : GridBudget P.toVITData G3) {mOld mNew : ℝ}
    (hretain : mOld - P.eps ≤ L3.mZ G3) (hmono : mNew ≤ mOld) :
    mNew ≤ (P.g : ℝ) ^ (-(3 : ℤ)) + P.eps := by
  have hp := mass_le_pivot G3 L3 (grid_lower_pos P) hG3.1
  have hi : 1 / (P.g : ℝ) ^ 3 = (P.g : ℝ) ^ (-(3 : ℤ)) := by
    simp only [zpow_neg, zpow_ofNat, one_div]
  rw [hi] at hp
  linarith

theorem return_step_reset (P : VITParameters) {κ0 : Type*}
    [Fintype κ0] [DecidableEq κ0] (G3 : ι → ℕ) (L3 : IntLat ι 3)
    (G2 : κ0 → ℕ) (L2 : IntLat κ0 2) (trimmedDensity mOld : ℝ)
    (hrank3 : Rank3Height P G3 L3) (hG3 : GridBudget P.toVITData G3)
    (hreturn : Rank2Return P G3 L3 G2 L2 trimmedDensity)
    (hretain : mOld - P.eps ≤ L3.mZ G3) (hmono : L2.mZ G2 ≤ mOld)
    (hdomain : P.theta0 - 30 * P.eps ≤ L2.mZ G2)
    (htrim : L2.mZ G2 - P.eps ≤ trimmedDensity)
    (htransition : trimmedDensity * (L2.H : ℝ) ≤
      P.D * (P.g : ℝ) * (L3.H : ℝ) * L3.mZ G3) :
    L2.mZ G2 * (L2.H : ℝ) ≤ P.A * P.D * P.C3 / (P.g : ℝ) ^ 2 ∧
      L2.mZ G2 ≤ (P.g : ℝ) ^ (-(3 : ℤ)) + P.eps := by
  have hslack := (rank2_slack P hdomain).1
  have hheavy2 : P.toVITData.mu ≤ L2.mZ G2 := by linarith [P.eps_pos]
  have hheavy3 : P.toVITData.mu ≤ L3.mZ G3 := by linarith [P.eps_pos]
  exact ⟨hreturn hheavy2 htrim (hrank3 hG3 hheavy3).2 htransition,
    return_mass_cap P G3 L3 hG3 hretain hmono⟩

theorem normal_rank_le_three (P : VITParameters) (G : ι → ℕ)
    (F : Finset (Grid G)) (hG : GridBudget P.toVITData G)
    (hheavy : P.toVITData.mu ≤ density G F) :
    Module.finrank ℤ (ordinaryNormals G F) ≤ 3 := by
  classical
  let N := ordinaryNormals G F
  let d := Module.finrank ℤ N
  let LN : IntLat ι d := {
    carrier := N
    basis := Module.finBasis ℤ N
    saturated := Algebra.VectorInverse.normalLattice_saturated _ }
  have hF := nonempty_of_density_pos G F ((threshold_pos P).trans_le hheavy)
  obtain ⟨t, ht⟩ := event_in_normal_fibre G LN F hF le_rfl
  have hm := (density_le_mass G LN t F ht).trans
    (mass_le_pivot G LN (grid_lower_pos P) hG.1)
  by_contra hn
  have hd : 4 ≤ d := by dsimp [d, N]; omega
  have hg : (1 : ℝ) ≤ P.g := by exact_mod_cast Nat.succ_le_of_lt (grid_lower_pos P)
  have hgpos : (0 : ℝ) < P.g := by exact_mod_cast grid_lower_pos P
  have hp : 1 / (P.g : ℝ) ^ d ≤ (P.g : ℝ) ^ (-(4 : ℤ)) := by
    rw [zpow_neg, zpow_ofNat, ← one_div]
    exact one_div_le_one_div_of_le (pow_pos hgpos _) (pow_le_pow_right₀ hg hd)
  exact (not_lt_of_ge ((hheavy.trans hm).trans hp)) P.rank4_light

omit [DecidableEq ι] in

theorem saturated_eq_of_le_of_finrank_eq {d : ℕ} (L : IntLat ι d)
    (N : Submodule ℤ (ι → ℤ)) (hLN : L.carrier ≤ N)
    (hrank : Module.finrank ℤ N = d) : L.carrier = N := by
  classical
  apply le_antisymm hLN
  intro x hx
  by_contra hxL
  let v : Fin d → N := fun j => ⟨L.basis j, hLN (L.basis j).property⟩
  have hv : LinearIndependent ℤ v := by
    apply LinearIndependent.of_comp N.subtype
    exact L.basis.linearIndependent.map' L.carrier.subtype (Submodule.ker_subtype _)
  have hs : Submodule.span ℤ (Set.range v) ≤ L.carrier.comap N.subtype := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    exact (L.basis j).property
  have hli : LinearIndependent ℤ (Fin.cons (⟨x, hx⟩ : N) v) := by
    apply hv.finCons' (⟨x, hx⟩ : N) v
    intro c y hy he
    by_contra hc
    apply hxL
    apply L.saturated c hc x
    have hval : c • x + (y : ι → ℤ) = 0 := by
      simpa only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero] using
        congrArg (fun z : N => (z : ι → ℤ)) he
    rw [eq_neg_of_add_eq_zero_left hval]
    exact L.carrier.neg_mem (hs hy)
  have hc := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, hrank] at hc
  omega

theorem rank2_normal_dichotomy (P : VITParameters) (G : ι → ℕ)
    (L : IntLat ι 2) (t : Fin 2 → ℤ) (F : Finset (Grid G))
    (hG : GridBudget P.toVITData G) (hF : F ⊆ ordinaryFibre G L t)
    (hheavy : P.toVITData.mu ≤ density G F) :
    ordinaryNormals G F = L.carrier ∨ Module.finrank ℤ (ordinaryNormals G F) = 3 := by
  have hLN := carrier_le_normals G L t F hF
  have hlow := (Submodule.inclusion hLN).finrank_le_finrank_of_injective
    (Submodule.inclusion_injective hLN)
  have hLdim : Module.finrank ℤ L.carrier = 2 := by
    simpa using Module.finrank_eq_card_basis L.basis
  rw [hLdim] at hlow
  have hhigh := normal_rank_le_three P G F hG hheavy
  by_cases hdim : Module.finrank ℤ (ordinaryNormals G F) = 2
  · exact Or.inl (saturated_eq_of_le_of_finrank_eq L _ hLN hdim).symm
  · exact Or.inr (by omega)

theorem unit_normal_of_fixed (G : ι → ℕ) (F : Finset (Grid G)) (i : ι) (a : ℤ)
    (hfixed : ∀ r ∈ F, ((r i : ℕ) : ℤ) = a) :
    Pi.single i 1 ∈ ordinaryNormals G F := by
  classical
  let ev : (ι → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj i
  have he : Algebra.DifferenceLattice.differenceLattice 0 F ≤ ev.ker := by
    apply Submodule.span_le.mpr
    rintro v ⟨r, hr, s, hs, rfl⟩
    change (Algebra.DifferenceLattice.ival 0 r - Algebra.DifferenceLattice.ival 0 s) i = 0
    simp only [Pi.sub_apply, Algebra.DifferenceLattice.ival, Pi.zero_apply, zero_add,
      hfixed r hr, hfixed s hs, sub_self]
  intro v hv
  have hh : v i = 0 := he hv
  simpa [Pi.single_apply] using hh

theorem unit_not_mem_of_pivot {d : ℕ} (L : IntLat ι d) (pivot : Fin d → ι)
    (hdet : (L.matrix.submatrix pivot id).det ≠ 0) (i : ι)
    (hnew : ∀ j, pivot j ≠ i) : Pi.single i 1 ∉ L.carrier := by
  classical
  intro hi
  let c : Fin d → ℤ := fun j => L.basis.repr ⟨Pi.single i 1, hi⟩ j
  have he : (Pi.single i 1 : ι → ℤ) = ∑ j, c j • (L.basis j : ι → ℤ) := by
    have hh := congrArg (fun z : L.carrier => (z : ι → ℤ))
      (L.basis.sum_repr ⟨Pi.single i 1, hi⟩)
    simpa only [c, Submodule.coe_sum, Submodule.coe_smul] using hh.symm
  have hw : L.matrix *ᵥ c = Pi.single i 1 := by
    ext j
    simpa only [Matrix.mulVec, dotProduct, IntLat.matrix, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm] using (congrFun he j).symm
  have hp : (L.matrix.submatrix pivot id) *ᵥ c = 0 := by
    ext j
    have hh := congrFun hw (pivot j)
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, Pi.single_apply,
      hnew j, (hnew j).symm] using hh
  have hc : c = 0 := (Matrix.mulVec_injective_of_det_ne_zero hdet) (by simpa using hp)
  have hz := congrFun hw i
  simp [hc] at hz

theorem no_fixed_coordinate_of_normals {d : ℕ} (G : ι → ℕ) (L : IntLat ι d)
    (F : Finset (Grid G)) (hnormals : ordinaryNormals G F = L.carrier)
    (pivot : Fin d → ι) (hdet : (L.matrix.submatrix pivot id).det ≠ 0)
    (i : ι) (hnew : ∀ j, pivot j ≠ i) :
    ¬ ∃ a : ℤ, ∀ r ∈ F, ((r i : ℕ) : ℤ) = a := by
  rintro ⟨a, ha⟩
  have hu := unit_normal_of_fixed G F i a ha
  rw [hnormals] at hu
  exact unit_not_mem_of_pivot L pivot hdet i hnew hu

theorem order_lt_width_of_normals (G : ι → ℕ) (L : IntLat ι 2)
    (F : Finset (Grid G)) (hnormals : ordinaryNormals G F = L.carrier)
    (pivot : Fin 2 → ι) (hdet : (L.matrix.submatrix pivot id).det ≠ 0)
    (i : ι) (hnew : ∀ j, pivot j ≠ i) (order : ℕ)
    (hjump : G i ≤ order → ∃ a : ℤ, ∀ r ∈ F, ((r i : ℕ) : ℤ) = a) :
    order < G i := by
  by_contra hn
  exact no_fixed_coordinate_of_normals G L F hnormals pivot hdet i hnew (hjump (by omega))

theorem regularize2_of_promotion_event (P : VITParameters) (G : ι → ℕ)
    (L : IntLat ι 2) (t : Fin 2 → ℤ) (F : Finset (Grid G))
    (hpromote : Rank2Promotion P G L t F)
    (hmax : atom G (imageZ G L.matrix) t = L.mZ G)
    (hF : F ⊆ ordinaryFibre G L t)
    (hretain : L.mZ G - P.eps ≤ density G F)
    (htrigger : Module.finrank ℤ (ordinaryNormals G F) = 3 ∨
      ∃ (i : ι) (a : ℤ), (∀ r ∈ F, ((r i : ℕ) : ℤ) = a) ∧
        Pi.single i 1 ∉ L.carrier) : Regularize2 P G L := by
  intro hG hm
  have hheavy : P.toVITData.mu ≤ density G F := by
    have hh := (rank2_slack P hm).2
    linarith [P.eps_pos]
  right
  exact hpromote hG hmax
    (nonempty_of_density_pos G F ((threshold_pos P).trans_le hheavy))
    hF hretain hheavy htrigger

section Stretches

variable {n : ℕ} {κ : Fin (n + 1) → Type*}
  [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]

theorem continuation_moment_step (P : VITParameters) {η : Fin 2 → Type*}
    [∀ k, Fintype (η k)] [∀ k, DecidableEq (η k)]
    (G : (k : Fin 2) → η k → ℕ) (L : (k : Fin 2) → IntLat (η k) 2)
    (width order : ℕ)
    (hstretch : Rank2Stretch P.L0 G L (fun _ : Fin 1 => width) (fun _ => order))
    (hpos : ∀ k i, 0 < G k i) (hwidth : 2 ^ P.L0 ≤ width)
    (horder : 1 ≤ order) (hnojump : order < width)
    (hheight : (L 1).H = order * (L 0).H)
    (hmass : (L 1).mZ (G 1) ≤ (L 0).mZ (G 0) *
      (((width + order - 1) / order : ℕ) : ℝ) / (width : ℝ))
    (hmono : (L 1).mZ (G 1) ≤ (L 0).mZ (G 0)) :
    (((L 1).mZ (G 1) * ((L 1).H : ℝ)) ^ (P.L0 - 1)) * (L 1).mZ (G 1) ≤
      (((L 0).mZ (G 0) * ((L 0).H : ℝ)) ^ (P.L0 - 1)) * (L 0).mZ (G 0) := by
  by_cases hv : order = 1
  · have hh : (L 1).H = (L 0).H := by simpa only [hv, one_mul] using hheight
    rw [hh]
    exact moment_mono (mass_nonneg _ _) (Nat.cast_nonneg _) hmono
  · have hv2 : 2 ≤ order := by omega
    apply hstretch P.L0_lower hpos (fun _ => hwidth) (fun _ => ⟨hv2, hnojump⟩)
    · intro k
      fin_cases k
      exact hheight
    · intro k
      fin_cases k
      exact hmass

theorem regular_of_prefix_recurrence (P : VITParameters)
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 2)
    (two : Fin (n + 1) → Prop)
    (hfirst : two 0 → (L 0).H = 1 ∧ (L 0).mZ (G 0) ≤ 1 / (P.g : ℝ) ^ 2)
    (hstep : ∀ k : Fin n, two k.succ →
      (two k.castSucc ∧
        (((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.succ).mZ (G k.succ) ≤
          (((L k.castSucc).mZ (G k.castSucc) * ((L k.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.castSucc).mZ (G k.castSucc)) ∨
      ((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ) ≤
          P.A * P.D * P.C3 / (P.g : ℝ) ^ 2 ∧
        (L k.succ).mZ (G k.succ) ≤ (P.g : ℝ) ^ (-(3 : ℤ)) + P.eps))
    (hfinal : two (Fin.last n))
    (hheavy : P.toVITData.mu ≤ (L (Fin.last n)).mZ (G (Fin.last n))) :
    Regular P.toVITData (G (Fin.last n)) (L (Fin.last n)) := by
  have hall (k : Fin (n + 1)) : two k →
      (((L k).mZ (G k) * ((L k).H : ℝ)) ^ (P.L0 - 1)) * (L k).mZ (G k) ≤
        (P.C2 / (P.g : ℝ) ^ 2) ^ (P.L0 - 1) * P.toVITData.mu := by
    induction k using Fin.induction with
    | zero =>
      intro ht
      obtain ⟨hh, hm⟩ := hfirst ht
      simpa only [hh, Nat.cast_one, mul_one] using
        initial_moment_bound P (mass_nonneg (G 0) (L 0)) hm
    | succ k ih =>
      intro ht
      rcases hstep k ht with ⟨hold, hcontinue⟩ | ⟨hreturn, hcap⟩
      · exact hcontinue.trans (ih hold)
      · exact return_moment_bound P (mass_nonneg (G k.succ) (L k.succ))
          (Nat.cast_nonneg _) hreturn hcap
  have hmu := threshold_pos P
  have hx : 0 ≤ (L (Fin.last n)).mZ (G (Fin.last n)) *
      ((L (Fin.last n)).H : ℝ) :=
    mul_nonneg (mass_nonneg _ _) (Nat.cast_nonneg _)
  have hbound : (0 : ℝ) ≤ P.C2 / (P.g : ℝ) ^ 2 :=
    div_nonneg P.C2_pos.le (sq_nonneg _)
  have hp := (mul_le_mul_of_nonneg_left hheavy (pow_nonneg hx (P.L0 - 1))).trans
    (hall (Fin.last n) hfinal)
  have hh := (pow_le_pow_iff_left₀ (n := P.L0 - 1) hx hbound
    (by have := P.L0_lower; omega)).mp
    ((mul_le_mul_iff_left₀ hmu).mp hp)
  simpa only [Regular, VITData.C, reduceIte, OfNat.ofNat_ne_one] using hh

theorem regularize2_of_normal_prefix_recurrence (P : VITParameters)
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 2)
    (F : (k : Fin (n + 1)) → Finset (Grid (G k))) (t : Fin 2 → ℤ)
    (hpromote : Rank2Promotion P (G (Fin.last n)) (L (Fin.last n)) t (F (Fin.last n)))
    (hmax : atom (G (Fin.last n)) (imageZ (G (Fin.last n)) (L (Fin.last n)).matrix) t =
      (L (Fin.last n)).mZ (G (Fin.last n)))
    (hF : F (Fin.last n) ⊆
      ordinaryFibre (G (Fin.last n)) (L (Fin.last n)) t)
    (hretain : (L (Fin.last n)).mZ (G (Fin.last n)) - P.eps ≤
      density (G (Fin.last n)) (F (Fin.last n)))
    (hfirst : ordinaryNormals (G 0) (F 0) = (L 0).carrier →
      (L 0).H = 1 ∧ (L 0).mZ (G 0) ≤ 1 / (P.g : ℝ) ^ 2)
    (hstep : ∀ k : Fin n,
      ordinaryNormals (G k.succ) (F k.succ) = (L k.succ).carrier →
      (ordinaryNormals (G k.castSucc) (F k.castSucc) = (L k.castSucc).carrier ∧
        (((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.succ).mZ (G k.succ) ≤
          (((L k.castSucc).mZ (G k.castSucc) * ((L k.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.castSucc).mZ (G k.castSucc)) ∨
      ((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ) ≤
          P.A * P.D * P.C3 / (P.g : ℝ) ^ 2 ∧
        (L k.succ).mZ (G k.succ) ≤ (P.g : ℝ) ^ (-(3 : ℤ)) + P.eps)) :
    Regularize2 P (G (Fin.last n)) (L (Fin.last n)) := by
  intro hG hm
  have hslack := rank2_slack P hm
  have hheavy : P.toVITData.mu ≤ density (G (Fin.last n)) (F (Fin.last n)) := by
    linarith [P.eps_pos, hslack.2]
  rcases rank2_normal_dichotomy P (G (Fin.last n)) (L (Fin.last n)) t
    (F (Fin.last n)) hG hF hheavy with heq | hrank
  · left
    apply regular_of_prefix_recurrence P G L
      (fun k => ordinaryNormals (G k) (F k) = (L k).carrier)
      hfirst hstep heq
    linarith [P.eps_pos, hslack.1]
  · exact regularize2_of_promotion_event P (G (Fin.last n)) (L (Fin.last n)) t
      (F (Fin.last n)) hpromote hmax hF hretain (Or.inl hrank) hG hm

end Stretches

end Algebra.Reg

end Praxis.Lift
