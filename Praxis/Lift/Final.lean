import Praxis.Lift.Record
import Praxis.Lift.Algebra.Mod.Final
import Praxis.Lift.Algebra.Mod.RegularizationClosed
import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Algebra.Conversion.Conversion
import Praxis.Algebra.Conversion.ConversionStatement
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Rank3Branch.VectorInverse
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

noncomputable section

set_option linter.ambiguousOpen false

namespace Praxis.Lift

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions Praxis.Lift.Algebra.Mod.Final

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def FinalFromModular (P : CertifiedLiftParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) : Prop :=
  ModularRegularization P.toVITParameters G z →
    HeavyStack.ConversionClaim 1 → HeavyStack.ConversionClaim 2 →
    HeavyStack.ConversionClaim 3 → VectorInverseStatement P G z

theorem eta_lt_p (P : CertifiedLiftParameters) : (P.eta : ℝ) < P.p := by
  have h : P.eta < P.p := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide))
    P.two_eta_lt_p
  exact_mod_cast h

theorem conversion_power_le (P : CertifiedLiftParameters) (G : ι → ℕ)
    (hG : GridBudget P.toVITData G) {d : ℕ} (L : IntLat ι d)
    (hm : P.toVITData.mu < L.mZ G) (hreg : Regular P.toVITData G L)
    (hd1 : 1 ≤ d) (hd3 : d ≤ 3) :
    (Nat.factorial d : ℝ) * L.H * (P.p : ℝ)^(d-1) ≤ (P.eta : ℝ)^d := by
  have hp : (0 : ℝ) < P.p := by exact_mod_cast P.p_prime.pos
  have hH := regular_height_le P.toVITParameters G L hm hreg
  interval_cases d
  · have hheight : (L.H : ℝ) ≤ P.toVITData.H1 := by
      simpa [VITData.C, VITData.H1] using hH
    have hceil : P.toVITData.H1 ≤ (P.eta : ℝ) := by
      have h1 := Int.le_ceil P.toVITData.H1
      have h2 : ((Int.ceil P.toVITData.H1 : ℤ) : ℝ) ≤ ((P.eta : ℤ) : ℝ) := by
        exact_mod_cast P.branch1
      push_cast at h2
      linarith
    simpa using hheight.trans hceil
  · have hheight : (L.H : ℝ) ≤ P.toVITData.H2 := by
      simpa [VITData.C, VITData.H2] using hH
    have hceil : 2 * P.toVITData.H2 * (P.p : ℝ) ≤ (P.eta : ℝ)^2 := by
      have h1 := Int.le_ceil (2 * P.toVITData.H2 * (P.p : ℝ))
      have h2 : ((Int.ceil (2 * P.toVITData.H2 * (P.p : ℝ)) : ℤ) : ℝ) ≤
          (((P.eta : ℤ) ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast P.branch2
      push_cast at h2
      linarith
    have hmul : 2 * (L.H : ℝ) * (P.p : ℝ) ≤ 2 * P.toVITData.H2 * (P.p : ℝ) := by
      have := mul_le_mul_of_nonneg_right hheight hp.le
      linarith
    have hgoal : 2 * (L.H : ℝ) * (P.p : ℝ) ≤ (P.eta : ℝ)^2 := hmul.trans hceil
    simpa [Nat.factorial] using hgoal
  · have hh := rank_three_height_lt P.toVITParameters G hG L hm
    have hfloor : (L.H : ℤ) ≤ Int.floor P.toVITData.H3 :=
      Int.le_floor.mpr (by exact_mod_cast hh.le)
    have hZ : 6 * (L.H : ℤ) * (P.p : ℤ)^2 ≤ (P.eta : ℤ)^3 := by
      have hp2 : (0 : ℤ) ≤ (P.p : ℤ)^2 := by positivity
      have hstep : 6 * (L.H : ℤ) * (P.p : ℤ)^2 ≤
          6 * Int.floor P.toVITData.H3 * (P.p : ℤ)^2 := by
        have := mul_le_mul_of_nonneg_right hfloor hp2
        linarith
      exact hstep.trans P.branch3
    have hR : 6 * (L.H : ℝ) * (P.p : ℝ)^2 ≤ (P.eta : ℝ)^3 := by
      exact_mod_cast hZ
    have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
    simpa [hfac] using hR

theorem height_lt_prime_of_power_le {d M p : ℕ} {eta : ℝ}
    (hd : 0 < d) (heta : 0 ≤ eta) (hep : eta < (p : ℝ))
    (hpow : (Nat.factorial d : ℝ) * M * (p : ℝ)^(d-1) ≤ eta^d) : M < p := by
  have hpower : eta^d < (p : ℝ)^d :=
    pow_lt_pow_left₀ hep heta (Nat.ne_of_gt hd)
  by_contra! hMp
  have hMpR : (p : ℝ) ≤ M := by exact_mod_cast hMp
  have hlow : (p : ℝ)^d ≤ (Nat.factorial d : ℝ) * M * (p : ℝ)^(d-1) := calc
    (p : ℝ)^d = (p : ℝ) * (p : ℝ)^(d-1) := by
      conv_lhs => rw [show d = (d-1)+1 by omega, pow_succ]
      ring
    _ ≤ (M : ℝ) * (p : ℝ)^(d-1) := by gcongr
    _ ≤ (Nat.factorial d : ℝ) * M * (p : ℝ)^(d-1) := by
      have hfac : (1 : ℝ) ≤ Nat.factorial d := by
        exact_mod_cast Nat.factorial_pos d
      have hnonneg : (0 : ℝ) ≤ (M : ℝ) * (p : ℝ)^(d-1) := by positivity
      nlinarith
  exact (not_lt_of_ge hlow) (hpow.trans_lt hpower)

theorem shortMultiple_of_conversion_power (P : CertifiedLiftParameters)
    {d : ℕ} (hd : 0 < d) (L : IntLat ι d) (z : ι → ZMod P.p) (hz : z ≠ 0)
    (hspan : z ∈ redSpan P.p L) (hconv : HeavyStack.ConversionClaim d)
    (hpow : (Nat.factorial d : ℝ) * L.H * (P.p : ℝ)^(d-1) ≤ (P.eta : ℝ)^d) :
    ShortMultiple P.p z (P.eta : ℝ) := by
  classical
  obtain ⟨r, hr, hH, hmax⟩ := lattice_maximal_minor L
  obtain ⟨c, hc⟩ := redSpan_coordinates L z hspan
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let A : Matrix (Fin (Fintype.card ι)) (Fin d) ℤ := L.matrix.submatrix e id
  let z' : Fin (Fintype.card ι) → ZMod P.p := z ∘ e
  have hz' : z' ≠ 0 := by
    intro h
    apply hz
    ext i
    simpa [z'] using congrFun h (e.symm i)
  have hminor : (A.submatrix (e.symm ∘ r) id).det.natAbs = L.H := by
    simpa [A, Matrix.submatrix, Function.comp_def] using hr
  have hmax' (s : Fin d → Fin (Fintype.card ι)) :
      (A.submatrix s id).det.natAbs ≤ L.H := hmax (e ∘ s)
  have hspan' : ∃ c : Fin d → ZMod P.p,
      ∀ i, z' i = ∑ j, (A i j : ZMod P.p) * c j := ⟨c, fun i => hc (e i)⟩
  obtain ⟨w, a, hw, ha, hcong, hb⟩ := hconv P.p (Fintype.card ι) P.p_prime A
    (e.symm ∘ r) L.H hminor hH
    (height_lt_prime_of_power_le hd (Nat.cast_nonneg _) (eta_lt_p P) hpow)
    hmax' z' hz' hspan'
  let v : ι → ℤ := w ∘ e.symm
  have hv : v ≠ 0 := by
    intro h
    apply hw
    ext i
    simpa [v] using congrFun h (e i)
  have hvc (i : ι) : (v i : ZMod P.p) = a * z i := by
    simpa [v, z'] using hcong (e.symm i)
  have hvb : maxAbs v ≤ P.eta := by
    apply Finset.sup_le
    intro i _
    have hreal : |(v i : ℝ)| ≤ (P.eta : ℝ) :=
      le_of_pow_le_pow_left₀ (Nat.ne_of_gt hd) (Nat.cast_nonneg _)
        ((hb (e.symm i)).trans hpow)
    have hZ : (((v i).natAbs : ℤ) : ℝ) ≤ ((P.eta : ℤ) : ℝ) := by
      simpa using hreal
    exact_mod_cast hZ
  exact ⟨a, v, ha, hv, hvc, by exact_mod_cast hvb⟩

theorem final_from_modular (P : CertifiedLiftParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) : FinalFromModular P G z := by
  intro hmod hconv1 hconv2 hconv3 hG hz hm
  obtain ⟨d, L, hW⟩ := hmod hG hz hm
  have hmass := witness_mass_gt_mu P.toVITParameters G z L hm hW
  have hpow := conversion_power_le P G hG L hmass hW.2.2.2.1 hW.1 hW.2.1
  have hconv : HeavyStack.ConversionClaim d := by
    have hd1 := hW.1
    have hd3 := hW.2.1
    interval_cases d <;> assumption
  exact shortMultiple_of_conversion_power P hW.1 L z hz hW.2.2.1 hconv hpow

theorem vector_inverse (P : CertifiedLiftParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p)
    (hmod : ModularRegularization P.toVITParameters G z) :
    VectorInverseStatement P G z :=
  final_from_modular P G z hmod (HeavyStack.conversion_general (by decide))
    HeavyStack.conversion_rank_two HeavyStack.conversion_rank_three

theorem vector_inverse_zero (P : CertifiedLiftParameters) {n : ℕ}
    (G : Fin n → ℕ) (z : Fin (n+1) → ZMod P.p)
    (hmod : ModularRegularization P.toVITParameters G (fun i => z i.succ)) :
    VectorInverseZ0Statement P G z := by
  let _ : Fact P.p.Prime := ⟨P.p_prime⟩
  intro hG hz hz0 hm
  obtain ⟨a, w, ha, hw, hcong, hb⟩ := vector_inverse P G (fun i => z i.succ)
    hmod hG (Algebra.RankThree.tail_ne_zero hz hz0) hm
  have hbound : maxAbs w ≤ P.eta := by exact_mod_cast hb
  let v : Fin (n+1) → ℤ := Fin.cons 0 w
  refine ⟨a, v, ha, ?_, rfl, ?_, ?_⟩
  · intro hv
    apply hw
    ext i
    exact congrFun hv i.succ
  · intro i
    refine Fin.cases ?_ (fun j => hcong j) i
    simp [v, hz0]
  · change (univ.sup fun i => (v i).natAbs) ≤ P.eta
    apply Finset.sup_le
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [v]
    · exact (Combinatorics.UnequalChain.natAbs_le_maxNorm w j).trans hbound

theorem modularRegularization_fin (P : VITParameters) (n : ℕ) (G : Fin n → ℕ)
    (z : Fin n → ZMod P.p) : ModularRegularization P G z :=
  Algebra.Mod.RegularizationClosed.modular_regularization P (Fin n) G z

theorem liftHyp_all (P : CertifiedLiftParameters) : LiftHyp P :=
  fun n G z => vector_inverse_zero P G z
    (modularRegularization_fin P.toVITParameters n G (fun i => z i.succ))

theorem liftHolds : LiftHolds := liftHyp_all

end Praxis.Lift

end
