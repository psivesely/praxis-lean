import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Lift.Record
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

noncomputable section

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.SatApp

open Praxis.Algebra Praxis.Algebra.Mod

open Finset

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

open scoped BigOperators Matrix

variable {κ : Type*}

theorem abs_det_le_factorial_prod {e : ℕ} (A : Matrix (Fin e) (Fin e) ℝ)
    (w : Fin e → ℝ) (hA : ∀ i j, |A i j| ≤ w i) :
    |A.det| ≤ (Nat.factorial e : ℝ) * ∏ i, w i := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin e),
        |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin e), ∏ i, w i := by
      apply Finset.sum_le_sum
      intro σ _
      have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
      rw [abs_mul, hs, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ i, w (σ i) := Finset.prod_le_prod
          (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = ∏ i, w i := Equiv.prod_comp σ w
    _ = _ := by simp [Fintype.card_perm]

theorem selected_norm_prod_le {d e : ℕ} (n : Fin d → ℕ)
    (hn : ∀ j, 1 ≤ n j) (I : Fin e → Option (Fin d))
    (hI : Function.Injective I) :
    (∏ i, (I i).elim (1 : ℝ) (fun j => (n j : ℝ))) ≤ ∏ j, (n j : ℝ) := by
  let w : Option (Fin d) → ℝ := fun i => i.elim 1 (fun j => (n j : ℝ))
  have hw (i : Option (Fin d)) : 1 ≤ w i := by
    cases i with
    | none => exact le_rfl
    | some j => dsimp [w]; exact_mod_cast hn j
  change (∏ i, w (I i)) ≤ _
  calc
    _ = ∏ i ∈ univ.image I, w i := by
      rw [Finset.prod_image]
      exact fun a _ b _ h => hI h
    _ ≤ ∏ i, w i := Finset.prod_le_prod_of_subset_of_one_le
      (subset_univ _) (fun i _ => (hw i).trans' (by norm_num))
      (fun i _ _ => hw i)
    _ = _ := by simp [w, Fintype.prod_option]

theorem minor_le_factorial_norm_prod {d e : ℕ} (n : Fin d → ℕ)
    (T : ℝ) (D : Matrix (Option (Fin d)) κ ℤ)
    (hn : ∀ j, 1 ≤ n j) (hT : 1 ≤ T)
    (hrows : ∀ j k, |(D (some j) k : ℝ)| ≤ T * n j)
    (hnew : ∀ k, |(D none k : ℝ)| ≤ T)
    (he : e ≤ d) (I : Fin e → Option (Fin d)) (J : Fin e → κ) :
    (|(D.submatrix I J).det| : ℝ) ≤
      (Nat.factorial d : ℝ) * (∏ j, (n j : ℝ)) * T^d := by
  classical
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  by_cases hI : Function.Injective I
  · let w : Option (Fin d) → ℝ := fun i => i.elim 1 (fun j => (n j : ℝ))
    have hw (i : Option (Fin d)) : 0 ≤ w i := by
      cases i <;> simp [w]
    have hentry (i : Fin e) (j : Fin e) :
        |(D (I i) (J j) : ℝ)| ≤ T * w (I i) := by
      cases hi : I i with
      | none => simpa [hi, w] using hnew (J j)
      | some k => simpa [hi, w] using hrows k (J j)
    have hdet := abs_det_le_factorial_prod
      ((D.submatrix I J).map (Int.castRingHom ℝ))
      (fun i => T * w (I i)) hentry
    have hnorm := selected_norm_prod_le n hn I hI
    have hfac : (Nat.factorial e : ℝ) ≤ Nat.factorial d := by
      exact_mod_cast Nat.factorial_le he
    have hpow : T^e ≤ T^d := pow_le_pow_right₀ hT he
    calc
      _ = |((D.submatrix I J).map (Int.castRingHom ℝ)).det| := by
        exact congrArg abs ((Int.castRingHom ℝ).map_det (D.submatrix I J))
      _ ≤ (Nat.factorial e : ℝ) * ∏ i, T * w (I i) := hdet
      _ = (Nat.factorial e : ℝ) * (∏ i, w (I i)) * T^e := by
        rw [Finset.prod_mul_distrib]
        simp only [prod_const, card_univ, Fintype.card_fin]
        ring
      _ ≤ (Nat.factorial d : ℝ) * (∏ j, (n j : ℝ)) * T^d := by
        have hp : 0 ≤ ∏ i, w (I i) := prod_nonneg (fun i _ => hw _)
        gcongr
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hI
    have hz : (D.submatrix I J).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by funext j; change D (I a) (J j) = D (I b) (J j); rw [hab])
    rw [hz]
    simp only [abs_zero, Int.cast_zero]
    positivity

theorem minorBound_lt_prime (d : ℕ) (P : VITParameters) (T : ℝ)
    (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    (hT2 : T^2 ≤ P.toVITData.T2) :
    minorBound P.toVITData d T < (P.p : ℝ) := by
  have hp0 : 0 ≤ (P.p : ℝ) := Nat.cast_nonneg _
  interval_cases d
  · have hs : (P.toVITData.H1 * T)^2 < (P.p : ℝ)^2 := by
      calc
        _ = P.toVITData.H1^2 * T^2 := by ring
        _ ≤ P.toVITData.H1^2 * P.toVITData.T2 :=
          mul_le_mul_of_nonneg_left hT2 (sq_nonneg _)
        _ < _ := P.minor1
    simpa [minorBound, basisConstant, heightBound] using
      lt_of_pow_lt_pow_left₀ 2 hp0 hs
  · have hg : 0 < (P.g : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) P.L0) P.g_lower
    have hmu : 0 < P.toVITData.mu := P.eps_pos.trans P.eps_lt_mu
    have hH2 : 0 < P.toVITData.H2 :=
      div_pos P.C2_pos (mul_pos (sq_pos_of_pos hg) hmu)
    have hs : 4 * P.toVITData.H2 * T^2 < (P.p : ℝ) :=
      (mul_le_mul_of_nonneg_left hT2 (by positivity)).trans_lt P.minor2
    norm_num [minorBound, basisConstant, heightBound] at ⊢
    exact hs
  · have hs : (54 * P.toVITData.H3 * T^3)^2 < (P.p : ℝ)^2 := by
      calc
        _ = (54 * P.toVITData.H3)^2 * (T^2)^3 := by ring
        _ ≤ (54 * P.toVITData.H3)^2 * P.toVITData.T2^3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg T) hT2 3)
            (sq_nonneg _)
        _ < _ := P.minor3
    have hlt := lt_of_pow_lt_pow_left₀ 2 hp0 hs
    norm_num [minorBound, basisConstant, heightBound] at ⊢
    exact hlt

theorem saturationApplication (d : ℕ) (P : VITParameters) (n : Fin d → ℕ)
    (T : ℝ) (D : Matrix (Option (Fin d)) κ ℤ) :
    SaturationApplication d P n T D := by
  intro hd1 hd3 hn hprod hT hT2 hrows hnew e he I J
  have hb : (|(D.submatrix I J).det| : ℝ) ≤ minorBound P.toVITData d T := by
    calc
      _ ≤ (Nat.factorial d : ℝ) * (∏ j, (n j : ℝ)) * T^d :=
        minor_le_factorial_norm_prod n T D hn hT hrows hnew he I J
      _ ≤ (Nat.factorial d : ℝ) *
          (basisConstant d * heightBound P.toVITData d) * T^d := by
        have hT0 : 0 ≤ T := le_trans (by norm_num) hT
        gcongr
      _ = _ := by unfold minorBound; ring
  refine ⟨hb, ?_⟩
  have hsmall : (|(D.submatrix I J).det| : ℝ) < (P.p : ℝ) :=
    hb.trans_lt (minorBound_lt_prime d P T hd1 hd3 hT2)
  exact_mod_cast hsmall

end Algebra.Mod.SatApp

end Praxis.Lift
