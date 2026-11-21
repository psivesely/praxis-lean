import Praxis.Lift.Algebra.Reg.Regularize2Closed
import Praxis.Lift.Algebra.Reg.Promote1
import Praxis.Lift.Algebra.Reg.Nested1
import Praxis.Lift.Algebra.Reg.Return1
import Praxis.Algebra.Reg.Stretch1
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Reg.Rank1Model
import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Algebra.Reg.Step2Actual
import Praxis.Algebra.Reg.Rank1Model
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Regularize1

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Lift.Algebra.Reg.Rank1Model

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Algebra.Reg.Rank1Model hiding Rank1Promotion Rank1Return21 Rank1Return31 Rank1NestedCall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rank1_slack (P : VITParameters) {m : ℝ}
    (hm : P.theta0 - 20 * P.eps ≤ m) :
    P.toVITData.mu + 80 * P.eps ≤ m ∧ P.toVITData.mu < m - 2 * P.eps := by
  dsimp [VITData.mu]
  constructor <;> linarith [P.eps_pos]

theorem common_nonneg (P : VITParameters) :
    (0 : ℝ) ≤ P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) :=
  div_nonneg (mul_nonneg P.A_pos.le
    (le_max_of_le_left (mul_nonneg P.D_pos.le P.C2_pos.le))) (Nat.cast_nonneg _)

theorem initial_moment_bound1 (P : VITParameters) {m : ℝ}
    (hm : 0 ≤ m) (hcap : m ≤ 1 / (P.g : ℝ)) :
    m ^ (P.L0 - 1) * m ≤
      (P.C1 / (P.g : ℝ)) ^ (P.L0 - 1) * P.toVITData.mu := by
  have hmu := Algebra.Reg.threshold_pos P
  have hr : m / P.toVITData.mu ≤ P.C1 ^ (P.L0 - 1) := by
    apply le_trans (div_le_div_of_nonneg_right hcap hmu.le)
    simpa only [one_div] using P.C1_power
  have hh := Algebra.Reg.moment_bound (n := P.L0 - 1) hmu hm hm
    (by positivity : (0 : ℝ) ≤ 1 / (P.g : ℝ)) hcap hr
  convert hh using 1
  ring

theorem return_moment_bound1 (P : VITParameters) {m H : ℝ}
    (hm : 0 ≤ m) (hH : 0 ≤ H)
    (hbound : m * H ≤ P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ))
    (hcap : m ≤ (P.g : ℝ) ^ (-(2 : ℤ)) + 2 * P.eps) :
    (m * H) ^ (P.L0 - 1) * m ≤
      (P.C1 / (P.g : ℝ)) ^ (P.L0 - 1) * P.toVITData.mu := by
  have hmu := Algebra.Reg.threshold_pos P
  have hB := common_nonneg P
  have hr := (div_le_div_of_nonneg_right hcap hmu.le).trans P.Q1_power
  have hh := Algebra.Reg.moment_bound (n := P.L0 - 1) hmu (mul_nonneg hm hH) hm hB hbound hr
  have hscale : P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) * P.Q1 ≤
      P.C1 / (P.g : ℝ) := by
    calc
      _ = (P.A * max (P.D * P.C2) (P.E * P.C3) * P.Q1) / (P.g : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right P.C1_recursion (Nat.cast_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg hB P.Q1_pos.le) hscale _) hmu.le)

theorem descent_mass_cap (P : VITParameters) {e : ℕ} (he : 2 ≤ e)
    (G : ι → ℕ) (N : IntLat ι e) (hG : GridBudget P.toVITData G)
    {mOld mNew : ℝ} (hretain : mOld - 2 * P.eps ≤ N.mZ G) (hmono : mNew ≤ mOld) :
    mNew ≤ (P.g : ℝ) ^ (-(2 : ℤ)) + 2 * P.eps := by
  have hgpos : (0 : ℝ) < P.g := by exact_mod_cast Algebra.Reg.grid_lower_pos P
  have hg1 : (1 : ℝ) ≤ P.g := by
    exact_mod_cast Nat.succ_le_of_lt (Algebra.Reg.grid_lower_pos P)
  have hN := Algebra.Reg.mass_le_pivot G N (Algebra.Reg.grid_lower_pos P) hG.1
  have hp : 1 / (P.g : ℝ) ^ e ≤ (P.g : ℝ) ^ (-(2 : ℤ)) := by
    rw [zpow_neg, zpow_ofNat, ← one_div]
    exact one_div_le_one_div_of_le (pow_pos hgpos _) (pow_le_pow_right₀ hg1 he)
  linarith

section Prefixes

variable {n : ℕ} {κ : Fin (n + 1) → Type*}
  [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]

theorem regular_of_prefix_recurrence1 (P : VITParameters)
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 1)
    (one : Fin (n + 1) → Prop)
    (hfirst : one 0 → (L 0).H = 1 ∧ (L 0).mZ (G 0) ≤ 1 / (P.g : ℝ))
    (hstep : ∀ k : Fin n, one k.succ →
      (one k.castSucc ∧
        (((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.succ).mZ (G k.succ) ≤
          (((L k.castSucc).mZ (G k.castSucc) * ((L k.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.castSucc).mZ (G k.castSucc)) ∨
      ((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ) ≤
          P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) ∧
        (L k.succ).mZ (G k.succ) ≤ (P.g : ℝ) ^ (-(2 : ℤ)) + 2 * P.eps))
    (hfinal : one (Fin.last n))
    (hheavy : P.toVITData.mu ≤ (L (Fin.last n)).mZ (G (Fin.last n))) :
    Regular P.toVITData (G (Fin.last n)) (L (Fin.last n)) := by
  have hall (k : Fin (n + 1)) : one k →
      (((L k).mZ (G k) * ((L k).H : ℝ)) ^ (P.L0 - 1)) * (L k).mZ (G k) ≤
        (P.C1 / (P.g : ℝ)) ^ (P.L0 - 1) * P.toVITData.mu := by
    induction k using Fin.induction with
    | zero =>
      intro ht
      obtain ⟨hh, hm⟩ := hfirst ht
      simpa only [hh, Nat.cast_one, mul_one] using
        initial_moment_bound1 P (Algebra.Reg.mass_nonneg (G 0) (L 0)) hm
    | succ k ih =>
      intro ht
      rcases hstep k ht with ⟨hold, hcontinue⟩ | ⟨hreturn, hcap⟩
      · exact hcontinue.trans (ih hold)
      · exact return_moment_bound1 P (Algebra.Reg.mass_nonneg (G k.succ) (L k.succ))
          (Nat.cast_nonneg _) hreturn hcap
  have hmu := Algebra.Reg.threshold_pos P
  have hx : 0 ≤ (L (Fin.last n)).mZ (G (Fin.last n)) *
      ((L (Fin.last n)).H : ℝ) :=
    mul_nonneg (Algebra.Reg.mass_nonneg _ _) (Nat.cast_nonneg _)
  have hbound : (0 : ℝ) ≤ P.C1 / (P.g : ℝ) :=
    div_nonneg P.C1_pos.le (Nat.cast_nonneg _)
  have hp := (mul_le_mul_of_nonneg_left hheavy (pow_nonneg hx (P.L0 - 1))).trans
    (hall (Fin.last n) hfinal)
  have hh := (pow_le_pow_iff_left₀ (n := P.L0 - 1) hx hbound
    (by have := P.L0_lower; omega)).mp
    ((mul_le_mul_iff_left₀ hmu).mp hp)
  simpa only [Regular, VITData.C, reduceIte, pow_one] using hh

end Prefixes

theorem rank1_normal_dichotomy (P : VITParameters) (G : ι → ℕ)
    (L : IntLat ι 1) (t : Fin 1 → ℤ) (F : Finset (Grid G))
    (hG : GridBudget P.toVITData G) (hF : F ⊆ ordinaryFibre G L t)
    (hheavy : P.toVITData.mu ≤ density G F) :
    ordinaryNormals G F = L.carrier ∨
      Module.finrank ℤ (ordinaryNormals G F) = 2 ∨
      Module.finrank ℤ (ordinaryNormals G F) = 3 := by
  have hLN := Algebra.Reg.carrier_le_normals G L t F hF
  have hlow := (Submodule.inclusion hLN).finrank_le_finrank_of_injective
    (Submodule.inclusion_injective hLN)
  have hLdim : Module.finrank ℤ L.carrier = 1 := by
    simpa using Module.finrank_eq_card_basis L.basis
  rw [hLdim] at hlow
  have hhigh := Algebra.Reg.normal_rank_le_three P G F hG hheavy
  by_cases hdim : Module.finrank ℤ (ordinaryNormals G F) = 1
  · exact Or.inl (Algebra.Reg.saturated_eq_of_le_of_finrank_eq L _ hLN hdim).symm
  · omega

theorem regularize1_of_promotion_event (P : VITParameters) (G : ι → ℕ)
    (L : IntLat ι 1) (t : Fin 1 → ℤ) (F : Finset (Grid G))
    (hpromote : Rank1Promotion P G L t F)
    (hV7 : ∀ M : IntLat ι 2, Regularize2 P G M)
    (hmax : atom G (imageZ G L.matrix) t = L.mZ G)
    (hF : F ⊆ ordinaryFibre G L t)
    (hretain : L.mZ G - P.eps ≤ density G F)
    (htrigger : Module.finrank ℤ (ordinaryNormals G F) = 2 ∨
      Module.finrank ℤ (ordinaryNormals G F) = 3 ∨
      ∃ (i : ι) (a : ℤ), (∀ r ∈ F, ((r i : ℕ) : ℤ) = a) ∧
        Pi.single i 1 ∉ L.carrier) : Regularize1 P G L := by
  intro hG hm
  have hheavy : P.toVITData.mu ≤ density G F := by
    have hh := (rank1_slack P hm).2
    linarith [P.eps_pos]
  rcases hpromote hG hmax
      (Algebra.Reg.nonempty_of_density_pos G F ((Algebra.Reg.threshold_pos P).trans_le hheavy))
      hF hretain hheavy htrigger with ⟨L2, hc2, hm2⟩ | ⟨L3, hc3, hm3, hH3, hreg3⟩
  · right
    exact (Algebra.Reg.Nested1.rank1_nested_call P G L L2 hG hm hc2 hm2 (hV7 L2)).2
  · right; right
    exact ⟨L3, hc3, by linarith [P.eps_pos], hH3, hreg3⟩

section Assembly

variable {n : ℕ} {κ : Fin (n + 1) → Type*}
  [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]

theorem regularize1_of_normal_prefix_recurrence (P : VITParameters)
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 1)
    (F : (k : Fin (n + 1)) → Finset (Grid (G k))) (t : Fin 1 → ℤ)
    (hpromote : Rank1Promotion P (G (Fin.last n)) (L (Fin.last n)) t (F (Fin.last n)))
    (hV7 : ∀ M : IntLat (κ (Fin.last n)) 2, Regularize2 P (G (Fin.last n)) M)
    (hmax : atom (G (Fin.last n)) (imageZ (G (Fin.last n)) (L (Fin.last n)).matrix) t =
      (L (Fin.last n)).mZ (G (Fin.last n)))
    (hF : F (Fin.last n) ⊆ ordinaryFibre (G (Fin.last n)) (L (Fin.last n)) t)
    (hretain : (L (Fin.last n)).mZ (G (Fin.last n)) - P.eps ≤
      density (G (Fin.last n)) (F (Fin.last n)))
    (hfirst : ordinaryNormals (G 0) (F 0) = (L 0).carrier →
      (L 0).H = 1 ∧ (L 0).mZ (G 0) ≤ 1 / (P.g : ℝ))
    (hstep : ∀ k : Fin n,
      ordinaryNormals (G k.succ) (F k.succ) = (L k.succ).carrier →
      (ordinaryNormals (G k.castSucc) (F k.castSucc) = (L k.castSucc).carrier ∧
        (((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.succ).mZ (G k.succ) ≤
          (((L k.castSucc).mZ (G k.castSucc) * ((L k.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.castSucc).mZ (G k.castSucc)) ∨
      ((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ) ≤
          P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) ∧
        (L k.succ).mZ (G k.succ) ≤ (P.g : ℝ) ^ (-(2 : ℤ)) + 2 * P.eps)) :
    Regularize1 P (G (Fin.last n)) (L (Fin.last n)) := by
  intro hG hm
  have hslack := rank1_slack P hm
  have hheavy : P.toVITData.mu ≤ density (G (Fin.last n)) (F (Fin.last n)) := by
    linarith [P.eps_pos, hslack.2]
  rcases rank1_normal_dichotomy P (G (Fin.last n)) (L (Fin.last n)) t
    (F (Fin.last n)) hG hF hheavy with heq | hrank
  · left
    apply regular_of_prefix_recurrence1 P G L
      (fun k => ordinaryNormals (G k) (F k) = (L k).carrier)
      hfirst hstep heq
    linarith [P.eps_pos, hslack.1]
  · exact regularize1_of_promotion_event P (G (Fin.last n)) (L (Fin.last n)) t
      (F (Fin.last n)) hpromote hV7 hmax hF hretain
      (hrank.elim Or.inl (fun h => Or.inr (Or.inl h))) hG hm

theorem regularize1_of_prefix_recurrence_closed (P : VITParameters)
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 1)
    (F : (k : Fin (n + 1)) → Finset (Grid (G k))) (t : Fin 1 → ℤ)
    (hmax : atom (G (Fin.last n)) (imageZ (G (Fin.last n)) (L (Fin.last n)).matrix) t =
      (L (Fin.last n)).mZ (G (Fin.last n)))
    (hF : F (Fin.last n) ⊆ ordinaryFibre (G (Fin.last n)) (L (Fin.last n)) t)
    (hretain : (L (Fin.last n)).mZ (G (Fin.last n)) - P.eps ≤
      density (G (Fin.last n)) (F (Fin.last n)))
    (hfirst : ordinaryNormals (G 0) (F 0) = (L 0).carrier →
      (L 0).H = 1 ∧ (L 0).mZ (G 0) ≤ 1 / (P.g : ℝ))
    (hstep : ∀ k : Fin n,
      ordinaryNormals (G k.succ) (F k.succ) = (L k.succ).carrier →
      (ordinaryNormals (G k.castSucc) (F k.castSucc) = (L k.castSucc).carrier ∧
        (((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.succ).mZ (G k.succ) ≤
          (((L k.castSucc).mZ (G k.castSucc) * ((L k.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (L k.castSucc).mZ (G k.castSucc)) ∨
      ((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ) ≤
          P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) ∧
        (L k.succ).mZ (G k.succ) ≤ (P.g : ℝ) ^ (-(2 : ℤ)) + 2 * P.eps)) :
    Regularize1 P (G (Fin.last n)) (L (Fin.last n)) :=
  regularize1_of_normal_prefix_recurrence P G L F t
    (Algebra.Reg.Promote1.rank1_promotion P _ _ t _
      (fun L3 => Algebra.Reg.Step2.Actual.rank3 P _ L3))
    (fun M => Algebra.Reg.Closed2.regularize2 P _ M) hmax hF hretain hfirst hstep

end Assembly

theorem rank1_stretch_closed (L0 : ℕ) {n : ℕ} {κ : Fin (n + 1) → Type*}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 1)
    (width order : Fin n → ℕ) : Rank1Stretch L0 G L width order :=
  Algebra.Reg.Stretch1.rank1_stretch Algebra.Reg.Step2.Actual.power L0 G L width order

end Algebra.Reg.Regularize1

end Praxis.Lift
