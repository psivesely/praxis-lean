import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel
import Praxis.Encryption.BN254
import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import VCVio.EvalDist.Defs.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.List.GetD

namespace Praxis.Algebra.Label

open OracleComp OracleSpec GroupModel.Sorted

namespace RefCoupling

open OracleComp OracleSpec

open scoped ENNReal

section WorldSets

variable {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]

noncomputable def unifSet (W : Finset H) : ProbComp H := by
  classical
  exact if h : W.Nonempty then
    letI : Nonempty {x // x ∈ W} := h.to_subtype
    letI : SampleableType {x // x ∈ W} := SampleableType.ofFintype _
    Subtype.val <$> ($ᵗ {x // x ∈ W})
  else pure (Classical.arbitrary H)

omit [Fintype H] in
theorem probOutput_unifSet (W : Finset H) (hW : W.Nonempty) (w : H) :
    Pr[= w | unifSet W] = if w ∈ W then ((W.card : ℝ≥0∞))⁻¹ else 0 := by
  classical
  by_cases hw : w ∈ W
  · rw [if_pos hw]
    simp only [unifSet, dif_pos hW]
    rw [show w = (⟨w, hw⟩ : {x // x ∈ W}).val from rfl,
      probOutput_map_injective _ Subtype.val_injective]
    simp
  · rw [if_neg hw]
    apply probOutput_eq_zero
    simp only [unifSet, dif_pos hW, support_map, Set.mem_image, not_exists, not_and]
    intro x _ hx
    exact hw (hx ▸ x.prop)

omit [Fintype H] [DecidableEq H] in
theorem mem_unifSet_support (W : Finset H) (hW : W.Nonempty) (σ : H)
    (h : σ ∈ support (unifSet W)) : σ ∈ W := by
  classical
  simp only [unifSet, dif_pos hW, support_map, Set.mem_image] at h
  obtain ⟨x, _, rfl⟩ := h
  exact x.prop

theorem unifSet_disintegrate {R B : Type} [DecidableEq R] (W : Finset H) (f : H → R)
    (k : R → H → ProbComp B) :
    𝒮[unifSet W >>= fun σ => unifSet (W.filter fun σ' => f σ' = f σ) >>= k (f σ)] =
      𝒮[unifSet W >>= fun σ => k (f σ) σ] := by
  classical
  by_cases hW : W.Nonempty
  swap
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst he
    simp [unifSet]
  apply evalSPMF_ext
  intro b
  simp only [probOutput_bind_eq_tsum, tsum_fintype, probOutput_unifSet W hW]
  set F : H → Finset H := fun σ => W.filter fun σ' => f σ' = f σ with hF
  have hFne : ∀ σ ∈ W, (F σ).Nonempty := fun σ hσ => ⟨σ, by simp [hF, hσ]⟩
  have hFeq : ∀ σ σ', f σ' = f σ → F σ' = F σ := by
    intro σ σ' h
    simp only [hF, h]

  have inner : ∀ σ ∈ W, (∑ σ', Pr[= σ' | unifSet (F σ)] * Pr[= b | k (f σ) σ']) =
      ∑ σ', if σ' ∈ F σ then ((F σ).card : ℝ≥0∞)⁻¹ * Pr[= b | k (f σ') σ'] else 0 := by
    intro σ hσ
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [probOutput_unifSet (F σ) (hFne σ hσ)]
    split_ifs with h
    · have : f σ' = f σ := (Finset.mem_filter.mp h).2
      rw [this]
    · simp
  calc
    _ = ∑ σ, ∑ σ', if σ ∈ W then (if σ' ∈ F σ then ((W.card : ℝ≥0∞))⁻¹ *
          (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | k (f σ') σ']) else 0) else 0 := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs with hσ
      · rw [inner σ hσ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ' _ => ?_
        split_ifs with h
        · rw [hFeq σ σ' (Finset.mem_filter.mp h).2]
        · simp
      · simp
    _ = ∑ σ', ∑ σ, if σ ∈ W then (if σ' ∈ F σ then ((W.card : ℝ≥0∞))⁻¹ *
          (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | k (f σ') σ']) else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ σ', if σ' ∈ W then ((W.card : ℝ≥0∞))⁻¹ * Pr[= b | k (f σ') σ'] else 0 := by
      refine Finset.sum_congr rfl fun σ' _ => ?_
      by_cases hσ' : σ' ∈ W
      · rw [if_pos hσ']
        have hset : ∀ σ, (if σ ∈ W then (if σ' ∈ F σ then ((W.card : ℝ≥0∞))⁻¹ *
            (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | k (f σ') σ']) else 0) else 0) =
            if σ ∈ F σ' then ((W.card : ℝ≥0∞))⁻¹ *
              (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | k (f σ') σ']) else 0 := by
          intro σ
          by_cases hσ : σ ∈ W
          · have hiff : σ' ∈ F σ ↔ σ ∈ F σ' := by
              simp only [hF, Finset.mem_filter, hσ, hσ', true_and]
              exact eq_comm
            simp only [if_pos hσ, hiff]
          · have : σ ∉ F σ' := fun h => hσ (Finset.mem_filter.mp h).1
            simp [hσ, this]
        simp only [hset]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        have hc : ((F σ').card : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast (Finset.card_pos.mpr (hFne σ' hσ')).ne'
        rw [← mul_assoc, mul_comm ((F σ').card : ℝ≥0∞), mul_assoc, ← mul_assoc _ _ (Pr[= b | _]),
          ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), one_mul]
      · rw [if_neg hσ']
        apply Finset.sum_eq_zero
        intro σ _
        split_ifs with hσ h
        · exact absurd (Finset.mem_filter.mp h).1 hσ'
        · rfl
        · rfl
    _ = _ := by
      refine Finset.sum_congr rfl fun σ' _ => ?_
      split_ifs <;> simp

end WorldSets

end RefCoupling

namespace RefCoupling

open OracleComp OracleSpec GroupModel.Sorted

open scoped ENNReal

section Decode

variable {p n : ℕ}

theorem decodeLabel_eq_some_iff (τ : ZMod p ↪ BitVec n) (t : BitVec n) (v : ZMod p) :
    decodeLabel τ t = some v ↔ τ v = t := by
  classical
  unfold decodeLabel
  constructor
  · intro h
    split at h
    · next hex =>
        have hv : hex.choose = v := Option.some.inj h
        rw [← hv]
        exact hex.choose_spec
    · exact absurd h (by simp)
  · intro h
    have hex : ∃ x, τ x = t := ⟨v, h⟩
    rw [dif_pos hex]
    exact congrArg some (τ.injective (hex.choose_spec.trans h.symm))

end Decode

end RefCoupling

end Praxis.Algebra.Label
