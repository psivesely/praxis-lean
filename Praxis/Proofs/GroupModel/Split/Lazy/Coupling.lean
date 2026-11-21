import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 4096

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Coupling

open Classical

def encodingEquiv :
    ((k ↪ Label P0) × (k ↪ Label P0) × (k ↪ Label P0)) ≃ LabelEncoding P0 where
  toFun t := fun s => match s with | .g₁ => t.1 | .g₂ => t.2.1 | .gₜ => t.2.2
  invFun σ := (σ .g₁, σ .g₂, σ .gₜ)
  left_inv _ := rfl
  right_inv σ := by funext s; cases s <;> rfl

noncomputable instance encodingFintype : Fintype (LabelEncoding P0) :=
  Fintype.ofEquiv _ encodingEquiv

noncomputable instance encodingDecidableEq : DecidableEq (LabelEncoding P0) :=
  Classical.decEq _

noncomputable def uniform {H : Type} [Fintype H] [Nonempty H]
    (W : Finset H) : ProbComp H := by
  classical
  exact if h : W.Nonempty then
    letI : Nonempty {σ // σ ∈ W} := h.to_subtype
    letI := SampleableType.ofFintype {σ // σ ∈ W}
    Subtype.val <$> ($ᵗ {σ // σ ∈ W})
  else pure (Classical.arbitrary H)

open scoped ENNReal in
lemma uniform_mass {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]
    (W : Finset H) (hW : W.Nonempty) (σ : H) :
    Pr[= σ | uniform W] = if σ ∈ W then ((W.card : ℝ≥0∞))⁻¹ else 0 := by
  classical
  by_cases hσ : σ ∈ W
  · rw [if_pos hσ]
    simp only [uniform, dif_pos hW]
    rw [show σ = (⟨σ, hσ⟩ : {σ // σ ∈ W}).val from rfl,
      probOutput_map_injective _ Subtype.val_injective]
    simp
  · rw [if_neg hσ]
    apply probOutput_eq_zero
    simp only [uniform, dif_pos hW, support_map, Set.mem_image,
      not_exists, not_and]
    intro x _ hx
    exact hσ (hx ▸ x.prop)

lemma three_uniform {H E α : Type} [Fintype H] [Nonempty H]
    [SampleableType H] [Fintype E] [Nonempty E] (e : (H × H × H) ≃ E)
    (f : E → ProbComp α) :
    evalSPMF (do
      let x ← $ᵗ H
      let y ← $ᵗ H
      let z ← $ᵗ H
      f (e (x, y, z))) =
      evalSPMF (uniform Finset.univ >>= f) := by
  classical
  letI : DecidableEq E := Classical.decEq _
  letI : DecidableEq H := Classical.decEq _
  apply evalSPMF_ext
  intro a
  simp only [probOutput_bind_eq_tsum,
    tsum_fintype, probOutput_uniformSample,
    uniform_mass Finset.univ Finset.univ_nonempty,
    Finset.mem_univ, if_true, Finset.card_univ]
  have hc : Fintype.card E = Fintype.card H ^ 3 := by
    rw [← Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod]
    ring
  rw [hc]
  rw [← Fintype.sum_equiv e
    (fun t => _ * Pr[= a | f (e t)])
    (fun σ => _ * Pr[= a | f σ]) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ1 _ => ?_
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ2 _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σT _ => ?_
  rw [Nat.cast_pow, ENNReal.inv_pow, pow_three]
  simp only [mul_assoc]

lemma sampleEncoding_uniform {α : Type} (f : LabelEncoding P0 → ProbComp α) :
    evalSPMF ((sampleEncoding : ProbComp (LabelEncoding P0)) >>= f) =
      evalSPMF (uniform Finset.univ >>= f) := by
  simp only [sampleEncoding, bind_assoc, pure_bind]
  exact three_uniform encodingEquiv f

end Praxis.Proofs.GroupModel.Split.Lazy.Coupling
