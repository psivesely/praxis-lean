import Praxis.Proofs.Classification.Conj
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

theorem descend_cube_coefficient (c z : KummerField P0) (hz : z ≠ 0)
    (h₁ : c * kConj (P0.m - 1) z = kConj (P0.m - 1) c * z)
    (h₂ : c * kConj P0.m z = kConj P0.m c * z) :
    ∃ r : Fq P0, c = algebraMap (Fq P0) (KummerField P0) r * z := by
  have hfixed (s : ℕ) (hs : c * kConj s z = kConj s c * z) : kConj s (c / z) = c / z := by
    rw [map_div₀]
    apply (div_eq_div_iff ((map_ne_zero (kConj s)).mpr hz) hz).mpr
    exact hs.symm
  obtain ⟨r, hr⟩ := kConj_consecutive_fixed (c / z) (hfixed _ h₁) (hfixed _ h₂)
  refine ⟨r, ?_⟩
  rw [hr, div_mul_cancel₀ c hz]

end

end Praxis.Proofs.Classification
