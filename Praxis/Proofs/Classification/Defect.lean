import Praxis.Proofs.Classification.Tensor
import Praxis.Proofs.Classification.ZCoordinates
import Praxis.Proofs.Classification.Quadratic
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Annihilate
import Praxis.Proofs.Classification.Coeff
import Praxis.Proofs.Classification.Cubic
import Praxis.Proofs.Classification.Moore
import Praxis.Params
import Praxis.Setting

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section Generic

variable {F : Type*} [Field F] {d : ℕ} {S : Type*} [Fintype S]

theorem cubic_defect_vector (Ξ : Tri F d) (ξ : S → Fin d → F) (c : S → F)
    (hΞ : Ξ = ∑ s, c s • cube (ξ s)) (u u₀ : Fin d → F)
    (hnorm : ∀ s, dotProduct u₀ (ξ s) = 1)
    (hb : ∀ h, Ξ h u (u - u₀) = 0) :
    ∑ s, (c s * dotProduct u (ξ s) * (dotProduct u (ξ s) - 1)) • ξ s = 0 := by
  ext i
  have h := hb (Pi.single i 1)
  rw [hΞ] at h
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, cube_apply, single_dotProduct,
    one_mul, sub_dotProduct, hnorm, smul_eq_mul] at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  convert h using 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end Generic

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

theorem toK_family_zero {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) (r : Fin d → Fq P0)
    (h : ∑ i, algebraMap (Fq P0) (KummerField P0) (r i) * toK (a i) = 0) : ∀ i, r i = 0 := by
  have hc : ∑ i, r i • a i = 0 := by
    apply toK_injective
    rw [toK_zero, toK_sum_finset]
    simpa only [toK_smul] using h
  exact Fintype.linearIndependent_iff.mp ha r hc

theorem defect_matrix_zero {d : ℕ} {S : Type*} [Fintype S]
    (a : Fin d → KPoly (Fq P0) P0.n) (ha : LinearIndependent (Fq P0) a)
    (ξ : S → Fin d → Fq P0) (e : S → Fq P0) (z : S → KummerField P0)
    (hz : ∀ s, dotProduct (fun i => toK (a i))
      (fun i => algebraMap (Fq P0) (KummerField P0) (ξ s i)) = z s)
    (hv : ∑ s, (algebraMap (Fq P0) (KummerField P0) (e s) * z s) •
      (fun i => algebraMap (Fq P0) (KummerField P0) (ξ s i)) = 0) :
    ∑ s, e s • Matrix.vecMulVec (ξ s) (ξ s) = 0 := by
  let Q := ∑ s, e s • Matrix.vecMulVec (ξ s) (ξ s)
  have hr (j : Fin d) :
      rowForm (fun i => toK (a i)) (Q.map (algebraMap (Fq P0) (KummerField P0))) (Pi.single j 1) = 0 := by
    rw [rowForm_square_sum]
    simp only [hz, single_dotProduct, one_mul]
    have h := congrFun hv j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  ext i j
  have hj := hr j
  rw [rowForm_apply, Matrix.mulVec_single_one] at hj
  have hc : ∑ r, algebraMap (Fq P0) (KummerField P0) (Q r j) * toK (a r) = 0 := by
    simpa only [dotProduct, Matrix.col_apply, Matrix.map_apply, mul_comm] using hj
  exact toK_family_zero a ha _ hc i

end

end Praxis.Proofs.Classification
