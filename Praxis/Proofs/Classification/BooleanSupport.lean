import Praxis.Proofs.Classification.CubeCoefficients
import Praxis.Proofs.Classification.Descent
import Praxis.Proofs.Classification.Defect
import Praxis.Proofs.Classification.Reconstruct
import Praxis.Proofs.Classification.FiniteSupport
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Compress
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Coordinates
import Praxis.Proofs.Classification.Cubic
import Praxis.Proofs.Classification.Moore
import Praxis.Proofs.Classification.MooreSpan
import Praxis.Proofs.Classification.Tensor
import Praxis.Proofs.Classification.Transport
import Praxis.Proofs.Classification.WeightEquations
import Praxis.Proofs.Classification.ZCoordinates
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

open Praxis.Algebra (Vec)

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

theorem boolean_from_frame {S : Type*} [Fintype S]
    (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (hsym : ∀ c, (W c).IsSymm)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin v) = ⊥)
    (Ξ : Tri (KummerField P0) (Module.finrank (Fq P0) (jointSpace W)))
    (hu : slice Ξ (zeta v W (P0.m - 1)) = CU W)
    (hv : slice Ξ (zeta v W P0.m) = CV W)
    (hedge₁ : slice Ξ (zeta v W (P0.m - 1)) =
      slice (mapTri (kConj (P0.m - 1)).toRingHom Ξ) (zeta v W 0))
    (hedge₂ : slice Ξ (zeta v W P0.m) =
      slice (mapTri (kConj P0.m).toRingHom Ξ) (zeta v W 0))
    (hbool : ∀ h (j : Fin P0.N), Ξ h (Bext W j.succ) (Bext W j.succ - Bext W 0) = 0)
    (ξ : S → Fin (Module.finrank (Fq P0) (jointSpace W)) → Fq P0)
    (hnorm : ∀ s, coordIn (jointSpace W) (ξ s) 0 = 1)
    (hli : LinearIndependent (Fq P0) (fun s => Matrix.vecMulVec (ξ s) (ξ s)))
    (hliF : LinearIndependent (KummerField P0) (fun s => Matrix.vecMulVec
      (fun i => algebraMap (Fq P0) (KummerField P0) (ξ s i))
      (fun i => algebraMap (Fq P0) (KummerField P0) (ξ s i))))
    (c : S → KummerField P0)
    (hΞ : Ξ = ∑ s, c s • cube (fun i => algebraMap (Fq P0) (KummerField P0) (ξ s i))) :
    ∃ (xs : Finset (Vec (Fq P0) P0.N)) (ρ : Vec (Fq P0) P0.N → Fq P0),
      (∀ x ∈ xs, x ∈ jointSpace W ∧ x 0 = 1 ∧ ∀ j : Fin P0.N, x j.succ = 0 ∨ x j.succ = 1) ∧
      W = ∑ x ∈ xs, ρ x • honestStack v x := by
  classical
  have hxV (s : S) : coordIn (jointSpace W) (ξ s) ∈ jointSpace W :=
    (coordIn_range (jointSpace W)).le ⟨ξ s, rfl⟩
  have hz (s : S) : Z v (coordIn (jointSpace W) (ξ s)) ≠ 0 := by
    intro hz
    have hzero := Z_eq_zero_of_injective v (jointSpace W) hinj _ (hxV s) hz
    have hn := hnorm s
    rw [hzero, Pi.zero_apply] at hn
    exact zero_ne_one hn
  have hc₁ := cube_edge_coefficients (kConj (P0.m - 1)) c ξ hliF Ξ hΞ
    (zeta v W 0) (zeta v W (P0.m - 1)) hedge₁
  have hc₂ := cube_edge_coefficients (kConj P0.m) c ξ hliF Ξ hΞ
    (zeta v W 0) (zeta v W P0.m) hedge₂
  simp only [coordinate_zeta_dot, kConj_zero] at hc₁ hc₂
  have hdesc (s : S) := descend_cube_coefficient (c s) (Z v (coordIn (jointSpace W) (ξ s)))
    (hz s) (hc₁ s) (hc₂ s)
  choose r hr using hdesc
  have hΞr : Ξ = ∑ s,
      (algebraMap (Fq P0) (KummerField P0) (r s) * Z v (coordIn (jointSpace W) (ξ s))) •
        cube (fun i => algebraMap (Fq P0) (KummerField P0) (ξ s i)) := by
    simpa only [hr] using hΞ
  have hsupport (s : S) (hrs : r s ≠ 0) (j : Fin P0.N) :
      coordIn (jointSpace W) (ξ s) j.succ = 0 ∨ coordIn (jointSpace W) (ξ s) j.succ = 1 := by
    let κ : S → Fq P0 := fun a => coordIn (jointSpace W) (ξ a) j.succ *
      (coordIn (jointSpace W) (ξ a) j.succ - 1)
    have hnormF (a : S) : dotProduct (Bext W 0)
        (fun i => algebraMap (Fq P0) (KummerField P0) (ξ a i)) = 1 := by
      rw [Bext_coordinate_dot, hnorm, map_one]
    have hdef := cubic_defect_vector Ξ
      (fun a i => algebraMap (Fq P0) (KummerField P0) (ξ a i)) c hΞ
      (Bext W j.succ) (Bext W 0) hnormF (fun h => hbool h j)
    have hdef' : ∑ a,
        (algebraMap (Fq P0) (KummerField P0) (r a * κ a) * Z v (coordIn (jointSpace W) (ξ a))) •
          (fun i => algebraMap (Fq P0) (KummerField P0) (ξ a i)) = 0 := by
      refine Eq.trans ?_ hdef
      apply Finset.sum_congr rfl
      intro a _
      rw [hr, Bext_coordinate_dot]
      simp only [κ, map_mul, map_sub, map_one]
      apply congrArg (fun q : KummerField P0 =>
        q • (fun i => algebraMap (Fq P0) (KummerField P0) (ξ a i)))
      ring
    have hcoords (a : S) : dotProduct (fun i => toK (basisForms v (jointSpace W) i))
        (fun i => algebraMap (Fq P0) (KummerField P0) (ξ a i)) =
        Z v (coordIn (jointSpace W) (ξ a)) := by
      have h := Z_coordinate_sum v (jointSpace W) (ξ a)
      simpa only [dotProduct, mul_comm] using h.symm
    have hQ := defect_matrix_zero (basisForms v (jointSpace W))
      (basisForms_independent v (jointSpace W) hinj) ξ (fun a => r a * κ a)
      (fun a => Z v (coordIn (jointSpace W) (ξ a))) hcoords hdef'
    have he := Fintype.linearIndependent_iff.mp hli _ hQ s
    have hκ : κ s = 0 := (mul_eq_zero.mp he).resolve_left hrs
    rcases mul_eq_zero.mp hκ with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hW := reconstruct_decomposition v W hsym Ξ hu hv ξ r hΞr
  obtain ⟨xs, ρ, hxs, hsum⟩ := indexed_to_finset
    (fun s => coordIn (jointSpace W) (ξ s)) r (honestStack v)
    (fun x => x ∈ jointSpace W ∧ x 0 = 1 ∧ ∀ j : Fin P0.N, x j.succ = 0 ∨ x j.succ = 1)
    (fun s hs => ⟨hxV s, hnorm s, hsupport s hs⟩)
  exact ⟨xs, ρ, hxs, hW.trans hsum⟩

end

end Praxis.Proofs.Classification
