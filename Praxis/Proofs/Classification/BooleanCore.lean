import Praxis.Proofs.Classification.BooleanSupport
import Praxis.Proofs.Classification.SpaceFrame
import Praxis.Proofs.Classification.ZeroConstant
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Compress
import Praxis.Proofs.Classification.Coordinates
import Praxis.Proofs.Classification.Extend
import Praxis.Proofs.Classification.Frame
import Praxis.Proofs.Classification.LocalCubic
import Praxis.Proofs.Classification.RationalCubes
import Praxis.Proofs.Classification.RationalZero
import Praxis.Proofs.Classification.Transport
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

theorem stack_zero_of_joint_bot {P : Params} (W : Stack P) (hV : jointSpace W = ⊥) : W = 0 := by
  classical
  funext c i j
  have hx : (W c).mulVec (Pi.single j 1) ∈ jointSpace W :=
    cell_range_le W c ⟨Pi.single j 1, rfl⟩
  rw [hV, Submodule.mem_bot] at hx
  have h := congrFun hx i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply, Matrix.zero_apply] using h

theorem empty_boolean_decomposition (v : Fin P0.n → Vec (Fq P0) P0.N)
    (W : Stack P0) (hW : W = 0) :
    ∃ (xs : Finset (Vec (Fq P0) P0.N)) (ρ : Vec (Fq P0) P0.N → Fq P0),
      (∀ x ∈ xs, x ∈ jointSpace W ∧ x 0 = 1 ∧ ∀ j : Fin P0.N, x j.succ = 0 ∨ x j.succ = 1) ∧
      W = ∑ x ∈ xs, ρ x • honestStack v x := by
  exact ⟨∅, fun _ => 0, by simp, by simpa using hW⟩

theorem frame_rows (W : Stack P0)
    (e : (Fin (Module.finrank (Fq P0) (jointSpace W)) → Fq P0) ≃ₗ[Fq P0]
      (Fin (Module.finrank (Fq P0) (jointSpace W)) → Fq P0))
    (idx : Fin (Module.finrank (Fq P0) (jointSpace W)) → Fin (P0.N + 1))
    (he : ∀ a j, e a j = coordIn (jointSpace W) a (idx j))
    (j : Fin (Module.finrank (Fq P0) (jointSpace W))) :
    frameMatrix (F := KummerField P0) e j = Bext W (idx j) := by
  funext r
  change algebraMap (Fq P0) (KummerField P0) (equivMatrix e j r) =
    algebraMap (Fq P0) (KummerField P0) (basisMat (jointSpace W) (idx j) r)
  rw [frame_matrix_entry (jointSpace W) e idx he]

theorem boolean_core (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (hsym : ∀ c, (W c).IsSymm)
    (hbool : ∀ c (j : Fin P0.N), W c j.succ j.succ = W c 0 j.succ)
    (hties : Ties v W) (hdim : Module.finrank (Fq P0) (jointSpace W) ≤ dimMax)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin v) = ⊥) :
    ∃ (xs : Finset (Vec (Fq P0) P0.N)) (ρ : Vec (Fq P0) P0.N → Fq P0),
      (∀ x ∈ xs, x ∈ jointSpace W ∧ x 0 = 1 ∧ ∀ j : Fin P0.N, x j.succ = 0 ∨ x j.succ = 1) ∧
      W = ∑ x ∈ xs, ρ x • honestStack v x := by
  classical
  by_cases hV : jointSpace W = ⊥
  · exact empty_boolean_decomposition v W (stack_zero_of_joint_bot W hV)
  have hd : 0 < Module.finrank (Fq P0) (jointSpace W) :=
    Nat.pos_of_ne_zero (fun h => hV (Submodule.finrank_eq_zero.mp h))
  obtain ⟨Ξ, hsymΞ, hu, hv, hp, hb⟩ := local_cubic v W hsym hbool hties hdim hinj
  obtain ⟨he₁, he₂⟩ := local_cubic_edges v W hsym Ξ hu hv hp
  have hbAll : ∀ h (i : Fin (P0.N + 1)), Ξ h (Bext W i) (Bext W i - Bext W 0) = 0 := by
    intro h i
    refine Fin.cases ?_ (fun j => hb h j) i
    simp only [sub_self, map_zero]
  by_cases hconst : evalAt (jointSpace W) (0 : Fin (P0.N + 1)) = 0
  · have hB0 : Bext W 0 = 0 := by
      funext r
      have hz := congrArg (fun f => f (Module.finBasis (Fq P0) (jointSpace W) r)) hconst
      have hz' : basisMat (jointSpace W) 0 r = 0 := by
        simpa only [basisMat_entry, evalAt_apply, LinearMap.zero_apply] using hz
      change algebraMap (Fq P0) (KummerField P0) (basisMat (jointSpace W) 0 r) = 0
      rw [hz', map_zero]
    have hbDiag : ∀ h i, Ξ h (Bext W i) (Bext W i) = 0 := by
      intro h i
      simpa only [hB0, sub_zero] using hbAll h i
    obtain ⟨x, hx, hx0⟩ := (jointSpace W).ne_bot_iff.mp hV
    have hex : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx0 (funext h)
    obtain ⟨i, hi⟩ := hex
    have hei : evalAt (jointSpace W) i ≠ 0 := by
      intro h
      have hz := congrArg (fun f => f (⟨x, hx⟩ : jointSpace W)) h
      exact hi (by simpa only [evalAt_apply, LinearMap.zero_apply] using hz)
    obtain ⟨e, idx, j₀, hj₀, hidx, he⟩ := coordinate_frame (jointSpace W) i hei
    have hbFrame : ∀ h j, Ξ h (frameMatrix (F := KummerField P0) e j)
        (frameMatrix (F := KummerField P0) e j) = 0 := by
      intro h j
      rw [frame_rows W e idx he]
      exact hbDiag h (idx j)
    rcases rational_zero_shape hd hdim e Ξ hsymΞ hbFrame with hΞ | ⟨t, M, h3, ht, hM, hfix⟩
    · exact empty_boolean_decomposition v W (stack_zero_of_cubic_zero v W hsym Ξ hu hv hΞ)
    · have ht0 : t = 0 := cubic_triangle_zero v W hinj h3 M hM hfix t
        (by simpa only [ht] using he₁) (by simpa only [ht] using he₂)
      have hΞ : Ξ = 0 := by rw [ht, ht0, zero_smul]
      exact empty_boolean_decomposition v W (stack_zero_of_cubic_zero v W hsym Ξ hu hv hΞ)
  · obtain ⟨e, idx, j₀, hj₀, hidx, he⟩ := coordinate_frame (jointSpace W) 0 hconst
    have hj : (⟨0, hd⟩ : Fin (Module.finrank (Fq P0) (jointSpace W))) = j₀ :=
      Fin.ext hj₀.symm
    have hbFrame : ∀ h j, Ξ h (frameMatrix (F := KummerField P0) e j)
        (frameMatrix (F := KummerField P0) e j - frameMatrix (F := KummerField P0) e ⟨0, hd⟩) = 0 := by
      intro h j
      rw [frame_rows W e idx he, frame_rows W e idx he, hj, hidx]
      exact hbAll h (idx j)
    obtain ⟨c, hc⟩ := rational_frame_cubes hd hdim e Ξ hsymΞ hbFrame
    have hnorm := frame_point_normalized (jointSpace W) 0 e idx j₀ hj₀ hidx he
    have hli : LinearIndependent (Fq P0) (fun s =>
        Matrix.vecMulVec (framePoint e s) (framePoint e s)) := by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
        frame_squares_independent (F := Fq P0) hd hdim e
    exact boolean_from_frame v W hsym hinj Ξ hu hv he₁ he₂ hb (framePoint e) hnorm hli
      (frame_squares_independent (F := KummerField P0) hd hdim e) c hc

end

end Praxis.Proofs.Classification
