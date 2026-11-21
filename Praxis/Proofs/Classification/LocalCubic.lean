import Praxis.Proofs.Classification.RowBoolean
import Praxis.Proofs.Classification.Tensor
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Coeff
import Praxis.Proofs.Classification.Compress
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Cubic
import Praxis.Proofs.Classification.MooreSpan
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

theorem local_cubic (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (hsym : ∀ c, (W c).IsSymm)
    (hbool : ∀ c (j : Fin P0.N), W c j.succ j.succ = W c 0 j.succ)
    (hties : Ties v W) (hdim : Module.finrank (Fq P0) (jointSpace W) ≤ dimMax)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin v) = ⊥) :
    ∃ Ξ : Tri (KummerField P0) (Module.finrank (Fq P0) (jointSpace W)),
      SymTri Ξ ∧
      slice Ξ (zeta v W (P0.m - 1)) = CU W ∧
      slice Ξ (zeta v W P0.m) = CV W ∧
      slice Ξ (zeta v W (P0.m + 1)) = (CU W).map (kConj (P0.m + 1)) ∧
      ∀ h (j : Fin P0.N), Ξ h (Bext W j.succ) (Bext W j.succ - Bext W 0) = 0 := by
  let h : Fin 3 → Fin (Module.finrank (Fq P0) (jointSpace W)) → KummerField P0 :=
    fun j => zeta v W (P0.m - 1 + j.val)
  let M : Fin 3 → Matrix (Fin (Module.finrank (Fq P0) (jointSpace W)))
      (Fin (Module.finrank (Fq P0) (jointSpace W))) (KummerField P0) :=
    fun j => if j.val = 0 then CU W else if j.val = 1 then CV W else (CU W).map (kConj (P0.m + 1))
  have hh₀ : h 0 = zeta v W (P0.m - 1) := by simp only [h, Fin.val_zero, Nat.add_zero]
  have hh₁ : h 1 = zeta v W P0.m := by
    simp only [h, Fin.val_one, show P0.m - 1 + 1 = P0.m by decide]
  have hh₂ : h 2 = zeta v W (P0.m + 1) := by
    change zeta v W (P0.m - 1 + 2) = _
    rw [show P0.m - 1 + 2 = P0.m + 1 by decide]
  have hspan : Submodule.span (KummerField P0) (Set.range h) = ⊤ := by
    unfold h zeta
    exact moore_three_span _ (basisForms_independent v (jointSpace W) hinj) hdim (P0.m - 1)
  obtain ⟨ht₁, ht₂, ht₃⟩ := compressed_ties v W hsym hties
  have hsymM : ∀ j, (M j).IsSymm := by
    intro j
    fin_cases j
    · simpa [M] using CU_symm W hsym
    · simpa [M] using CV_symm W hsym
    · have hsplus : ((CU W).map (kConj (P0.m + 1))).IsSymm := by
        change ((CU W).map (kConj (P0.m + 1))).transpose = _
        rw [← Matrix.transpose_map, (CU_symm W hsym).eq]
      simpa [M] using hsplus
  have hM₀ : M 0 = CU W := by simp [M]
  have hM₁ : M 1 = CV W := by simp [M]
  have hM₂ : M 2 = (CU W).map (kConj (P0.m + 1)) := by simp [M]
  have hcompat : ∀ r s, (M r).mulVec (h s) = (M s).mulVec (h r) := by
    intro r s
    fin_cases r <;> fin_cases s
    · rfl
    · simpa [M, h, show P0.m - 1 + 1 = P0.m by decide, show P0.m - 1 + 2 = P0.m + 1 by decide] using ht₁
    · simpa [M, h, show P0.m - 1 + 1 = P0.m by decide, show P0.m - 1 + 2 = P0.m + 1 by decide] using ht₂
    · simpa [M, h, show P0.m - 1 + 1 = P0.m by decide, show P0.m - 1 + 2 = P0.m + 1 by decide] using ht₁.symm
    · rfl
    · simpa [M, h, show P0.m - 1 + 1 = P0.m by decide, show P0.m - 1 + 2 = P0.m + 1 by decide] using ht₃
    · simpa [M, h, show P0.m - 1 + 1 = P0.m by decide, show P0.m - 1 + 2 = P0.m + 1 by decide] using ht₂.symm
    · simpa [M, h, show P0.m - 1 + 1 = P0.m by decide, show P0.m - 1 + 2 = P0.m + 1 by decide] using ht₃.symm
    · rfl
  obtain ⟨Ξ, hΞsym, hΞ⟩ := compatible_cubic h M hspan hsymM hcompat
  refine ⟨Ξ, hΞsym, ?_, ?_, ?_, ?_⟩
  · simpa [hh₀, M] using hΞ 0
  · simpa [hh₁, M] using hΞ 1
  · simpa [hh₂, M] using hΞ 2
  · intro x j
    apply tri_vanish_on_span Ξ h hspan (Bext W j.succ) (Bext W j.succ - Bext W 0) _ x
    intro r
    rw [tri_slice_eval, hΞ r]
    obtain ⟨hb₁, hb₂, hb₃⟩ := compressed_boolean W hsym hbool j
    fin_cases r
    · simpa [M] using hb₁
    · simpa [M] using hb₂
    · simpa [M] using hb₃

theorem zeta_conj (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (s t : ℕ) :
    (fun i => kConj s (zeta v W t i)) = zeta v W (s + t) := by
  funext i
  simp only [zeta, kConj_toK, ← sigma_add]

theorem zeta_n (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) :
    zeta v W P0.n = zeta v W 0 := by
  funext i
  simp only [zeta, sigma_n, sigma_zero]

theorem local_cubic_edges (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (hsym : ∀ c, (W c).IsSymm)
    (Ξ : Tri (KummerField P0) (Module.finrank (Fq P0) (jointSpace W)))
    (hu : slice Ξ (zeta v W (P0.m - 1)) = CU W)
    (hv : slice Ξ (zeta v W P0.m) = CV W)
    (hp : slice Ξ (zeta v W (P0.m + 1)) = (CU W).map (kConj (P0.m + 1))) :
    (slice Ξ (zeta v W (P0.m - 1)) =
      slice (mapTri (kConj (P0.m - 1)).toRingHom Ξ) (zeta v W 0)) ∧
    (slice Ξ (zeta v W P0.m) =
      slice (mapTri (kConj P0.m).toRingHom Ξ) (zeta v W 0)) := by
  constructor
  · have hs := slice_mapTri (kConj (P0.m - 1)).toRingHom Ξ (zeta v W (P0.m + 1))
    have hz : (fun i => (kConj (P0.m - 1)).toRingHom (zeta v W (P0.m + 1) i)) = zeta v W 0 := by
      have hz' := zeta_conj v W (P0.m - 1) (P0.m + 1)
      rw [show (P0.m - 1) + (P0.m + 1) = P0.n by decide, zeta_n] at hz'
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hz'
    rw [hz] at hs
    have hm : (slice Ξ (zeta v W (P0.m + 1))).map (kConj (P0.m - 1)).toRingHom = CU W := by
      ext i j
      rw [hp, Matrix.map_apply, Matrix.map_apply]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ← kConj_add,
        show (P0.m - 1) + (P0.m + 1) = P0.n by decide, kConj_n]
    exact hu.trans (hs.trans hm).symm
  · have hs := slice_mapTri (kConj P0.m).toRingHom Ξ (zeta v W P0.m)
    have hz : (fun i => (kConj P0.m).toRingHom (zeta v W P0.m i)) = zeta v W 0 := by
      have hz' := zeta_conj v W P0.m P0.m
      rw [show P0.m + P0.m = P0.n by decide, zeta_n] at hz'
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hz'
    rw [hz] at hs
    have hm : (slice Ξ (zeta v W P0.m)).map (kConj P0.m).toRingHom = CV W := by
      ext i j
      rw [hv, Matrix.map_apply]
      have hc := congrFun (congrFun (CV_fixed W hsym) i) j
      simpa only [Matrix.map_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hc
    exact hv.trans (hs.trans hm).symm

end

end Praxis.Proofs.Classification
