import Praxis.Proofs.Classification.Compress
import Praxis.Proofs.Classification.ZCoordinates
import Praxis.Grid
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Coeff
import Praxis.Proofs.Classification.CoeffMul
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Coordinates
import Praxis.Proofs.Classification.Moore
import Praxis.Proofs.Classification.MooreSpan
import Praxis.Proofs.Classification.PolyMatrix
import Praxis.Proofs.Classification.Serialization
import Praxis.Proofs.Classification.WeightEquations
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

theorem frob_dot {k : Type*} [CommSemiring k] {n : ℕ} {I : Type*} [Fintype I]
    (β : k) (s : ℕ) (v : Fin n → I → k) (x : I → k) :
    frob β s (fun e => dotProduct (v e) x) = fun e => dotProduct (frob β s v e) x := by
  funext e
  simp only [frob, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def fieldForms (v : Fin P0.n → Vec (Fq P0) P0.N) (s : ℕ) :
    Fin (P0.N + 1) → KummerField P0 := fun i => toK (fun e => sigma P0 s v e i)

def zeta (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (s : ℕ) :
    Fin (Module.finrank (Fq P0) (jointSpace W)) → KummerField P0 :=
  fun r => toK (sigma P0 s (basisForms v (jointSpace W) r))

theorem fieldForms_dot (v : Fin P0.n → Vec (Fq P0) P0.N) (s : ℕ)
    (x : Vec (Fq P0) P0.N) :
    dotProduct (fieldForms v s) (fun i => algebraMap (Fq P0) (KummerField P0) (x i)) =
      kConj s (Z v x) := by
  unfold fieldForms
  rw [Z, kConj_toK]
  have hz : sigma P0 s (zOf v x) = fun e => dotProduct (sigma P0 s v e) x := by
    exact frob_dot (betaF P0) s v x
  rw [hz, ← evalCoeffs_root, evalCoeffs_dot]
  simp only [evalCoeffs_root]

theorem basisMat_entry {k : Type*} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    (V : Submodule k (I → k)) (i : I) (r : Fin (Module.finrank k V)) :
    basisMat V i r = (Module.finBasis k V r : I → k) i := by
  rw [basisMat, LinearMap.toMatrix'_apply]
  simp only [coordIn, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.equivFun_symm_apply, Pi.single_apply]
  simp

theorem basisForms_apply {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (V : Submodule (Fq P) (Vec (Fq P) P.N))
    (r : Fin (Module.finrank (Fq P) V)) :
    basisForms v V r = zOf v (Module.finBasis (Fq P) V r) := by
  rw [basisForms, restrictedForms, LinearMap.comp_apply, Submodule.subtype_apply, zLin_eq_zOf]

theorem Bext_fieldForms (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (s : ℕ) :
    (Bext W).transpose.mulVec (fieldForms v s) = zeta v W s := by
  funext r
  simp only [zeta, basisForms_apply, ← kConj_toK]
  unfold Bext
  simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, basisMat_entry]
  exact (dotProduct_comm _ _).trans (fieldForms_dot v s
    (Module.finBasis (Fq P0) (jointSpace W) r))

theorem matrix_sigma_toK (p : KPoly (Algebra.Mat (Fq P0) P0.N) P0.n) (s : ℕ) (i j : Fin (P0.N + 1)) :
    toK (fun e => sigma P0 s p e i j) = kConj s (toK (fun e => p e i j)) := by
  rw [kConj_toK]
  apply congrArg toK
  funext e
  simp only [sigma, frob, Matrix.smul_apply, smul_eq_mul]

theorem reduceP_sub {k M : Type*} [Ring k] [AddCommGroup M] [Module k M]
    (n : ℕ) (c : k) (p q : ℕ → M) :
    reduceP n c (p - q) = reduceP n c p - reduceP n c q := by
  funext e
  simp only [reduceP, Pi.sub_apply, smul_sub]
  abel

theorem reduced_tie_field (M N : KPoly (Algebra.Mat (Fq P0) P0.N) P0.n)
    (b d : KPoly (Vec (Fq P0) P0.N) P0.n)
    (h : reduceP P0.n (c0F P0) (rawMulMV M b - rawMulMV N d) = 0) :
    (Matrix.of (fun i j => toK (fun e => M e i j))).mulVec (fun j => toK (fun e => b e j)) =
      (Matrix.of (fun i j => toK (fun e => N e i j))).mulVec (fun j => toK (fun e => d e j)) := by
  funext i
  have hh := congrArg (fun p : KPoly (Vec (Fq P0) P0.N) P0.n => toK (fun e => p e i)) h
  rw [reduceP_sub] at hh
  simp only [Pi.sub_apply, Pi.zero_apply] at hh
  change toK ((fun e => reduceP P0.n (c0F P0) (rawMulMV M b) e i) -
      (fun e => reduceP P0.n (c0F P0) (rawMulMV N d) e i)) = toK 0 at hh
  rw [toK_sub, toK_zero, toK_reduce_mulVec, toK_reduce_mulVec] at hh
  exact sub_eq_zero.mp hh

theorem ambient_ties (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0) (hties : Ties v W) :
    (UField W).mulVec (fieldForms v P0.m) = (VField W).mulVec (fieldForms v (P0.m - 1)) ∧
    (UField W).mulVec (fieldForms v (P0.m + 1)) =
      ((UField W).map (kConj (P0.m + 1))).mulVec (fieldForms v (P0.m - 1)) ∧
    (VField W).mulVec (fieldForms v (P0.m + 1)) =
      ((UField W).map (kConj (P0.m + 1))).mulVec (fieldForms v P0.m) := by
  have h₁ := reduced_tie_field _ _ _ _ (hties .t1)
  have h₂ := reduced_tie_field _ _ _ _ (hties .t2)
  have h₃ := reduced_tie_field _ _ _ _ (hties .t3)
  simp only [matrix_sigma_toK] at h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

theorem Bext_cancel_vec (W : Stack P0)
    (a b : Fin (Module.finrank (Fq P0) (jointSpace W)) → KummerField P0)
    (h : (Bext W).mulVec a = (Bext W).mulVec b) : a = b := by
  have hh := congrArg (Lext W).mulVec h
  simpa only [Matrix.mulVec_mulVec, Lext_Bext, Matrix.one_mulVec] using hh

theorem UField_conj_factor (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) (s : ℕ) :
    (UField W).map (kConj s) = Bext W * (CU W).map (kConj s) * (Bext W).transpose := by
  rw [UField_factor W hsym]
  simp only [Matrix.map_mul, Matrix.transpose_map, Bext_fixed]

theorem compressed_ties (v : Fin P0.n → Vec (Fq P0) P0.N) (W : Stack P0)
    (hsym : ∀ c, (W c).IsSymm) (hties : Ties v W) :
    (CU W).mulVec (zeta v W P0.m) = (CV W).mulVec (zeta v W (P0.m - 1)) ∧
    (CU W).mulVec (zeta v W (P0.m + 1)) =
      ((CU W).map (kConj (P0.m + 1))).mulVec (zeta v W (P0.m - 1)) ∧
    (CV W).mulVec (zeta v W (P0.m + 1)) =
      ((CU W).map (kConj (P0.m + 1))).mulVec (zeta v W P0.m) := by
  obtain ⟨h₁, h₂, h₃⟩ := ambient_ties v W hties
  rw [UField_factor W hsym, VField_factor W hsym] at h₁
  rw [UField_conj_factor W hsym, UField_factor W hsym] at h₂
  rw [UField_conj_factor W hsym, VField_factor W hsym] at h₃
  simp only [← Matrix.mulVec_mulVec, Bext_fieldForms] at h₁ h₂ h₃
  exact ⟨Bext_cancel_vec W _ _ h₁, Bext_cancel_vec W _ _ h₂, Bext_cancel_vec W _ _ h₃⟩

end

end Praxis.Proofs.Classification
