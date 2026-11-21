import Praxis.Proofs.Classification.Transport
import Praxis.Proofs.Classification.Annihilate
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Compress
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Moore
import Praxis.Proofs.Classification.Serialization
import Praxis.Params
import Praxis.Stack

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

section Generic

variable {F : Type*} [Field F] {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

theorem factor_entry (B : Matrix I J F) (C : Matrix J J F) (i j : I) :
    (B * C * B.transpose) i j = dotProduct (B i) (C.mulVec (B j)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

end Generic

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

theorem UField_boolean (W : Stack P0)
    (hbool : ∀ c (j : Fin P0.N), W c j.succ j.succ = W c 0 j.succ) (j : Fin P0.N) :
    UField W j.succ j.succ = UField W 0 j.succ := by
  unfold UField
  apply congrArg toK
  funext e
  simp only [polyU, stackU, Matrix.sum_apply]
  exact Finset.sum_congr rfl (fun c _ => hbool c j)

theorem VField_boolean (W : Stack P0)
    (hbool : ∀ c (j : Fin P0.N), W c j.succ j.succ = W c 0 j.succ) (j : Fin P0.N) :
    VField W j.succ j.succ = VField W 0 j.succ := by
  unfold VField
  apply congrArg toK
  funext e
  simp only [polyV]
  split_ifs
  · simp only [stackV, Matrix.sum_apply]
    exact Finset.sum_congr rfl (fun c _ => hbool c j)
  · rfl

theorem rowBoolean_factor {d : ℕ} (B : Matrix (Fin (P0.N + 1)) (Fin d) (KummerField P0))
    (C : Matrix (Fin d) (Fin d) (KummerField P0)) (hsym : C.IsSymm)
    (j : Fin P0.N)
    (hb : (B * C * B.transpose) j.succ j.succ = (B * C * B.transpose) 0 j.succ) :
    rowForm (B j.succ) C (B j.succ - B 0) = 0 := by
  rw [map_sub, rowForm_apply, rowForm_apply, ← factor_entry, ← factor_entry]
  have hs : (B * C * B.transpose).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
      hsym.eq, Matrix.mul_assoc]
  rw [hb, hs.apply 0 j.succ, sub_self]

theorem compressed_boolean (W : Stack P0) (hsym : ∀ c, (W c).IsSymm)
    (hbool : ∀ c (j : Fin P0.N), W c j.succ j.succ = W c 0 j.succ) :
    ∀ j : Fin P0.N,
      rowForm (Bext W j.succ) (CU W) (Bext W j.succ - Bext W 0) = 0 ∧
      rowForm (Bext W j.succ) (CV W) (Bext W j.succ - Bext W 0) = 0 ∧
      rowForm (Bext W j.succ) ((CU W).map (kConj (P0.m + 1))) (Bext W j.succ - Bext W 0) = 0 := by
  intro j
  refine ⟨rowBoolean_factor _ _ (CU_symm W hsym) j ?_,
    rowBoolean_factor _ _ (CV_symm W hsym) j ?_, rowBoolean_factor _ _ ?_ j ?_⟩
  · rw [← UField_factor W hsym]
    exact UField_boolean W hbool j
  · rw [← VField_factor W hsym]
    exact VField_boolean W hbool j
  · change ((CU W).map (kConj (P0.m + 1))).transpose = _
    rw [← Matrix.transpose_map, (CU_symm W hsym).eq]
  · rw [← UField_conj_factor W hsym]
    exact congrArg (kConj (P0.m + 1)) (UField_boolean W hbool j)

end

end Praxis.Proofs.Classification
