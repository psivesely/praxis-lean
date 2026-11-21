import Praxis.Proofs.Classification.PolyMatrix
import Praxis.Proofs.Classification.Coordinates
import Praxis.Grid
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.CoeffMul
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Serialization
import Praxis.Params
import Praxis.Setting
import Praxis.Stack

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

def compressedCell (W : Stack P0) (c : Cell P0) :=
  leftMat (jointSpace W) * W c * (leftMat (jointSpace W)).transpose

def CU (W : Stack P0) :=
  evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleU (compressedCell W))

def CV (W : Stack P0) :=
  evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleV (compressedCell W))

def Bext (W : Stack P0) := (basisMat (jointSpace W)).map (algebraMap (Fq P0) (KummerField P0))

def Lext (W : Stack P0) := (leftMat (jointSpace W)).map (algebraMap (Fq P0) (KummerField P0))

theorem Lext_Bext (W : Stack P0) : Lext W * Bext W = 1 := by
  rw [Lext, Bext, ← Matrix.map_mul, leftMat_basisMat, Matrix.map_one] <;> simp only [map_zero, map_one]

theorem compressedCell_symm (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) (c : Cell P0) :
    (compressedCell W c).IsSymm := by
  dsimp [compressedCell, Matrix.IsSymm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, (hsym c).eq, Matrix.mul_assoc]

theorem compressedCell_factor (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) (c : Cell P0) :
    W c = basisMat (jointSpace W) * compressedCell W c * (basisMat (jointSpace W)).transpose :=
  symmetric_factorization_explicit _ _ (hsym c) (cell_range_le W c)

theorem evalMatrix_assembleU (W : Stack P0) :
    evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleU W) = UField W := by
  ext i j
  rw [evalMatrix, evalCoeffs_root]
  rfl

theorem evalMatrix_assembleV (W : Stack P0) :
    evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleV W) = VField W := by
  ext i j
  rw [evalMatrix, evalCoeffs_root]
  rfl

theorem UField_factor (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) :
    UField W = Bext W * CU W * (Bext W).transpose := by
  have hW : W = (fun c => basisMat (jointSpace W) * compressedCell W c *
      (basisMat (jointSpace W)).transpose) := funext (compressedCell_factor W hsym)
  calc
    UField W = evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleU W) :=
      (evalMatrix_assembleU W).symm
    _ = evalMatrix (AdjoinRoot.root (KummerPoly P0))
        (assembleU (fun c => basisMat (jointSpace W) * compressedCell W c *
          (basisMat (jointSpace W)).transpose)) := congrArg (fun W' : Stack P0 =>
          evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleU W')) hW
    _ = _ := by
      rw [assembleU_factor, evalMatrix_mul_right, evalMatrix_mul_left]
      rfl

theorem VField_factor (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) :
    VField W = Bext W * CV W * (Bext W).transpose := by
  have hW : W = (fun c => basisMat (jointSpace W) * compressedCell W c *
      (basisMat (jointSpace W)).transpose) := funext (compressedCell_factor W hsym)
  calc
    VField W = evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleV W) :=
      (evalMatrix_assembleV W).symm
    _ = evalMatrix (AdjoinRoot.root (KummerPoly P0))
        (assembleV (fun c => basisMat (jointSpace W) * compressedCell W c *
          (basisMat (jointSpace W)).transpose)) := congrArg (fun W' : Stack P0 =>
          evalMatrix (AdjoinRoot.root (KummerPoly P0)) (assembleV W')) hW
    _ = _ := by
      rw [assembleV_factor, evalMatrix_mul_right, evalMatrix_mul_left]
      rfl

theorem CU_symm (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) : (CU W).IsSymm :=
  evalMatrix_symm _ _ (assembleU_symm _ (compressedCell_symm W hsym))

theorem CV_symm (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) : (CV W).IsSymm :=
  evalMatrix_symm _ _ (assembleV_symm _ (compressedCell_symm W hsym))

theorem Bext_fixed (W : Stack P0) (s : ℕ) : (Bext W).map (kConj s) = Bext W := by
  ext i j
  simp only [Bext, Matrix.map_apply, AlgHom.commutes]

theorem factor_cancel (W : Stack P0)
    (C D : Matrix (Fin (Module.finrank (Fq P0) (jointSpace W)))
      (Fin (Module.finrank (Fq P0) (jointSpace W))) (KummerField P0))
    (h : Bext W * C * (Bext W).transpose = Bext W * D * (Bext W).transpose) : C = D := by
  have hleft := congrArg (fun M => Lext W * M) h
  simp only [← Matrix.mul_assoc, Lext_Bext, Matrix.one_mul] at hleft
  have hright := congrArg (fun M => M * (Lext W).transpose) hleft
  simpa only [Matrix.mul_assoc, ← Matrix.transpose_mul, Lext_Bext,
    Matrix.transpose_one, Matrix.mul_one] using hright

theorem CV_fixed (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) :
    (CV W).map (kConj P0.m) = CV W := by
  apply factor_cancel W
  calc
    Bext W * (CV W).map (kConj P0.m) * (Bext W).transpose =
        (Bext W * CV W * (Bext W).transpose).map (kConj P0.m) := by
      simp only [Matrix.map_mul, Matrix.transpose_map, Bext_fixed]
    _ = (VField W).map (kConj P0.m) := congrArg (fun M => M.map (kConj P0.m)) (VField_factor W hsym).symm
    _ = VField W := VField_fixed W
    _ = Bext W * CV W * (Bext W).transpose := VField_factor W hsym

end

end Praxis.Proofs.Classification
