import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Trim.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.AdditiveChain
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GridTrim

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

open Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

namespace Praxis.Algebra.Trans

def PrimitiveMatrix {n q : ℕ} (K : Matrix (Fin n) (Fin q) ℤ) : Prop :=
  Algebra.VectorInverse.PrimitiveRows K

def realMatrix {n q : ℕ} (K : Matrix (Fin n) (Fin q) ℤ) :
    Matrix (Fin n) (Fin q) ℝ := K.map (Int.castRingHom ℝ)

def ratMatrix {n q : ℕ} (K : Matrix (Fin n) (Fin q) ℤ) :
    Matrix (Fin n) (Fin q) ℚ := K.map (Int.castRingHom ℚ)

def oldBlock {r q : ℕ} (K : Matrix (Fin (r+1)) (Fin q) ℤ) :
    Matrix (Fin r) (Fin q) ℤ := K.submatrix Fin.castSucc id

def rationalNormal {α : Type} {n : ℕ} (S : Finset α) (f : α → Fin n → ℚ)
    (z : Fin n → ℚ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, dotProduct z (f x - f y) = 0

structure TransitionInput (n r q : ℕ) where
  grids : Fin (n+1) → ℕ
  old : Matrix (Fin n) (Fin r) ℤ
  normal : Matrix (Fin (n+1)) (Fin q) ℤ
  imageNormal : Matrix (Fin (r+1)) (Fin q) ℤ
  event : Finset (Grid grids)

namespace TransitionInput

variable {n r q : ℕ} (T : TransitionInput n r q)

def oldGrids : Fin n → ℕ := fun i => T.grids i.castSucc

def oldPoint (x : Grid T.grids) : Grid T.oldGrids := fun i => x i.castSucc

def sourceQ (x : Grid T.grids) : Fin (n+1) → ℚ := fun i => (x i : ℕ)

def imageQ (x : Grid T.grids) : Fin (r+1) → ℚ :=
  Fin.snoc (fun j => ∑ i, (T.old i j : ℚ) * (x i.castSucc : ℕ))
    ((x (Fin.last n) : ℕ) : ℚ)

def pullbackQ (u : Fin (r+1) → ℚ) : Fin (n+1) → ℚ :=
  Fin.snoc (fun i => ∑ j, (T.old i j : ℚ) * u j.castSucc) (u (Fin.last r))

def pulledNormal : Matrix (Fin (n+1)) (Fin q) ℤ :=
  Fin.snoc (T.old * oldBlock T.imageNormal) (T.imageNormal (Fin.last r))

def density : ℝ := (T.event.card : ℝ) / Fintype.card (Grid T.grids)

def oldHeight : ℕ := height T.old

def newHeight : ℕ := height T.normal

def oldMass : ℝ := mass T.oldGrids (imageZ T.oldGrids T.old)

def sigma : Matrix (Fin r) (Fin r) ℝ :=
  Analysis.gridCovariance T.oldGrids (realMatrix T.old)

def center : Fin r → ℝ := fun j =>
  ∑ i, (T.old i j : ℝ) * ((T.oldGrids i : ℝ)-1)/2

def OldLattice : Prop := PrimitiveMatrix T.old

def TrimmedEvent (P : VITData) : Prop := T.event.Nonempty ∧
  ∀ x ∈ T.event, Analysis.mahalanobisSq T.sigma T.center
    (fun j => (imageZ T.oldGrids T.old (T.oldPoint x) j : ℝ)) ≤ P.R^2

def OrdinaryNormals : Prop := PrimitiveMatrix T.normal ∧
  ∀ z, rationalNormal T.event T.sourceQ z ↔
    ∃ a : Fin q → ℚ, z = (ratMatrix T.normal).mulVec a

def WholeNormalPullback : Prop := ∀ z,
  rationalNormal T.event T.sourceQ z ↔
    ∃ u, rationalNormal T.event T.imageQ u ∧ z = T.pullbackQ u

def ImageNormals : Prop := PrimitiveMatrix T.imageNormal ∧
  (∀ z, rationalNormal T.event T.imageQ z ↔
    ∃ a : Fin q → ℚ, z = (ratMatrix T.imageNormal).mulVec a) ∧
  ∃ pivot : Fin q → Fin r, ((oldBlock T.imageNormal).submatrix pivot id).det ≠ 0

def OldMaximalMinor : Prop := ∃ pivot : Fin q → Fin n,
  ((T.normal.submatrix (fun j => (pivot j).castSucc) id).det).natAbs = T.newHeight

def GridBounds (P : VITData) : Prop :=
  (∀ i, 0 < T.grids i) ∧ (∑ i, (T.grids i : ℝ)^2) ≤ (P.g : ℝ)^2 * P.S

end TransitionInput

def TransitionData (r q : ℕ) (P : VITData) {n : ℕ} (T : TransitionInput n r q) : Prop :=
  T.OldLattice ∧ T.TrimmedEvent P ∧ T.OrdinaryNormals ∧ T.WholeNormalPullback ∧
    T.ImageNormals ∧ T.OldMaximalMinor ∧ T.GridBounds P

def NormalPullback : Prop :=
  ∀ n r q (P : VITData) (T : TransitionInput n r q), TransitionData r q P T →
    ∃ (A : Matrix (Fin q) (Fin q) ℤ) (h : ℕ) (pivot : Fin q → Fin n),
      T.pulledNormal = T.normal * A ∧ A.det.natAbs = h ∧ 1 ≤ h ∧
      ((T.normal.submatrix (fun j => (pivot j).castSucc) id).det).natAbs = T.newHeight ∧
      ((T.pulledNormal.submatrix (fun j => (pivot j).castSucc) id).det).natAbs = h*T.newHeight

def Transition32 (P : VITParameters) : Prop :=
  PlanarCount → SectionCount3 → Algebra.Trim.TrimForIntLat →
  ∀ n (T : TransitionInput n 3 2), TransitionData 3 2 P.toVITData T →
    T.density * T.newHeight ≤ P.D * P.g * T.oldHeight * T.oldMass

def Transition21 (P : VITParameters) : Prop :=
  PlanarCount → SectionCount3 → Algebra.Trim.TrimForIntLat →
  ∀ n (T : TransitionInput n 2 1), TransitionData 2 1 P.toVITData T →
    T.density * T.newHeight ≤ P.D * P.g * T.oldHeight * T.oldMass

def Transition31 (P : VITParameters) : Prop :=
  PlanarCount → SectionCount3 → Algebra.Trim.TrimForIntLat →
  ∀ n (T : TransitionInput n 3 1), TransitionData 3 1 P.toVITData T →
    T.density * T.newHeight ≤ P.E * (P.g : ℝ)^2 * T.oldHeight * T.oldMass

end Praxis.Algebra.Trans
