import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section

open Module MeasureTheory

open scoped BigOperators

namespace Praxis.Algebra.Point

abbrev E (e : ℕ) := EuclideanSpace ℝ (Fin e)

structure FullLat (e : ℕ) where
  carrier : Submodule ℤ (E e)
  discrete : DiscreteTopology carrier
  isZLattice : letI := discrete; IsZLattice ℝ carrier

attribute [instance] FullLat.discrete FullLat.isZLattice

def FullLat.det {e : ℕ} (L : FullLat e) : ℝ := ZLattice.covolume L.carrier

def volHull {e : ℕ} (S : Finset (E e)) : ℝ :=
  (volume (convexHull ℝ (S : Set (E e)))).toReal

def spanDim {e : ℕ} (S : Finset (E e)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (S : Set (E e)))

def InCoset {e : ℕ} (L : FullLat e) (a : E e) (S : Finset (E e)) : Prop :=
  ∀ x ∈ S, x - a ∈ L.carrier

def simplexPoints {e : ℕ} (v : Fin (e + 1) → E e) : Finset (E e) :=
  Finset.univ.image v

def edgeVectors {e : ℕ} (v : Fin (e + 1) → E e) : Fin e → E e :=
  fun i => v i.succ - v 0

def vectorDet {e : ℕ} (v : Fin e → E e) : ℝ :=
  Matrix.det (fun i j => v j i)

def standardVertices (e : ℕ) : Fin (e + 1) → E e :=
  Fin.cases 0 (fun i => EuclideanSpace.basisFun (Fin e) ℝ i)

def StdSimplexVolume : Prop :=
  ∀ e, volHull (simplexPoints (standardVertices e)) = 1 / (e.factorial : ℝ)

def SimplexVolumeDet : Prop :=
  ∀ e (v : Fin (e + 1) → E e), AffineIndependent ℝ v →
    volHull (simplexPoints v) = |vectorDet (edgeVectors v)| / (e.factorial : ℝ)

def LatticeDetLower : Prop :=
  ∀ e (L : FullLat e) (v : Fin e → E e),
    (∀ i, v i ∈ L.carrier) → LinearIndependent ℝ v → L.det ≤ |vectorDet v|

def SimplexVolumeLower : Prop :=
  ∀ e (L : FullLat e) (a : E e) (v : Fin (e + 1) → E e),
    (∀ i, v i - a ∈ L.carrier) → AffineIndependent ℝ v →
    L.det / (e.factorial : ℝ) ≤ volHull (simplexPoints v)

def IsExposed {e : ℕ} (S : Finset (E e)) (v : E e) : Prop :=
  v ∈ S ∧ ∃ f : E e →ₗ[ℝ] ℝ, ∀ w ∈ S, w ≠ v → f w < f v

def ExposedPoint : Prop :=
  ∀ e (S : Finset (E e)), S.Nonempty → ∃ v, IsExposed S v

def affineFlat {n : ℕ} (a : E n) (W : Submodule ℝ (E n)) : Set (E n) :=
  {x | x - a ∈ W}

def sectionVolume {n : ℕ} (C : Set (E n)) (a : E n)
    (W : Submodule ℝ (E n)) : ℝ :=
  (volume {w : W | a + (w : E n) ∈ C}).toReal

def PyramidVolume : Prop :=
  ∀ e, 1 ≤ e → ∀ (H : Submodule ℝ (E e)) (a v : E e) (B : Finset (E e)),
    Module.finrank ℝ H = e - 1 → B.Nonempty → spanDim B = e - 1 →
    (∀ b ∈ B, b ∈ affineFlat a H) → v ∉ affineFlat a H →
    volHull (insert v B) =
      sectionVolume (convexHull ℝ (B : Set (E e))) a H *
        Metric.infDist v (affineFlat a H) / (e : ℝ)

def latticeInSubspace {n : ℕ} (L : Submodule ℤ (E n))
    (W : Submodule ℝ (E n)) : Submodule ℤ W :=
  L.comap (W.subtype.restrictScalars ℤ)

def LatticeRational {n : ℕ} (L : Submodule ℤ (E n))
    (W : Submodule ℝ (E n)) : Prop :=
  Submodule.span ℝ ((L : Set (E n)) ∩ (W : Set (E n))) = W

def LayerSpacing : Prop :=
  ∀ e, 1 ≤ e → ∀ (L : FullLat e) (H : Submodule ℝ (E e)) (v : E e),
    Module.finrank ℝ H = e - 1 → LatticeRational L.carrier H →
    v ∈ L.carrier → v ∉ H →
    L.det / ZLattice.covolume (latticeInSubspace L.carrier H) ≤
      Metric.infDist v (H : Set (E e))

def VertexRemovalGain : Prop :=
  ∀ e, 1 ≤ e → ∀ (L : FullLat e) (a : E e) (S : Finset (E e)) (v : E e),
    InCoset L a S → IsExposed S v → spanDim (S.erase v) = e →
    volHull (S.erase v) + L.det / (e.factorial : ℝ) ≤ volHull S

def SimplexCount (e : ℕ) : Prop :=
  1 ≤ e → e ≤ 4 → ∀ (L : FullLat e) (a : E e) (S : Finset (E e)),
    InCoset L a S → spanDim S = e →
    (S.card : ℝ) ≤ (e.factorial : ℝ) * volHull S / L.det + (e : ℝ)

def CountDim0 : Prop :=
  ∀ n (S : Finset (E n)), S.Nonempty → spanDim S = 0 → S.card = 1

def CountDim1 : Prop :=
  ∀ (L : FullLat 1) (a : E 1) (S : Finset (E 1)),
    InCoset L a S → spanDim S = 1 → (S.card : ℝ) ≤ volHull S / L.det + 1

def PlanarCount : Prop :=
  ∀ (L : FullLat 2) (a : E 2) (S : Finset (E 2)),
    InCoset L a S → spanDim S = 2 → (S.card : ℝ) ≤ 6 * volHull S / L.det

def differenceBody {n : ℕ} (C : Set (E n)) : Set (E n) :=
  {z | ∃ x ∈ C, ∃ y ∈ C, z = x - y}

def CentrallySymmetric {n : ℕ} (C : Set (E n)) : Prop :=
  ∀ x, x ∈ C ↔ -x ∈ C

def SectionCount (e k : ℕ) : Prop :=
  ∀ n, n ≤ 4 → ∀ (W : Submodule ℝ (E n)) (chart : W ≃ₗᵢ[ℝ] E e)
    (L : FullLat e) (a : E n) (b : E e) (C : Set (E n)) (S : Finset W),
    IsCompact C → Convex ℝ C →
    (∀ x ∈ S, a + (x : E n) ∈ C) →
    InCoset L b (S.image chart) → spanDim (S.image chart) = e →
    (S.card : ℝ) ≤ (k : ℝ) * sectionVolume (differenceBody C) 0 W / L.det ∧
    (CentrallySymmetric C →
      sectionVolume (differenceBody C) 0 W = (2 : ℝ)^e * sectionVolume C 0 W ∧
      (S.card : ℝ) ≤ (k : ℝ) * (2 : ℝ)^e * sectionVolume C 0 W / L.det)

def SectionCount3 : Prop := SectionCount 3 81

def SectionCount4 : Prop := SectionCount 4 972

def integerLattice (n : ℕ) : Submodule ℤ (E n) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ))

namespace Coordinates

def coordinateLattice (e : ℕ) : FullLat e where
  carrier := integerLattice e
  discrete := inferInstanceAs (DiscreteTopology
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin e) ℝ).toBasis)))
  isZLattice := inferInstanceAs (IsZLattice ℝ
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin e) ℝ).toBasis)))

theorem coordinate_det (e : ℕ) : (coordinateLattice e).det = 1 := by
  change ZLattice.covolume
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin e) ℝ).toBasis)) = 1
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (EuclideanSpace.basisFun (Fin e) ℝ).toBasis volume)]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped
    (EuclideanSpace.basisFun (Fin e) ℝ).toBasis volume)]
  simp [(EuclideanSpace.basisFun (Fin e) ℝ).volume_parallelepiped, Measure.real]

end Coordinates

end Praxis.Algebra.Point
