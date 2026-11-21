import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Trans.AlgModel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

open Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

namespace Praxis.Algebra.Trans

def ChartCase (r q : ℕ) : Prop := (r = 3 ∧ q = 2) ∨ (r = 2 ∧ q = 1) ∨ (r = 3 ∧ q = 1)

structure ChartBasis (r q : ℕ) where
  K : Matrix (Fin (r+1)) (Fin q) ℤ
  rows : Fin q ⊕ Fin (r-q) ≃ Fin r

namespace ChartBasis

variable {r q : ℕ} (B : ChartBasis r q)

def pivot : Fin q → Fin r := fun i => B.rows (Sum.inl i)

def free : Fin (r-q) → Fin r := fun i => B.rows (Sum.inr i)

def U : Matrix (Fin r) (Fin q) ℤ := oldBlock B.K

def v : Fin q → ℤ := B.K (Fin.last r)

def a : ℤ := (B.U.submatrix B.pivot id).det

def HasPivot : Prop := B.a ≠ 0

def pivotReal : Matrix (Fin q) (Fin q) ℝ := (realMatrix B.U).submatrix B.pivot id

def freeReal : Matrix (Fin (r-q)) (Fin q) ℝ := (realMatrix B.U).submatrix B.free id

def A : Matrix (Fin r) (Fin (r-q)) ℝ := fun i j =>
  match B.rows.symm i with
  | Sum.inl k => -((B.pivotReal.transpose)⁻¹ * B.freeReal.transpose) k j
  | Sum.inr k => if k = j then 1 else 0

def b : Fin r → ℝ := fun i =>
  match B.rows.symm i with
  | Sum.inl k => -((B.pivotReal.transpose)⁻¹).mulVec (fun j => (B.v j : ℝ)) k
  | Sum.inr _ => 0

def c (t : Fin q → ℝ) : Fin r → ℝ := fun i =>
  match B.rows.symm i with
  | Sum.inl k => ((B.pivotReal.transpose)⁻¹).mulVec t k
  | Sum.inr _ => 0

def projectZ (w : Fin (r+1) → ℤ) : Fin (r-q+1) → ℤ :=
  Fin.snoc (fun j => w (B.free j).castSucc) (w (Fin.last r))

def project (w : Fin (r+1) → ℝ) : E (r-q+1) :=
  WithLp.toLp 2 (Fin.snoc (fun j => w (B.free j).castSucc) (w (Fin.last r)))

def projectLinear : (Fin (r+1) → ℤ) →ₗ[ℤ] (Fin (r-q+1) → ℤ) where
  toFun := B.projectZ
  map_add' := by intro x y; ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [projectZ]
  map_smul' := by intro s x; ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [projectZ]

def Gamma : Submodule ℤ (Fin (r-q+1) → ℤ) :=
  (B.K.transpose.mulVecLin.ker).map B.projectLinear

def castCoordinates (e : ℕ) : (Fin e → ℤ) →ₗ[ℤ] E e where
  toFun := fun z => WithLp.toLp 2 (fun i => (z i : ℝ))
  map_add' := by intro x y; ext i; simp
  map_smul' := by intro s x; ext i; simp

def realGamma : Submodule ℤ (E (r-q+1)) := B.Gamma.map (castCoordinates _)

def normalGram (Sigma : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  (realMatrix B.U).transpose * Sigma * realMatrix B.U

def C (Sigma : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin (r-q)) (Fin (r-q)) ℝ :=
  B.A.transpose * Sigma⁻¹ * B.A

end ChartBasis

structure ChartGeometry (r q : ℕ) extends ChartBasis r q where
  Sigma : Matrix (Fin r) (Fin r) ℝ
  mu : Fin r → ℝ
  target : Fin q → ℝ
  R : ℝ
  lower : ℝ
  upper : ℝ

namespace ChartGeometry

variable {r q : ℕ} (T : ChartGeometry r q)

def delta (x : ℝ) : Fin r → ℝ := fun i => T.b i * x + T.c T.target i - T.mu i

def ell (x : ℝ) : Fin (r-q) → ℝ :=
  (T.C T.Sigma)⁻¹ |>.mulVec (T.A.transpose.mulVec (T.Sigma⁻¹.mulVec (T.delta x)))

def rho (x : ℝ) : Fin r → ℝ := T.delta x - T.A.mulVec (T.ell x)

def reconstruct (w : E (r-q+1)) : Fin r → ℝ :=
  T.A.mulVec (fun j => w j.castSucc) +
    (fun i => T.b i * w (Fin.last (r-q)) + T.c T.target i)

def envelope : Set (E (r-q+1)) := {w |
  w (Fin.last (r-q)) ∈ Set.Icc T.lower T.upper ∧
  quadratic (T.C T.Sigma)
    ((fun j => w j.castSucc) + T.ell (w (Fin.last (r-q)))) ≤ T.R^2}

def shear (w : E (r-q+1)) : E (r-q+1) :=
  WithLp.toLp 2 (Fin.snoc ((fun j => w j.castSucc) + T.ell (w (Fin.last (r-q))))
    (w (Fin.last (r-q))))

def straightCylinder : Set (E (r-q+1)) := {w |
  w (Fin.last (r-q)) ∈ Set.Icc T.lower T.upper ∧
  quadratic (T.C T.Sigma) (fun j => w j.castSucc) ≤ T.R^2}

def actualSection : Set (E (r-q+1)) := {w |
  w (Fin.last (r-q)) ∈ Set.Icc T.lower T.upper ∧
  quadratic T.Sigma⁻¹ (T.reconstruct w - T.mu) ≤ T.R^2}

def midpoint : ℝ := (T.lower + T.upper)/2

def envelopeCenter : E (r-q+1) :=
  WithLp.toLp 2 (Fin.snoc (-T.ell T.midpoint) T.midpoint)

def intervalLength : ℝ := T.upper - T.lower

def ballVolume (d : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.closedBall (0 : E d) 1)).toReal

def bodyVolume {e : ℕ} (D : Set (E e)) : ℝ := (MeasureTheory.volume D).toReal

def cylinderVolume : ℝ := T.intervalLength * ballVolume (r-q) * T.R^(r-q) /
  Real.sqrt (T.C T.Sigma).det

def shearMatrix : Matrix (Fin (r-q+1)) (Fin (r-q+1)) ℝ := fun i j =>
  Fin.lastCases (if j = Fin.last (r-q) then 1 else 0)
    (fun k => if j = Fin.last (r-q) then T.ell 1 k - T.ell 0 k
      else if j = k.castSucc then 1 else 0) i

end ChartGeometry

structure ChartData (r q : ℕ) extends ChartGeometry r q where
  S : Finset (Fin (r+1) → ℤ)
  dimensionCase : ChartCase r q
  primitive : PrimitiveMatrix K
  pivot_ne_zero : toChartBasis.HasPivot
  positive : Sigma.PosDef
  radius_pos : 0 < R
  interval_order : lower ≤ upper
  nonempty : S.Nonempty
  affine_span : ∀ w : Fin (r+1) → ℝ,
    w ∈ affineSpan ℝ (Set.image (fun z : Fin (r+1) → ℤ => fun i => (z i : ℝ))
      (S : Set (Fin (r+1) → ℤ))) ↔ (realMatrix K).transpose.mulVec w = target
  contained : ∀ w ∈ S,
    (w (Fin.last r) : ℝ) ∈ Set.Icc lower upper ∧
    quadratic Sigma⁻¹ ((fun i => (w i.castSucc : ℝ)) - mu) ≤ R^2

namespace ChartData

variable {r q : ℕ} (T : ChartData r q)

def chartPoints : Finset (E (r-q+1)) :=
  T.S.image (fun z => T.project (fun i => (z i : ℝ)))

end ChartData

def ProjectedKernelIndex : Prop :=
  ∀ r q (B : ChartBasis r q), ChartCase r q → PrimitiveMatrix B.K → B.HasPivot →
    Function.Surjective B.K.transpose.mulVec ∧
    B.Gamma.toAddSubgroup.index = B.a.natAbs ∧
    Submodule.span ℝ (B.realGamma : Set (E (r-q+1))) = ⊤ ∧
    (∃ L : FullLat (r-q+1), L.carrier = B.realGamma ∧
      L.det = (B.Gamma.toAddSubgroup.index : ℝ) ∧ L.det = |(B.a : ℝ)|) ∧
    ∀ (t : Fin q → ℝ) (anchor : Fin (r+1) → ℤ),
      (realMatrix B.K).transpose.mulVec (fun i => (anchor i : ℝ)) = t →
      Set.BijOn B.projectZ
        {w | (realMatrix B.K).transpose.mulVec (fun i => (w i : ℝ)) = t}
        {z | z - B.projectZ anchor ∈ B.Gamma}

def ShearedCylinderEnvelope : Prop :=
  ∀ r q (T : ChartGeometry r q), ChartCase r q → T.HasPivot → T.Sigma.PosDef →
    0 < T.R → T.lower ≤ T.upper →
    (T.C T.Sigma).PosDef ∧
    (∀ (z : Fin (r-q) → ℝ) (x : ℝ),
      quadratic T.Sigma⁻¹ (T.A.mulVec z + T.delta x) =
        quadratic (T.C T.Sigma) (z + T.ell x) + quadratic T.Sigma⁻¹ (T.rho x)) ∧
    T.actualSection ⊆ T.envelope ∧
    Set.BijOn T.shear T.envelope T.straightCylinder ∧ T.shearMatrix.det = 1 ∧
    IsCompact T.envelope ∧ Convex ℝ T.envelope ∧
    (∀ w, w ∈ T.envelope ↔ 2 • T.envelopeCenter - w ∈ T.envelope) ∧
    ChartGeometry.bodyVolume T.envelope = T.cylinderVolume ∧
    ChartGeometry.bodyVolume (differenceBody T.envelope) =
      (2 : ℝ)^(r-q+1) * ChartGeometry.bodyVolume T.envelope

def ComplementaryGram : Prop :=
  ∀ r q (B : ChartBasis r q) (Sigma : Matrix (Fin r) (Fin r) ℝ),
    ChartCase r q → B.HasPivot → Sigma.PosDef →
    (B.a : ℝ)^2 * Sigma.det * (B.C Sigma).det = (B.normalGram Sigma).det

def ChartCountEnvelope (r q : ℕ) : Prop :=
  PlanarCount → SectionCount3 → ∀ T : ChartData r q,
    (T.S.card : ℝ) ≤ (if r-q+1 = 2 then 6 else 648) *
      ChartGeometry.bodyVolume T.envelope / |(T.a : ℝ)|

def ChartCount (r q : ℕ) : Prop :=
  PlanarCount → SectionCount3 → ∀ T : ChartData r q,
    (T.S.card : ℝ) ≤ (if r-q+1 = 2 then 6 else 648) * T.intervalLength *
      ChartGeometry.ballVolume (r-q) * T.R^(r-q) * Real.sqrt T.Sigma.det /
      Real.sqrt (T.normalGram T.Sigma).det

namespace Chart

def Transition32 (P : VITParameters) : Prop :=
  ChartCount 3 2 → NormalPullback →
  (∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedCross3 B s) →
  (∀ n (w : Fin n → ℝ) S, ESymBounds w S) → Algebra.Trans.Transition32 P

def Transition21 (P : VITParameters) : Prop :=
  ChartCount 2 1 → NormalPullback →
  (∀ n (B : Matrix (Fin n) (Fin 2) ℝ) (s : Fin n → ℝ), WeightedAdj2 B s) →
  (∀ n (w : Fin n → ℝ) S, ESymBounds w S) → Algebra.Trans.Transition21 P

def Transition31 (P : VITParameters) : Prop :=
  ChartCount 3 1 → NormalPullback →
  (∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedPairs3 B s) →
  (∀ n (w : Fin n → ℝ) S, ESymBounds w S) → Algebra.Trans.Transition31 P

theorem transition32_compat (P : VITParameters) (h : Transition32 P)
    (hc : ChartCount 3 2) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedCross3 B s)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S) : Algebra.Trans.Transition32 P :=
  h hc hn hw he

theorem transition21_compat (P : VITParameters) (h : Transition21 P)
    (hc : ChartCount 2 1) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 2) ℝ) (s : Fin n → ℝ), WeightedAdj2 B s)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S) : Algebra.Trans.Transition21 P :=
  h hc hn hw he

theorem transition31_compat (P : VITParameters) (h : Transition31 P)
    (hc : ChartCount 3 1) (hn : NormalPullback)
    (hw : ∀ n (B : Matrix (Fin n) (Fin 3) ℝ) (s : Fin n → ℝ), WeightedPairs3 B s)
    (he : ∀ n (w : Fin n → ℝ) S, ESymBounds w S) : Algebra.Trans.Transition31 P :=
  h hc hn hw he

theorem transition32_of_base (P : VITParameters) (h : Algebra.Trans.Transition32 P) :
    Transition32 P := fun _ _ _ _ => h

theorem transition21_of_base (P : VITParameters) (h : Algebra.Trans.Transition21 P) :
    Transition21 P := fun _ _ _ _ => h

theorem transition31_of_base (P : VITParameters) (h : Algebra.Trans.Transition31 P) :
    Transition31 P := fun _ _ _ _ => h

end Chart

end Praxis.Algebra.Trans
