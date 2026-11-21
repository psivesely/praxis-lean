import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.SmallMinorSaturation
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.Conversion.Conversion
import Praxis.Algebra.Conversion.ConversionStatement
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.InverseBranches.NormalBranches
import Praxis.Algebra.TrimAnalysis.CovarianceTrim

set_option autoImplicit false

noncomputable section

namespace Praxis.Algebra.Mod.Definitions

open Finset Module

open Praxis.Algebra.Inverse.Definitions

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

def extend {A : Type*} (v : ι → A) (a : A) : Option ι → A :=
  fun i => i.elim a v

def stepMatrix {d : ℕ} (B : Matrix ι (Fin d) ℤ) :
    Matrix (Option ι) (Option (Fin d)) ℤ :=
  fun i j => match i, j with
    | none, none => 1
    | some i, some j => B i j
    | _, _ => 0

def stepImage {d : ℕ} (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (r : Grid (extend G Gx)) : Option (Fin d) → ℤ :=
  (stepMatrix B).transpose *ᵥ (fun i => ((r i : ℕ) : ℤ))

def pullMod {d p : ℕ} (B : Matrix ι (Fin d) ℤ)
    (c : Option (Fin d) → ZMod p) : Option ι → ZMod p :=
  (stepMatrix B).map (Int.castRingHom (ZMod p)) *ᵥ c

def density {A : Type*} [Fintype A] (F : Finset A) : ℝ :=
  (F.card : ℝ) / Fintype.card A

def imageDifferences {A : Type*} [Fintype A] [DecidableEq A] {d : ℕ}
    (X : A → Option (Fin d) → ℤ) (F : Finset A) :
    Matrix (Option (Fin d)) (F × F) ℤ :=
  fun i s => X s.1.val i - X s.2.val i

def imageCenter {d : ℕ} (G : ι → ℕ) (B : Matrix ι (Fin d) ℤ) : Fin d → ℝ :=
  fun j => ∑ i, (B i j : ℝ) * (((G i : ℝ) - 1) / 2)

def Trimmed {d : ℕ} (P : VITData) (G : ι → ℕ) (Gx : ℕ)
    (B : Matrix ι (Fin d) ℤ) (F : Finset (Grid (extend G Gx))) : Prop :=
  ∀ r ∈ F, Analysis.mahalanobisSq
    (Analysis.gridCovariance G (B.map (Int.castRingHom ℝ)))
    (imageCenter G B) (fun j => (stepImage G Gx B r (some j) : ℝ)) ≤ P.R^2

def wrapFactor (P : VITData) (d : ℕ) : ℝ :=
  if d = 1 then P.D else if d = 2 then P.E else if d = 3 then P.F else 0

def heightBound (P : VITData) (d : ℕ) : ℝ :=
  if d = 1 then P.H1 else if d = 2 then P.H2 else if d = 3 then P.H3 else 0

def basisConstant (d : ℕ) : ℝ :=
  if d = 1 then 1 else if d = 2 then 2 else if d = 3 then 9 else 0

def minorBound (P : VITData) (d : ℕ) (T : ℝ) : ℝ :=
  (Nat.factorial d : ℝ) * basisConstant d * heightBound P d * T^d

def congruenceKernel {d : ℕ} (p : ℕ) (c : Option (Fin d) → ZMod p) :
    AddSubgroup (Option (Fin d) → ℤ) where
  carrier := {x | ∑ i, c i * (x i : ZMod p) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ i, c i * (x i : ZMod p)) = 0 at hx
    change (∑ i, c i * (y i : ZMod p)) = 0 at hy
    change (∑ i, c i * ((x+y) i : ZMod p)) = 0
    simp only [Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    change (∑ i, c i * (x i : ZMod p)) = 0 at hx
    change (∑ i, c i * ((-x) i : ZMod p)) = 0
    simp only [Pi.neg_apply, Int.cast_neg, mul_neg, sum_neg_distrib, hx, neg_zero]

def FullImageExclusion (d : ℕ) (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι d) (c : Option (Fin d) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) : Prop :=
  1 ≤ d → d ≤ 3 → GridBudget P.toVITData (extend G Gx) →
    Regular P.toVITData G L → c ≠ 0 → F.Nonempty →
    (∀ r ∈ F, ∑ i, c i * (stepImage G Gx L.matrix r i : ZMod P.p) = t) →
    Trimmed P.toVITData G Gx L.matrix F →
    Analysis.rationalRank (imageDifferences (stepImage G Gx L.matrix) F) = d+1 →
    Nat.card ((Option (Fin d) → ℤ) ⧸ congruenceKernel P.p c) = P.p ∧
    (∃ y : Option (Fin d) → ℤ, ∀ r ∈ F,
      stepImage G Gx L.matrix r - y ∈ congruenceKernel P.p c) ∧
    density F ≤ wrapFactor P.toVITData d * P.toVITData.C d / (P.p : ℝ) ∧
    wrapFactor P.toVITData d * P.toVITData.C d / (P.p : ℝ) < P.toVITData.mu

def SaturationApplication (d : ℕ) (P : VITParameters) (n : Fin d → ℕ)
    (T : ℝ) (D : Matrix (Option (Fin d)) κ ℤ) : Prop :=
  1 ≤ d → d ≤ 3 → (∀ j, 1 ≤ n j) →
    (∏ j, (n j : ℝ)) ≤ basisConstant d * heightBound P.toVITData d →
    1 ≤ T → T^2 ≤ P.toVITData.T2 →
    (∀ j k, |(D (some j) k : ℝ)| ≤ T * n j) →
    (∀ k, |(D none k : ℝ)| ≤ T) →
    ∀ e : ℕ, e ≤ d → ∀ (I : Fin e → Option (Fin d)) (J : Fin e → κ),
      (|(D.submatrix I J).det| : ℝ) ≤ minorBound P.toVITData d T ∧
      |(D.submatrix I J).det| < (P.p : ℤ)

def ModPullback {d p : ℕ} (L : IntLat ι d)
    (E : Submodule ℤ (Option (Fin d) → ℤ))
    (c : Option (Fin d) → ZMod p) : Prop :=
  p.Prime → Saturated E → Analysis.KillsSubmodule p c E →
    ∃ q : ℕ, ∃ N : IntLat (Option ι) q,
      N.carrier = Algebra.Lattice.saturation
        ((Algebra.VectorInverse.normalLattice E).map (stepMatrix L.matrix).mulVecLin) ∧
      N.carrier = Algebra.VectorInverse.normalLattice
        (E.comap (stepMatrix L.matrix).transpose.mulVecLin) ∧
      q + Module.finrank ℤ E = d+1 ∧
      pullMod L.matrix c ∈ redSpan p N

def RegularWitness (P : VITData) (G : ι → ℕ) (z : ι → ZMod P.p)
    (d : ℕ) (L : IntLat ι d) : Prop :=
  1 ≤ d ∧ d ≤ 3 ∧ z ∈ redSpan P.p L ∧ Regular P G L ∧
    mass G (scalar G z) - 3*P.eps ≤ L.mZ G

def ModStep (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (z : ι → ZMod P.p) (a : ZMod P.p) : Prop :=
  GridBudget P.toVITData (extend G Gx) → z ≠ 0 →
    P.theta0 < mass (extend G Gx) (scalar (extend G Gx) (extend z a)) →
    ∀ d : ℕ, ∀ L : IntLat ι d, RegularWitness P.toVITData G z d L →
      ∃ q : ℕ, ∃ N : IntLat (Option ι) q,
        RegularWitness P.toVITData (extend G Gx) (extend z a) q N

def ModularRegularization (P : VITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) : Prop :=
  GridBudget P.toVITData G → z ≠ 0 → P.theta0 < mass G (scalar G z) →
    ∃ d : ℕ, ∃ L : IntLat ι d, RegularWitness P.toVITData G z d L

def FinalFromModular (P : CertifiedVITParameters) (G : ι → ℕ)
    (z : ι → ZMod P.p) : Prop :=
  ModularRegularization P.toVITParameters G z →
    HeavyStack.ConversionClaim 1 → HeavyStack.ConversionClaim 2 →
    HeavyStack.ConversionClaim 3 → VectorInverseStatement P G z

end Praxis.Algebra.Mod.Definitions
