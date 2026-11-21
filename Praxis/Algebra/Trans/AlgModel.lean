import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open scoped BigOperators

namespace Praxis.Algebra.Trans

section Algebra

variable {R : Type*} [CommRing R]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weightedGram {r : ℕ} (B : Matrix ι (Fin r) R) (sigma : ι → R) :
    Matrix (Fin r) (Fin r) R :=
  B.transpose * Matrix.diagonal (fun i => sigma i ^ 2) * B

def quadratic {r : ℕ} (A : Matrix (Fin r) (Fin r) R) (v : Fin r → R) : R :=
  dotProduct v (A.mulVec v)

def detRows2 (u v : Fin 2 → R) : R := Matrix.det ![u, v]

def detRows3 (u v w : Fin 3 → R) : R := Matrix.det ![u, v, w]

def WeightedAdj2 (B : Matrix ι (Fin 2) R) (sigma : ι → R) : Prop :=
  ∀ i, quadratic (Matrix.adjugate (weightedGram B sigma)) (B i) =
    ∑ l, sigma l ^ 2 * detRows2 (B i) (B l) ^ 2

def WeightedCross3 (B : Matrix ι (Fin 3) R) (sigma : ι → R) : Prop :=
  ∀ i j, quadratic (weightedGram B sigma) (crossProduct (B i) (B j)) =
    ∑ l, sigma l ^ 2 * detRows3 (B i) (B j) (B l) ^ 2

def WeightedPairs3 [LinearOrder ι] (B : Matrix ι (Fin 3) R) (sigma : ι → R) : Prop :=
  ∀ i, quadratic (Matrix.adjugate (weightedGram B sigma)) (B i) =
    ∑ l, ∑ j ∈ Finset.univ.filter (fun j => l < j),
      sigma l ^ 2 * sigma j ^ 2 * detRows3 (B i) (B l) (B j) ^ 2

def elementarySymmetric (w : ι → R) (k : ℕ) : R :=
  ((Finset.univ : Finset ι).val.map w).esymm k

def rowMinor [LinearOrder ι] {r : ℕ} (B : Matrix ι (Fin r) R) (I : Finset ι) : R :=
  if h : I.card = r then Matrix.det (B.submatrix (I.orderEmbOfFin h) id) else 0

def CauchyBinet3 [LinearOrder ι] {r : ℕ}
    (B : Matrix ι (Fin r) R) (sigma : ι → R) : Prop :=
  r ≤ 3 → Matrix.det (weightedGram B sigma) =
    ∑ I ∈ Finset.univ.powersetCard r, rowMinor B I ^ 2 * ∏ i ∈ I, sigma i ^ 2

end Algebra

def ESymBounds {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → R) (S : R) : Prop :=
  (∀ i, 0 ≤ w i) → (∑ i, w i) = S →
    elementarySymmetric w 2 ≤ S ^ 2 / 2 ∧ elementarySymmetric w 3 ≤ S ^ 3 / 6

end Praxis.Algebra.Trans
