import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Round

namespace Praxis.Algebra.Basis.ElementaryModel

abbrev ZMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℤ

def columnL1 {d : ℕ} (C : ZMatrix d) (j : Fin d) : ℕ :=
  ∑ i, (C i j).natAbs

def columnL1Product {d : ℕ} (C : ZMatrix d) : ℕ :=
  ∏ j, columnL1 C j

def Unimodular {d : ℕ} (U : ZMatrix d) : Prop :=
  U.det = 1 ∨ U.det = -1

def prefixGram {d : ℕ} (C : ZMatrix d) (k : ℕ) (h : k ≤ d) : ℤ :=
  Matrix.det (fun i j : Fin k => ∑ r, C r (i.castLE h) * C r (j.castLE h))

def D1 (C : ZMatrix 3) : ℤ := prefixGram C 1 (by decide)

def D2 (C : ZMatrix 3) : ℤ := prefixGram C 2 (by decide)

def potential (C : ZMatrix 3) : ℕ := (D1 C).natAbs * (D2 C).natAbs

def dotQ {d : ℕ} (x y : Fin d → ℚ) : ℚ := ∑ i, x i * y i

def columnQ {d : ℕ} (C : ZMatrix d) (j : Fin d) : Fin d → ℚ :=
  fun i => (C i j : ℚ)

def q1 (C : ZMatrix 3) : Fin 3 → ℚ := columnQ C 0

def t1 (C : ZMatrix 3) : ℚ := dotQ (q1 C) (q1 C)

def m21 (C : ZMatrix 3) : ℚ := dotQ (columnQ C 1) (q1 C) / t1 C

def q2 (C : ZMatrix 3) : Fin 3 → ℚ :=
  fun i => columnQ C 1 i - m21 C * q1 C i

def t2 (C : ZMatrix 3) : ℚ := dotQ (q2 C) (q2 C)

def m31 (C : ZMatrix 3) : ℚ := dotQ (columnQ C 2) (q1 C) / t1 C

def m32 (C : ZMatrix 3) : ℚ := dotQ (columnQ C 2) (q2 C) / t2 C

def q3 (C : ZMatrix 3) : Fin 3 → ℚ :=
  fun i => columnQ C 2 i - m31 C * q1 C i - m32 C * q2 C i

def t3 (C : ZMatrix 3) : ℚ := dotQ (q3 C) (q3 C)

def orthogonalMatrix (C : ZMatrix 3) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => ![q1 C i, q2 C i, q3 C i] j

def shear {d : ℕ} (i j : Fin d) (k : ℤ) : ZMatrix d :=
  fun r s => (if r = s then 1 else 0) - (if r = i ∧ s = j then k else 0)

def swapChange {d : ℕ} (i j : Fin d) : ZMatrix d :=
  fun r s => if r = (Equiv.swap i j) s then 1 else 0

def SizeBounds3 (C : ZMatrix 3) : Prop :=
  |m21 C| ≤ (1 / 2 : ℚ) ∧ |m31 C| ≤ (1 / 2 : ℚ) ∧ |m32 C| ≤ (1 / 2 : ℚ)

def firstReduce (C : ZMatrix 3) : ZMatrix 3 := C * shear 0 1 (round (m21 C))

def secondReduce (C : ZMatrix 3) : ZMatrix 3 :=
  firstReduce C * shear 1 2 (round (m32 (firstReduce C)))

def sizeReduceChange (C : ZMatrix 3) : ZMatrix 3 :=
  (shear 0 1 (round (m21 C)) * shear 1 2 (round (m32 (firstReduce C)))) *
    shear 0 2 (round (m31 (secondReduce C)))

structure Gram3Facts (C : ZMatrix 3) : Prop where
  positive : 0 < D1 C ∧ 0 < D2 C ∧ 0 < t1 C ∧ 0 < t2 C ∧ 0 < t3 C
  minors : D2 C =
    (C 0 0 * C 1 1 - C 1 0 * C 0 1) ^ 2 +
    (C 0 0 * C 2 1 - C 2 0 * C 0 1) ^ 2 +
    (C 1 0 * C 2 1 - C 2 0 * C 1 1) ^ 2
  orthogonal : dotQ (q1 C) (q2 C) = 0 ∧ dotQ (q1 C) (q3 C) = 0 ∧
    dotQ (q2 C) (q3 C) = 0
  prefix_values : (D1 C : ℚ) = t1 C ∧ (D2 C : ℚ) = t1 C * t2 C
  potential_cast : (potential C : ℚ) = t1 C * (t1 C * t2 C)
  determinant : (orthogonalMatrix C).det = (C.det : ℚ) ∧
    t1 C * t2 C * t3 C = (C.det : ℚ) ^ 2
  norms : dotQ (columnQ C 0) (columnQ C 0) = t1 C ∧
    dotQ (columnQ C 1) (columnQ C 1) = t2 C + m21 C ^ 2 * t1 C ∧
    dotQ (columnQ C 2) (columnQ C 2) =
      t3 C + m32 C ^ 2 * t2 C + m31 C ^ 2 * t1 C
  shear_det : ∀ (i j : Fin 3) (k : ℤ), i ≠ j → (shear i j k).det = 1
  shear21 : ∀ k : ℤ, let B := C * shear 0 1 k
    B.det = C.det ∧ D1 B = D1 C ∧ D2 B = D2 C ∧ potential B = potential C ∧
    q1 B = q1 C ∧ q2 B = q2 C ∧ q3 B = q3 C ∧
    m21 B = m21 C - k ∧ m31 B = m31 C ∧ m32 B = m32 C
  shear32 : ∀ k : ℤ, let B := C * shear 1 2 k
    B.det = C.det ∧ D1 B = D1 C ∧ D2 B = D2 C ∧ potential B = potential C ∧
    q1 B = q1 C ∧ q2 B = q2 C ∧ q3 B = q3 C ∧
    m21 B = m21 C ∧ m31 B = m31 C - k * m21 C ∧ m32 B = m32 C - k
  shear31 : ∀ k : ℤ, let B := C * shear 0 2 k
    B.det = C.det ∧ D1 B = D1 C ∧ D2 B = D2 C ∧ potential B = potential C ∧
    q1 B = q1 C ∧ q2 B = q2 C ∧ q3 B = q3 C ∧
    m21 B = m21 C ∧ m31 B = m31 C - k ∧ m32 B = m32 C
  swap12 : (swapChange (0 : Fin 3) 1).det = -1 ∧
    let B := C * swapChange 0 1
    B.det = -C.det ∧ D2 B = D2 C ∧
    (D1 B : ℚ) = t2 C + m21 C ^ 2 * t1 C
  swap23 : (swapChange (1 : Fin 3) 2).det = -1 ∧
    let B := C * swapChange 1 2
    B.det = -C.det ∧ D1 B = D1 C ∧
    (D2 B : ℚ) = t1 C * (t3 C + m32 C ^ 2 * t2 C)

def Gram3Identities : Prop :=
  ∀ C : ZMatrix 3, C.det ≠ 0 → Gram3Facts C

def SizeReduce3 : Prop :=
  ∀ C : ZMatrix 3, C.det ≠ 0 →
    Unimodular (sizeReduceChange C) ∧
    potential (C * sizeReduceChange C) = potential C ∧
    SizeBounds3 (C * sizeReduceChange C)

def ReducedPotential3 : Prop :=
  ∀ C : ZMatrix 3, C.det ≠ 0 → ∃ U : ZMatrix 3,
    Unimodular U ∧ SizeBounds3 (C * U) ∧
    (∀ V : ZMatrix 3, Unimodular V → potential (C * U) ≤ potential (C * V)) ∧
    3 * t1 (C * U) ≤ 4 * t2 (C * U) ∧
    3 * t2 (C * U) ≤ 4 * t3 (C * U)

def ColumnL1Core3 : Prop :=
  ∀ C : ZMatrix 3, C.det ≠ 0 → ∃ U : ZMatrix 3,
    Unimodular U ∧ columnL1Product (C * U) ≤ 8 * C.det.natAbs

end Praxis.Algebra.Basis.ElementaryModel
