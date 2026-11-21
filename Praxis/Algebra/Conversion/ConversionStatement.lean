import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

namespace HeavyStack

def ShortMultiple (p n d : ℕ) (M : ℕ) (z : Fin n → ZMod p) : Prop :=
  ∃ (w : Fin n → ℤ) (a : ZMod p),
    w ≠ 0 ∧ a ≠ 0 ∧ (∀ i, (w i : ZMod p) = a * z i) ∧
    ∀ i, |(w i : ℝ)| ^ d ≤ (Nat.factorial d : ℝ) * M * (p : ℝ) ^ (d - 1)

def ConversionClaim (d : ℕ) : Prop :=
  ∀ (p n : ℕ), p.Prime → ∀ (B : Matrix (Fin n) (Fin d) ℤ)
    (r : Fin d → Fin n) (M : ℕ),
    (B.submatrix r id).det.natAbs = M → 0 < M → M < p →
    (∀ s : Fin d → Fin n, (B.submatrix s id).det.natAbs ≤ M) →
    ∀ z : Fin n → ZMod p, z ≠ 0 →
      (∃ c : Fin d → ZMod p, ∀ i, z i = ∑ j, (B i j : ZMod p) * c j) →
      ShortMultiple p n d M z

end HeavyStack
