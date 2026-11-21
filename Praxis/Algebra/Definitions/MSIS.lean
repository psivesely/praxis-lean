import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace Praxis.Algebra

structure MSISRing (p d : ℕ) where

  Phi : Polynomial (ZMod p)
  monic : Phi.Monic
  natDegree_eq : Phi.natDegree = d

namespace MSISRing

variable {p d : ℕ}

abbrev Ring (R : MSISRing p d) : Type := AdjoinRoot R.Phi

noncomputable def coords (R : MSISRing p d) : R.Ring ≃ (Fin R.Phi.natDegree → ZMod p) :=
  (AdjoinRoot.powerBasis' R.monic).basis.equivFun.toEquiv

instance [NeZero p] (R : MSISRing p d) : Finite R.Ring :=
  Finite.of_equiv _ R.coords.symm

noncomputable instance [NeZero p] (R : MSISRing p d) : Fintype R.Ring :=
  Fintype.ofFinite _

noncomputable def embed (R : MSISRing p d) (w : Fin d → ℤ) : R.Ring :=
  AdjoinRoot.mk R.Phi
    (∑ t : Fin d, Polynomial.C ((w t : ℤ) : ZMod p) * Polynomial.X ^ (t : ℕ))

end MSISRing

abbrev RingMatrix {p d : ℕ} (R : MSISRing p d) (rows ellCols : ℕ) : Type :=
  Matrix (Fin rows) (Fin ellCols) R.Ring

abbrev CoeffVec (d ellCols : ℕ) : Type := Fin ellCols → Fin d → ℤ

def coeffNorm {d ellCols : ℕ} (w : CoeffVec d ellCols) : ℕ :=
  Finset.univ.sup fun c => Finset.univ.sup fun t => (w c t).natAbs

def NonzeroModP (p : ℕ) {d ellCols : ℕ} (w : CoeffVec d ellCols) : Prop :=
  ∃ c t, ((w c t : ℤ) : ZMod p) ≠ 0

noncomputable def moduleMul {p d rows ellCols : ℕ} (R : MSISRing p d)
    (A : RingMatrix R rows ellCols) (w : CoeffVec d ellCols) : Fin rows → R.Ring :=
  fun r => ∑ c, A r c * R.embed (w c)

def IsMSISSolution {p d rows ellCols : ℕ} (R : MSISRing p d) (B : ℕ)
    (A : RingMatrix R rows ellCols) (w : CoeffVec d ellCols) : Prop :=
  NonzeroModP p w ∧ coeffNorm w ≤ B ∧ moduleMul R A w = 0

def MSISWins {p d rows ellCols : ℕ} (R : MSISRing p d) (B : ℕ)
    (A : RingMatrix R rows ellCols) (out : Option (CoeffVec d ellCols)) : Prop :=
  ∃ w, out = some w ∧ IsMSISSolution R B A w

structure MSISAlgorithm {p d : ℕ} (R : MSISRing p d) (rows ellCols : ℕ) where

  Coins : Type
  [coinsFintype : Fintype Coins]
  [coinsNonempty : Nonempty Coins]

  run : RingMatrix R rows ellCols → Coins → Option (CoeffVec d ellCols)

attribute [instance] MSISAlgorithm.coinsFintype MSISAlgorithm.coinsNonempty

noncomputable def msisSuccess {p d rows ellCols : ℕ} [NeZero p] (R : MSISRing p d) (B : ℕ)
    (red : MSISAlgorithm R rows ellCols) : ℝ := by
  classical
  exact ((Finset.univ.filter fun x : RingMatrix R rows ellCols × red.Coins =>
      MSISWins R B x.1 (red.run x.1 x.2)).card : ℝ) /
    (Fintype.card (RingMatrix R rows ellCols × red.Coins) : ℝ)

section Facts

variable {p d rows ellCols : ℕ}

theorem coeffNorm_le_iff (w : CoeffVec d ellCols) (B : ℕ) :
    coeffNorm w ≤ B ↔ ∀ c t, (w c t).natAbs ≤ B := by
  simp [coeffNorm, Finset.sup_le_iff]

end Facts

end Praxis.Algebra
