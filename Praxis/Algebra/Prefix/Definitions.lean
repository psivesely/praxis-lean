import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.AdditiveChain
import Praxis.Algebra.DifferenceLattice.Saturation

set_option autoImplicit false

namespace Praxis.Algebra.Prefix.Definitions

open Finset Module

open Praxis.Algebra.Inverse.Definitions

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IntegerMassHeight {d : ℕ} (L : IntLat ι d) (G : ι → ℕ) (g : ℕ) : Prop :=
  1 ≤ d → d ≤ 3 → 2 ≤ g → g < 2^254 → (∀ i, g ≤ G i) →
    L.mZ G ≤ (1 / (g : ℝ)^d) * (1 + 2 / (g : ℝ))^254 *
      (1 / (L.H : ℝ) + 1 / (g : ℝ))

def IntegerMassPivot {d : ℕ} (L : IntLat ι d) (G : ι → ℕ) (g : ℕ) : Prop :=
  1 ≤ d → d ≤ 3 → 0 < g → (∀ i, g ≤ G i) → L.mZ G ≤ 1 / (g : ℝ)^d

structure PivotFirstPrefix (d n k : ℕ) where
  rank_lower : 1 ≤ d
  rank_upper : d ≤ 3
  rank_le_prefix : d ≤ k
  prefix_le_ambient : k ≤ n
  original : IntLat (Fin n) d
  order : Equiv.Perm (Fin n)
  maximal_pivot :
    (original.matrix.submatrix
      (fun a : Fin d => order ⟨a.val, lt_of_lt_of_le a.isLt (rank_le_prefix.trans prefix_le_ambient)⟩)
      id).det.natAbs = original.H
  pivot_nonzero : 0 < original.H
  rows : AddSubgroup (Fin d → ℤ)
  rows_eq : rows = AddSubgroup.closure (Set.range
    (fun i : Fin k => original.matrix (order ⟨i.val, lt_of_lt_of_le i.isLt prefix_le_ambient⟩)))
  primitive : IntLat (Fin k) d
  primitive_eq : primitive.carrier = Algebra.Lattice.saturation
    ((original.matrix.submatrix
      (fun i : Fin k => order ⟨i.val, lt_of_lt_of_le i.isLt prefix_le_ambient⟩) id).mulVecLin.range)

namespace PivotFirstPrefix

variable {d n k : ℕ}

def coord (P : PivotFirstPrefix d n k) (i : Fin k) : Fin n :=
  P.order ⟨i.val, lt_of_lt_of_le i.isLt P.prefix_le_ambient⟩

noncomputable def matrix (P : PivotFirstPrefix d n k) : Matrix (Fin k) (Fin d) ℤ :=
  P.original.matrix.submatrix P.coord id

noncomputable def divisor (P : PivotFirstPrefix d n k) : ℕ :=
  univ.gcd (fun r : Fin d → Fin k => (P.matrix.submatrix r id).det.natAbs)

noncomputable def primitiveHeight (P : PivotFirstPrefix d n k) : ℕ := P.primitive.H

noncomputable def originalHeight (P : PivotFirstPrefix d n k) : ℕ := P.original.H

def grids (P : PivotFirstPrefix d n k) (G : Fin n → ℕ) : Fin k → ℕ := G ∘ P.coord

end PivotFirstPrefix

structure PivotFirstStep (d n k : ℕ) where
  old : PivotFirstPrefix d n k
  next : PivotFirstPrefix d n (k+1)
  same_original : next.original = old.original
  same_order : next.order = old.order
  grids : Fin n → ℕ
  grids_pos : ∀ i, 0 < grids i
  residueOrder : ℕ
  quotient_order : residueOrder = addOrderOf (QuotientAddGroup.mk' old.rows
    (old.original.matrix (old.order ⟨k, by have := next.prefix_le_ambient; omega⟩)))

namespace PivotFirstStep

variable {d n k : ℕ}

def newCoord (P : PivotFirstStep d n k) : Fin n :=
  P.old.order ⟨k, by have := P.next.prefix_le_ambient; omega⟩

def IsOrdinaryFibre (P : PivotFirstStep d n k)
    (F : Finset (Grid (P.next.grids P.grids))) : Prop :=
  ∀ r ∈ F, ∀ s ∈ F,
    imageZ (P.next.grids P.grids) P.next.matrix r =
      imageZ (P.next.grids P.grids) P.next.matrix s

end PivotFirstStep

def PrefixHeight {d n k : ℕ} (P : PivotFirstPrefix d n k) : Prop :=
  P.divisor * P.primitiveHeight = P.originalHeight

def PrefixOrder {d n k : ℕ} (P : PivotFirstStep d n k) : Prop :=
  P.old.divisor = P.residueOrder * P.next.divisor

def JumpFixesCoordinate {d n k : ℕ} (P : PivotFirstStep d n k) : Prop :=
  ∀ F : Finset (Grid (P.next.grids P.grids)), F.Nonempty → P.IsOrdinaryFibre F →
    P.grids P.newCoord ≤ P.residueOrder →
      ∃ a : Fin (P.next.grids P.grids ⟨k, Nat.lt_succ_self k⟩),
        ∀ r ∈ F, r ⟨k, Nat.lt_succ_self k⟩ = a

def PrefixMassMono {d n k : ℕ} (P : PivotFirstStep d n k) : Prop :=
  P.next.primitive.mZ (P.next.grids P.grids) ≤
    P.old.primitive.mZ (P.old.grids P.grids)

end Praxis.Algebra.Prefix.Definitions
