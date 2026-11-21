import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Defs

namespace Praxis.Algebra

abbrev Vec (F : Type*) (N : ℕ) := Fin (N + 1) → F

abbrev Mat (F : Type*) (N : ℕ) := Matrix (Fin (N + 1)) (Fin (N + 1)) F

def dot {F : Type*} [CommSemiring F] {N : ℕ}
    (u x : Vec F N) : F := ∑ i, u i * x i

structure Gate (F : Type*) (N : ℕ) where
  products : ℕ
  left : Fin products → Vec F N
  right : Fin products → Vec F N
  linear : Vec F N

abbrev Relation (F : Type*) (N n : ℕ) := Fin n → Gate F N

def Sat {F : Type*} [Field F] {N n : ℕ}
    (R : Relation F N n) (x : Vec F N) : Prop :=
  x 0 = 1 ∧ (∀ i : Fin N, x i.succ = 0 ∨ x i.succ = 1) ∧
  ∀ g, (∑ j, dot ((R g).left j) x * dot ((R g).right j) x) =
    x 0 * dot (R g).linear x

def MomentGate {F : Type*} [Field F] {N : ℕ}
    (g : Gate F N) (M : Mat F N) : F :=
  (∑ j, ∑ i, ∑ k, g.left j i * M i k * g.right j k) -
    ∑ k, M 0 k * g.linear k

end Praxis.Algebra
