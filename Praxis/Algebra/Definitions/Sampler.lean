import Praxis.Algebra.Definitions.Stack
import Mathlib.Probability.Distributions.Uniform
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Algebra

open Finset

section Law

variable {N : ℕ}

abbrev GridSample (g : ℕ) (G : Fin N → ℕ) :=
  Fin g × ((i : Fin N) → Fin (G i))

def centerA (G : Fin N → ℕ) : ℤ :=
  (((∑ i, (G i + 1)) + 1) / 2 : ℕ)

def centeredZ {g : ℕ} (G : Fin N → ℕ) (w : GridSample g G) : Vec ℤ N :=
  Fin.cases (motive := fun _ => ℤ)
    (centerA G + (2 + (w.1.val : ℤ)) -
      (∑ i, (2 + ((w.2 i).val : ℤ))) / 2)
    (fun i => 2 + ((w.2 i).val : ℤ))

def centeredF {p g : ℕ} {G : Fin N → ℕ} (w : GridSample g G) : Vec (ZMod p) N :=
  fun i => (centeredZ G w i : ZMod p)

end Law

section Atoms

noncomputable def atom {X Y : Type*} [Fintype X]
    (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card X

noncomputable def maxAtom {X Y : Type*} [Fintype X] (f : X → Y) : ℝ :=
  ⨆ y, atom f y

end Atoms

section Masses

variable {p N : ℕ}

noncomputable def stackMass {d rows : ℕ} (g : ℕ) (G : Fin N → ℕ)
    (W : Stack (ZMod p) N d rows) : ℝ :=
  maxAtom (fun (w : GridSample g G) (ki : Cell d rows × Fin (N + 1)) =>
    dot (stackRows W ki) (centeredF w))

noncomputable def scalarMass (g : ℕ) (G : Fin N → ℕ) (z : Vec (ZMod p) N) : ℝ :=
  maxAtom (fun w : GridSample g G => dot z (centeredF w))

noncomputable def productMass (G : Fin N → ℕ) (z : Fin N → ZMod p) : ℝ :=
  maxAtom (fun k : (i : Fin N) → Fin (G i) =>
    ∑ i, z i * (((2 + ((k i).val : ℤ)) : ℤ) : ZMod p))

end Masses

def atom_comp_equiv.{u, u', v} : Prop :=
  ∀ (X : Type u) (X' : Type u') (Y : Type v) [Fintype X] [Fintype X'] (e : X' ≃ X)
    (f : X → Y) (y : Y), atom (f ∘ e) y = atom f y

theorem atom_eq_count {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) (y : Y) :
    atom f y = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card X := by
  unfold atom
  congr

theorem atom_comp_equiv_holds.{u, u', v} : atom_comp_equiv.{u, u', v} := by
  intro X X' Y _ _ e f y
  classical
  rw [atom_eq_count, atom_eq_count, Fintype.card_congr e]
  congr 2
  exact Finset.card_bij (fun x _ => e x) (by simp) (fun _ _ _ _ h => e.injective h)
    (fun x hx => ⟨e.symm x, by simpa using hx, by simp⟩)

end Praxis.Algebra
