import Praxis.Algebra.Definitions.Sampler
import Praxis.Algebra.Definitions.Stack

set_option autoImplicit false

namespace Praxis.Algebra.RankMass

open Finset Matrix

open scoped BigOperators

section Defs

variable {p N : ℕ}

abbrev TailSample (G : Fin N → ℕ) := (i : Fin N) → Fin (G i)

def tailForm (G : Fin N → ℕ) (z : Fin N → ZMod p) (k : TailSample G) : ZMod p :=
  ∑ i, z i * (((2 + ((k i).val : ℤ)) : ℤ) : ZMod p)

end Defs

section Rank

variable {p N d rows : ℕ} [Fact p.Prime]

def RankBoundAt (g : ℕ) (G : Fin N → ℕ) (W : Stack (ZMod p) N d rows) : Prop :=
  stackMass g G W ≤ 1 / (g : ℝ) ^ stackRank W

def RankFourAt (g : ℕ) (G : Fin N → ℕ) (W : Stack (ZMod p) N d rows) : Prop :=
  4 ≤ stackRank W → stackMass g G W ≤ 1 / (g : ℝ) ^ 4

end Rank

def centered_rank_bound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N d rows g : ℕ) (G : Fin N → ℕ),
    0 < g → (∀ i, g ≤ G i ∧ G i ≤ p) → g ≤ p →
    ∀ W : Stack (ZMod p) N d rows, RankBoundAt g G W

def rank_ge_four_light : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N d rows g : ℕ) (G : Fin N → ℕ),
    0 < g → (∀ i, g ≤ G i ∧ G i ≤ p) → g ≤ p →
    ∀ W : Stack (ZMod p) N d rows, RankFourAt g G W

section Tools

def cnt {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) (y : Y) : ℕ :=
  (univ.filter (fun x => f x = y)).card

theorem atom_eq_cnt {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) (y : Y) :
    atom f y = (cnt f y : ℝ) / Fintype.card X :=
  atom_eq_count f y

variable {N g : ℕ} {G : Fin N → ℕ}

theorem coord0_zero_of_rows {F : Type*} [Field F] {N d rows : ℕ} (W : Stack F N d rows)
    (h : ∀ ki, stackRows W ki 0 = 0) : ∀ v ∈ stackSpace W, v 0 = 0 := by
  intro v hv
  have hle : stackSpace W ≤ LinearMap.ker (LinearMap.proj (R := F)
      (φ := fun _ : Fin (N + 1) => F) 0) := by
    rw [stackSpace, Submodule.span_le]
    rintro _ ⟨ki, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
    exact h ki
  simpa using LinearMap.mem_ker.mp (hle hv)

end Tools

end Praxis.Algebra.RankMass
