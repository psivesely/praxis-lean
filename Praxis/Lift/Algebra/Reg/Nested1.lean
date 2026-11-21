import Praxis.Lift.Algebra.Reg.Rank1Model
import Praxis.Lift.Record
import Praxis.Algebra.Reg.Rank1Model
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Nested1

open Praxis.Algebra Praxis.Algebra.Reg

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Lift.Algebra.Reg.Rank1Model

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Algebra.Reg.Rank1Model hiding Rank1Promotion Rank1Return21 Rank1Return31 Rank1NestedCall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nested_handoff (P : VITParameters) {m1 m2 : ℝ}
    (hm1 : P.theta0 - 20 * P.eps ≤ m1) (hm2 : m1 - P.eps ≤ m2) :
    P.theta0 - 21 * P.eps ≤ m2 := by
  linarith

theorem domain_widening (P : VITParameters) :
    P.theta0 - 30 * P.eps ≤ P.theta0 - 21 * P.eps := by
  linarith [P.eps_pos]

theorem rank_two_retention (P : VITParameters) {m1 m2 : ℝ}
    (hm2 : m1 - P.eps ≤ m2) : m1 - 2 * P.eps ≤ m2 := by
  linarith [P.eps_pos]

theorem rank_three_retention (P : VITParameters) {m1 m2 m3 : ℝ}
    (hm2 : m1 - P.eps ≤ m2) (hm3 : m2 - P.eps ≤ m3) :
    m1 - 2 * P.eps ≤ m3 := by
  linarith

theorem rank1_nested_call (P : VITParameters) (G : ι → ℕ)
    (L1 : IntLat ι 1) (L2 : IntLat ι 2) : Rank1NestedCall P G L1 L2 := by
  intro hG hm1 hcontain hm2 hV7

  have h21 : P.theta0 - 21 * P.eps ≤ L2.mZ G := nested_handoff P hm1 hm2
  have hdomain : P.theta0 - 30 * P.eps ≤ L2.mZ G :=
    (domain_widening P).trans h21
  refine ⟨hdomain, ?_⟩

  rcases hV7 hG hdomain with hreg2 | ⟨L3, h23, hm3, hH3, hreg3⟩
  · exact Or.inl ⟨L2, hcontain, rank_two_retention P hm2, hreg2⟩
  · exact Or.inr ⟨L3, hcontain.trans h23, rank_three_retention P hm2 hm3,
      hH3, hreg3⟩

end Algebra.Reg.Nested1

end Praxis.Lift
