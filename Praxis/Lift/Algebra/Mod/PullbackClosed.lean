import Praxis.Lift.Algebra.Mod.Pullback
import Praxis.Algebra.Sat.Annihilator
import Praxis.Algebra.Sat.Summand
import Praxis.Lift.Record
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.PullbackClosed

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

universe u

theorem modPullback_all (p : ℕ) :
    ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (d : ℕ) (L : IntLat α d) (E : Submodule ℤ (Option (Fin d) → ℤ))
      (c : Option (Fin d) → ZMod p), ModPullback L E c :=
  fun _ _ _ _ L E c =>
    Algebra.Mod.Pullback.modPullback L E c
      (Algebra.Sat.satAnnihilatorEq Algebra.Sat.satDirectSummand)

theorem hpb (P : VITParameters) :
    ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (d : ℕ) (L : IntLat α d) (E : Submodule ℤ (Option (Fin d) → ℤ))
      (c : Option (Fin d) → ZMod P.p), ModPullback L E c :=
  modPullback_all P.p

end Algebra.Mod.PullbackClosed

end Praxis.Lift
