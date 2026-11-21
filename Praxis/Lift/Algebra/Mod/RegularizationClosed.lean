import Praxis.Lift.Algebra.Mod.Wrap2Poly
import Praxis.Lift.Algebra.Reg.Regularize1Assemble
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.RegularizationClosed

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

theorem regularize1_all.{u} (P : VITParameters) :
    ∀ (α : Type u) [Fintype α] [DecidableEq α] (G : α → ℕ) (L : IntLat α 1),
      Algebra.Reg.Definitions.Regularize1 P G L :=
  fun _ _ _ G L => Algebra.Reg.Assemble1.regularize1 P G L

theorem modular_regularization.{u} (P : VITParameters)
    (α : Type u) [Fintype α] [DecidableEq α]
    (G : α → ℕ) (z : α → ZMod P.p) : ModularRegularization P G z :=
  Algebra.Mod.Wrap2Poly.modular_regularization_of_regularize1 P (regularize1_all P) α G z

end Algebra.Mod.RegularizationClosed

end Praxis.Lift
