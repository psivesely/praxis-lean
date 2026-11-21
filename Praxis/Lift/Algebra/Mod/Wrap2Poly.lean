import Praxis.Lift.Algebra.Mod.Wrap2
import Praxis.Lift.Algebra.Mod.Wrap3
import Praxis.Algebra.Trans.CauchyBinet
import Praxis.Algebra.Trans.Esym
import Praxis.Lift.Algebra.Mod.Wrap1
import Praxis.Lift.Algebra.Mod.Induct
import Praxis.Lift.Algebra.Mod.PullbackClosed
import Praxis.Lift.Algebra.Reg.Step2Actual
import Praxis.Lift.Algebra.Reg.Regularize2Closed
import Praxis.Algebra.Point.Dim4
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Mod.Definitions
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Algebra.Mod.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

noncomputable section

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Mod.Wrap2Poly

open Praxis.Algebra Praxis.Algebra.Mod

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Mod.Definitions

open Praxis.Algebra.Mod.Definitions hiding FullImageExclusion SaturationApplication ModStep
  ModularRegularization FinalFromModular

theorem fullImageExclusion_of_sectionCount3.{u} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (hc : Algebra.Point.SectionCount3) (P : VITParameters) (G : ι → ℕ) (Gx : ℕ)
    (L : IntLat ι 2) (c : Option (Fin 2) → ZMod P.p) (t : ZMod P.p)
    (F : Finset (Grid (extend G Gx))) : FullImageExclusion 2 P G Gx L c t F := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  intro _ _ hbudget hreg hnc hF hf htrim hrank
  let : Fact P.p.Prime := ⟨P.p_prime⟩
  have hg : 0 < P.g := lt_of_lt_of_le (Nat.pow_pos (by decide)) P.g_lower
  have hG : ∀ i, 0 < G i := fun i => hg.trans_le (hbudget.1 (some i))
  have hSigma := Algebra.Mod.Wrap3.covariance_posDef G hG L
  refine ⟨Algebra.Mod.Wrap2.congruenceKernel_card c hnc,
    Algebra.Mod.Wrap2.fibre_in_coset _ c t F hF hf, ?_, ?_⟩
  · have hcount := Algebra.Mod.Wrap2.image_count hc P G Gx L c t F hnc hF hf htrim hrank hSigma
    simpa [wrapFactor, VITData.C] using
      Algebra.Mod.Wrap2.density_bound_of_image_count P G Gx L F hbudget hreg
        (Algebra.Trans.cauchyBinet3 _ _) (Algebra.Trans.esymBounds _ _) hcount
  · simpa [wrapFactor, VITData.C] using P.wrap2

theorem fullImageExclusion_all.{u} (P : VITParameters) :
    ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (d : ℕ) (G : α → ℕ) (Gx : ℕ) (L : IntLat α d) c t F,
      FullImageExclusion d P G Gx L c t F
  | _, _, _, 0, _, _, _, _, _, _ => fun h1 => absurd h1 (by decide)
  | _, _, _, 1, G, Gx, L, c, t, F =>
    Algebra.Mod.Wrap1.fullImageExclusion Algebra.Reg.Step2.Actual.planar
      (fun _ _ B σ => Algebra.Trans.cauchyBinet3 B σ)
      (fun _ w s => Algebra.Trans.esymBounds w s)
      Algebra.Reg.Step2.Actual.trim P G Gx L c t F
  | _, _, _, 2, G, Gx, L, c, t, F =>
    fullImageExclusion_of_sectionCount3 Algebra.Reg.Step2.Actual.section3 P G Gx L c t F
  | _, _, _, 3, G, Gx, L, c, t, F =>
    Algebra.Mod.Wrap3.fullImageExclusion
      (Algebra.Point.sectionCount4 (Algebra.Reg.Step2.Actual.simplex_count 4)
        Algebra.Reg.Step2.Actual.simplex_lower)
      (fun _ _ _ _ B σ => Algebra.Trans.cauchyBinet3 B σ)
      (fun _ _ _ w S => Algebra.Trans.esymBounds w S)
      Algebra.Reg.Step2.Actual.trim P G Gx L c t F
  | _, _, _, _ + 4, _, _, _, _, _, _ => fun _ h3 => absurd h3 (by omega)

theorem modular_regularization_of_regularize1.{u} (P : VITParameters)
    (h1 : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (G : α → ℕ) (L : IntLat α 1), Algebra.Reg.Definitions.Regularize1 P G L)
    (α : Type u) [Fintype α] [DecidableEq α]
    (G : α → ℕ) (z : α → ZMod P.p) : ModularRegularization P G z :=
  Algebra.Mod.Induct.modular_regularization P (fullImageExclusion_all P)
    (Algebra.Mod.PullbackClosed.hpb P)
    (fun _ _ _ G L => Algebra.Reg.Step2.Actual.rank3 P G L)
    (fun _ _ _ G L => Algebra.Reg.Closed2.regularize2 P G L) h1 α G z

end Algebra.Mod.Wrap2Poly

end Praxis.Lift
