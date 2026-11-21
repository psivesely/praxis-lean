import Praxis.Proofs.Monitor.Stop.Fold
import Praxis.Proofs.Monitor.Stop.Sampling
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Stop.Deterministic
import Praxis.Params
import Praxis.Reduction

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

variable {P : Params} [Fact (Nat.Prime P.q)]

noncomputable local instance (pp : PublicParams P) [Nonempty (ValidCoin pp)] :
    SampleableType (AssignSample pp) :=
  SampleableType.ofFintype (AssignSample pp)

theorem fixed_world_bound_of_roots (pp : PublicParams P) (m : Msg P) (w : WorldOut P)
    [Nonempty (ValidCoin pp)] (b : ENNReal)
    (hroot : ∀ D ι, (¬ ∀ ω, ValidCoins pp.qap ω.coins →
        valT pp (formsOfRun w) ω D = ι * kappa pp ω.coins) →
      Pr[fun z : AssignSample pp =>
        valT pp (formsOfRun w) (sampleToAssign z) D = ι * kappa pp (sampleToAssign z).coins |
        $ᵗ (AssignSample pp)] ≤ b) :
    Pr[fun z : AssignSample pp => ∃ D ι, GoodMark pp w D ι ∧
      monitor (monCtx (redViewOf pp m w) (sampleToAssign z)) w.out.pv w.st.tr w.st.kdfLog ≠
        .stack D | $ᵗ (AssignSample pp)] ≤ b := by
  classical
  by_cases hg : ∃ D ι, GoodMark pp w D ι
  · obtain ⟨D, ι, hgood⟩ := hg
    apply le_trans _ (hroot D ι (goodMark_nonformal pp w D ι hgood))
    apply probEvent_mono
    intro z _ hz
    obtain ⟨D', ι', hg', hm⟩ := hz
    obtain ⟨hD, hι⟩ := goodMark_unique pp w hg' hgood
    subst D'
    subst ι'
    exact fixed_world_miss pp m w D ι (sampleToAssign z) hgood z.1.2 hm
  · have hempty : (fun _z : AssignSample pp => ∃ D ι, GoodMark pp w D ι ∧
        monitor (monCtx (redViewOf pp m w) (sampleToAssign _z)) w.out.pv w.st.tr
          w.st.kdfLog ≠ .stack D) = fun _ => False := by
      funext z
      apply propext
      constructor
      · rintro ⟨D, ι, hgood, _⟩
        exact hg ⟨D, ι, hgood⟩
      · intro h
        exact h.elim
    rw [hempty]
    simp

end Praxis.Proofs.Monitor
