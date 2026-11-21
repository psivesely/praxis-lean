import Praxis.Proofs.NamesInitial
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.NamesBudget
import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesMonitor
import Praxis.Proofs.NamesReservoir
import Praxis.Params
import Praxis.Setting

namespace Praxis.Proofs.Names.Game

open OracleComp OracleSpec

open scoped ENNReal

variable {P : Params}

theorem run_plain (left right : Fq P) (σ : Fq P ↪ Label P)
    {α : Type} (oa : ObsComp P α) (p : Reservoir.Phase) :
    Prod.fst <$> Reservoir.run left right σ oa p = simulateQ (plain σ) oa := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a => rfl
  | query_bind i k ih =>
    rcases i with n | q
    · rw [Reservoir.run_coin]
      simp only [map_bind, ih, simulateQ_bind, simulateQ_query]
      rfl
    · rw [Reservoir.run_probe]
      simp only [ih, simulateQ_bind, simulateQ_query]
      simp [plain, Reservoir.observe]

theorem program_probability [Fact (Nat.Prime P.q)] [Nonempty (Fq P ↪ Label P)]
    (src : LabelEncoding P) (pp : PublicParams P) (forms : FormMatrix P)
    (c : Coins P) (hne : kappa pp c ≠ -kappa pp c) (hdr : Header P) (pad : Msg P)
    (hf : Seed P × FormIndex P → Option (Rq P)) (A : Adversary P) (Q QH R : ℕ)
    (hR : 0 < R) (hreserve : observerBudget Q QH + R ≤ Fintype.card (Label P)) :
    Pr[fun w => firstMark pp w = some .guessName |
      ($ᵗ (Fq P ↪ Label P)) >>= fun σ =>
        restoredWorld src σ (kappa pp c) pad <$>
          simulateQ (plain σ) (program src pp forms c hdr pad hf A Q QH)] ≤
      (observerBudget Q QH : ℝ≥0∞)^2 * (R : ℝ≥0∞)⁻¹^2 := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  calc
    _ ≤ Pr[fun z => z.2 = .success |
        ($ᵗ (Fq P ↪ Label P)) >>= fun σ =>
          Reservoir.run (kappa pp c) (-kappa pp c) σ
            (program src pp forms c hdr pad hf A Q QH) .fresh] := by
      simp only [probEvent_bind_eq_tsum, probEvent_map]
      apply ENNReal.tsum_le_tsum
      intro σ
      refine mul_le_mul' le_rfl ?_
      rw [← run_plain (kappa pp c) (-kappa pp c) σ _ .fresh, probEvent_map]
      exact probEvent_mono (program_guess_implies_success src σ pp forms c hne hdr pad hf A Q QH)
    _ ≤ _ := Reservoir.uniform_run_bound (kappa pp c) (-kappa pp c) hne _
      (observerBudget Q QH) R (program_bound src pp forms c hdr pad hf A Q QH) hR hreserve

end Praxis.Proofs.Names.Game
