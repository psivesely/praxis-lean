import Praxis.Proofs.IndexSelection.Trace
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.IndexSelection.Setup
import Praxis.Proofs.IndexSelection.Step
import Praxis.Params
import Praxis.Relation
import Praxis.Scheme
import Praxis.Units

namespace Praxis.Proofs.IndexSelection

open OracleComp OracleSpec

set_option maxRecDepth 4096

private theorem enc_view {P : Params} [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P)
    (z : EncOut P × OracleState P)
    (hz : z ∈ support ((encGame σ pp m).run OracleState.empty)) :
    ∃ v c, z.1.pv = pubView σ pp v c := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [encGame, encAt, StateT.run_bind, StateT.run_lift, bind_assoc,
    pure_bind, StateT.run_modify, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨seed, _, es, hes, cs, _, pad, hpad, rfl⟩ := hz
  exact ⟨_, _, rfl⟩

private theorem run_view {P : Params} [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (A : Adversary P) (z : (EncOut P × Bool) × OracleState P)
    (hz : z ∈ support (runWith σ A (encGame σ pp m) OracleState.empty)) :
    ∃ v c, z.1.1.pv = pubView σ pp v c := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [runWith, StateT.run_bind, StateT.run_pure, bind_assoc,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨es, hes, out, hout, rfl⟩ := hz
  exact enc_view σ pp m es hes

private theorem fold_bound {P : Params} (S : Relation P) (hS : InShape P S)
    (hP : P = P0) (tr : List (TrOp P)) (st : ExState P) :
    WithinUnits (tr.foldlM (exStepC (sparseOf S)) st)
      (tr.length * (Constants.running_time_extractor_per_operation + 1 +
        2 * 2 * (Constants.running_time_extractor_per_sector_test +
          Constants.running_time_extractor_per_sector_test_per_S * size S))) := by
  induction tr generalizing st with
  | nil => simp [List.foldlM, WithinUnits]
  | cons op tr ih =>
    simp only [List.foldlM_cons, List.length_cons]
    rw [Nat.succ_mul, Nat.add_comm]
    exact isQueryBoundP_bind (jset_step P hP S hS st op) (fun st' _ => ih st')

private theorem extractor_bound (P : Params) [Fact (Nat.Prime P.q)] (hP : P = P0)
    (S : Relation P) (hS : InShape P S) (Q : ℕ) (pub : PubView P) (tr : List (TrOp P))
    (hlen : tr.length ≤ Q)
    (hview : ∃ σ pp v c, pub = pubView σ pp v c) :
    WithinUnits (extractorC (sparseOf S) pub tr)
      (simBudget Q * (Constants.running_time_extractor_per_w +
        Constants.running_time_extractor_per_w_per_S * size S) +
        Constants.running_time_extractor_setup) := by
  obtain ⟨σ, pp, v, c, rfl⟩ := hview
  unfold extractorC
  have hb : WithinUnits (do
      let sk ← drawSketchesC
      let st ← initStateC (pubView σ pp v c) sk
      let st' ← tr.foldlM (exStepC (sparseOf S)) st
      pure st'.found)
      (Constants.running_time_extractor_sketch_draws +
        (Constants.running_time_extractor_R1_total_scalars +
          Constants.running_time_extractor_label_table +
          (tr.length * (Constants.running_time_extractor_per_operation + 1 +
            2 * 2 * (Constants.running_time_extractor_per_sector_test +
              Constants.running_time_extractor_per_sector_test_per_S * size S)) + 0))) := by
    refine isQueryBoundP_bind (jset_draw P hP) (fun sk _ => ?_)
    refine isQueryBoundP_bind (jset_init P hP σ pp v c sk) (fun st _ => ?_)
    refine isQueryBoundP_bind (fold_bound S hS hP tr st) (fun st' _ => ?_)
    exact isQueryBoundP_pure isUnit st'.found 0
  refine hb.mono ?_
  have hm := Nat.mul_le_mul_right
    (Constants.running_time_extractor_per_operation + 1 +
      2 * 2 * (Constants.running_time_extractor_per_sector_test +
        Constants.running_time_extractor_per_sector_test_per_S * size S)) hlen
  have hqs : 0 ≤ Q * size S := Nat.zero_le _
  dsimp only [simBudget, Constants.LT, Constants.running_time_extractor_sketch_draws,
    Constants.running_time_extractor_R1_total_scalars,
    Constants.running_time_extractor_label_table, Constants.running_time_extractor_per_operation,
    Constants.running_time_extractor_per_sector_test,
    Constants.running_time_extractor_per_sector_test_per_S,
    Constants.running_time_extractor_per_w, Constants.running_time_extractor_per_w_per_S,
    Constants.running_time_extractor_setup] at hm ⊢
  nlinarith only [hm, hqs, Nat.zero_le Q, Nat.zero_le (size S)]

theorem jset_total (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S) (Q QH : ℕ)
    (A : Adversary P0) (hA : InClass A Q QH) (m0 m1 : Msg P0) :
    ∀ input ∈ support ((scheme ch).extractInputs S m0 m1 A),
      WithinUnits ((scheme ch).extractor (sparseOf S) input.1 input.2)
          (simBudget Q * (Constants.running_time_extractor_per_w +
              Constants.running_time_extractor_per_w_per_S * size S) +
            Constants.running_time_extractor_setup) ∧
        SmallSamples ((scheme ch).extractor (sparseOf S) input.1 input.2) := by
  intro input hinput
  letI : Fact (Nat.Prime P0.q) := (scheme ch).prime
  have hlen := jset_trace ch S Q QH A hA m0 m1 input hinput
  letI := (scheme ch).coins_nonempty S
  have hview : ∃ σ v c, input.1 = pubView σ ((scheme ch).setup S) v c := by
    have hi := hinput
    simp only [Scheme.extractInputs, bind_assoc, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hi
    obtain ⟨b, _, σ, _, out, hout, rfl⟩ := hi
    obtain ⟨v, c, hv⟩ := run_view σ ((scheme ch).setup S) (if b then m1 else m0) A out hout
    exact ⟨σ, v, c, hv⟩
  have hv : ∃ σ pp v c, input.1 = pubView σ pp v c := by
    obtain ⟨σ, v, c, h⟩ := hview
    exact ⟨σ, (scheme ch).setup S, v, c, h⟩
  change PubView P0 × List (TrOp P0) at input
  change input.2.length ≤ Q at hlen
  change (∃ σ pp v c, input.1 = pubView σ pp v c) at hv
  have hq : P0.q ≤ 2 ^ unitWordBits := by
    change Constants.q ≤ 2 ^ unitWordBits
    decide +kernel
  dsimp only [scheme]
  constructor
  · with_reducible
      exact extractor_bound P0 rfl S hS Q input.1 input.2 hlen hv
  · with_reducible
      exact jset_small hq S input.1 input.2

end Praxis.Proofs.IndexSelection
