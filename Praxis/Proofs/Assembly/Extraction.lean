import Praxis.Proofs.Coupling.Half
import Praxis.Proofs.Query.Marked
import Praxis.Proofs.Names
import Praxis.Proofs.GroupModel.Cmp
import Praxis.Proofs.Differences
import Praxis.Proofs.Ledger.Delta
import Praxis.Proofs.MonitorBounds
import Praxis.Proofs.Monitor.Recover
import Praxis.Proofs.Reduction.Law
import Praxis.Proofs.Injectivity.Inj
import Praxis.Proofs.Injectivity.Sound
import Praxis.Proofs.IndexSelection.Total
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Games
import Praxis.Keys
import Praxis.Ledger
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Init
import Praxis.Proofs.Ledger.Split
import Praxis.Proofs.Monitor.Stop
import Praxis.Proofs.Reduction.Complete
import Praxis.Proofs.Reduction.Sound
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Scheme
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Assembly

open OracleComp OracleSpec

open Praxis.Algebra (Vec)

set_option linter.constructorNameAsVariable false

private theorem prob_or_real_le {α : Type} (law : ProbComp α) (E F : α → Prop) :
    (Pr[fun x => E x ∨ F x | law]).toReal ≤
      (Pr[E | law]).toReal + (Pr[F | law]).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
    (probEvent_or_le law E F)
  simpa only [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] using h

set_option maxHeartbeats 1000000 in
private theorem worldFull_support {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (A : Adversary P) (ext : ExtractorLaw P) (f : FullOut P)
    (hf : f ∈ support (worldFull pp m A ext)) :
    f.w ∈ support (worldRun pp m A) := by
  unfold worldFull at hf
  obtain ⟨w, hw, hf⟩ := support_bind_exists hf
  obtain ⟨ωp, _, hf⟩ := support_bind_exists hf
  obtain ⟨ω0, _, hf⟩ := support_bind_exists hf
  obtain ⟨ω1, _, hf⟩ := support_bind_exists hf
  obtain ⟨x, _, hf⟩ := support_bind_exists hf
  have he := eq_of_mem_support_pure hf
  have hew : f.w = w := congrArg FullOut.w he
  exact hew.symm ▸ hw

private theorem firstMark_cases (pp : PublicParams P0) (w : WorldOut P0)
    (hmark : firstMark pp w ≠ none) :
    firstMark pp w = some .init ∨ firstMark pp w = some .guessName ∨
      ChargedCmp pp w ∨ ∃ D ι, GoodMark pp w D ι := by
  classical
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hmark
  cases k with
  | init => exact Or.inl hk
  | guessName => exact Or.inr (Or.inl hk)
  | g1 => exact Or.inr (Or.inr (Or.inl ⟨.g1, hk, Or.inl rfl⟩))
  | g2 => exact Or.inr (Or.inr (Or.inl ⟨.g2, hk, Or.inr (Or.inl rfl)⟩))
  | keyFormal =>
    exact Or.inr (Or.inr (Or.inl ⟨.keyFormal, hk, Or.inr (Or.inr (Or.inl rfl))⟩))
  | diff D =>
    by_cases hgood : GoodCmp pp w D 0
    · exact Or.inr (Or.inr (Or.inr ⟨D, 0, .diff D, hk, rfl, hgood⟩))
    · exact Or.inr (Or.inr (Or.inl
        ⟨.diff D, hk, Or.inr (Or.inr (Or.inr ⟨D, 0, rfl, hgood⟩))⟩))
  | key D =>
    by_cases hgood : GoodCmp pp w D 1
    · exact Or.inr (Or.inr (Or.inr ⟨D, 1, .key D, hk, rfl, hgood⟩))
    · exact Or.inr (Or.inr (Or.inl
        ⟨.key D, hk, Or.inr (Or.inr (Or.inr ⟨D, 1, rfl, hgood⟩))⟩))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem target_failure_bound
    (h_marked : type_of% @Praxis.Proofs.Query.target_marked)
    (h_init : type_of% @Praxis.Proofs.GroupModel.gg_init)
    (h_cmp : type_of% @Praxis.Proofs.GroupModel.gg_cmp)
    (h_name : type_of% @Praxis.Proofs.Names.gg_name)
    (h_ediff : type_of% @Praxis.Proofs.Differences.good_mark_passing)
    (h_mon : type_of% @Praxis.Proofs.Monitor.monitor_at_mark)
    (h_rec : type_of% @Praxis.Proofs.Monitor.recovery_span)
    (h_complete : type_of% @Praxis.Proofs.Reduction.red_complete)
    (h_sound : type_of% @Praxis.Proofs.Reduction.red_sound)
    (h_law : type_of% @Praxis.Proofs.Reduction.red_law)
    (h_inj : type_of% @Praxis.Proofs.Injectivity.jse_inj)
    (h_split : type_of% @Praxis.Proofs.Ledger.ledger_split)
    (h_monfit : type_of% @Praxis.Proofs.MonitorBounds.monfit)
    (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (Q QH : ℕ) (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => TargetQueried (ppOf ch S) f.w ∧ ExtFails S f.x |
      worldFull (ppOf ch S) m A extF]).toReal ≤
        (ledgerE (simBudget Q) : ℝ) + (scheme ch).succ S m A := by
  classical
  let law := worldFull (ppOf ch S) m A extF
  let I : FullOut P0 → Prop := fun f => firstMark (ppOf ch S) f.w = some .init
  let N : FullOut P0 → Prop := fun f => firstMark (ppOf ch S) f.w = some .guessName
  let C : FullOut P0 → Prop := fun f => ChargedCmp (ppOf ch S) f.w
  let M : FullOut P0 → Prop := fun f => ∃ D ι, GoodMark (ppOf ch S) f.w D ι ∧
    monitor (monCtx (redViewOf (ppOf ch S) m f.w) f.wp) f.w.out.pv f.w.st.tr
      f.w.st.kdfLog ≠ MonStop.stack D
  let R : FullOut P0 → Prop := fun f => ∃ D ι, GoodMark (ppOf ch S) f.w D ι ∧
    gradSpan (ppOf ch S) (recAssign f.w0 f.w1) D (markSector D) ≠ jointSpace (markStack D)
  let J : FullOut P0 → Prop := fun f => InjCase (ppOf ch S) f.w ∧ ExtFails S f.x
  let W : FullOut P0 → Prop := RmWins main_d_ne_zero (ppOf ch S) m
  have hcover : ∀ f ∈ support law,
      TargetQueried (ppOf ch S) f.w ∧ ExtFails S f.x →
        I f ∨ N f ∨ C f ∨ M f ∨ R f ∨ J f ∨ W f := by
    intro f hf ht
    have hsupport : f.w ∈ support (worldRun (ppOf ch S) m A) := by
      with_reducible exact (@worldFull_support P0 main_prime main_encodings
        (ppOf ch S) (ppOf_coins ch S) m A extF f hf)
    have hmark : firstMark (ppOf ch S) f.w ≠ none := by
      with_reducible exact (@h_marked (ppOf ch S) (ppOf_coins ch S) m A f.w hsupport ht.1)
    rcases firstMark_cases (ppOf ch S) f.w hmark with hi | hn | hc | ⟨D, ι, hg⟩
    · exact Or.inl hi
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr (Or.inl hc))
    · right; right; right
      by_cases hk : jointSpace (markStack D) ⊓ LinearMap.ker (zLin (formsOfRun f.w)) = ⊥
      · right; right; left
        exact ⟨⟨D, ι, hg, hk, (h_ediff ch S hS f.w D ι hg).2.2.2⟩, ht.2⟩
      · by_cases hm : monitor (monCtx (redViewOf (ppOf ch S) m f.w) f.wp) f.w.out.pv
            f.w.st.tr f.w.st.kdfLog = MonStop.stack D
        · by_cases hr : gradSpan (ppOf ch S) (recAssign f.w0 f.w1) D (markSector D) =
              jointSpace (markStack D)
          · right; right; right
            have hout := h_complete ch S hS m f D ι hg hk hm hr
            obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hout
            exact ⟨z, hz, h_sound (redViewOf (ppOf ch S) m f.w) f.wp
              (recAssign f.w0 f.w1) z hz⟩
          · right; left
            exact ⟨D, ι, hg, hr⟩
        · left
          exact ⟨D, ι, hg, hm⟩
  have hp := ENNReal.toReal_mono probEvent_ne_top (probEvent_mono hcover)
  have hu0 := prob_or_real_le law I (fun f => N f ∨ C f ∨ M f ∨ R f ∨ J f ∨ W f)
  have hu1 := prob_or_real_le law N (fun f => C f ∨ M f ∨ R f ∨ J f ∨ W f)
  have hu2 := prob_or_real_le law C (fun f => M f ∨ R f ∨ J f ∨ W f)
  have hu3 := prob_or_real_le law M (fun f => R f ∨ J f ∨ W f)
  have hu4 := prob_or_real_le law R (fun f => J f ∨ W f)
  have hu5 := prob_or_real_le law J W
  have hi : (Pr[I | law]).toReal ≤ (ledgerInit : ℝ) := h_init ch S hS Q QH A hA m
  have hn : (Pr[N | law]).toReal ≤ (ledgerName : ℝ) := h_name ch S hS Q QH A hA m
  have hc : (Pr[C | law]).toReal ≤ (ledgerCmp (simBudget Q) : ℝ) :=
    h_cmp ch S hS Q QH A hA m
  have hm : (Pr[M | law]).toReal ≤ (Constants.eps_f : ℝ) := h_mon ch S hS Q QH A hA m
  have hr : (Pr[R | law]).toReal ≤ (Constants.eps_f : ℝ) := h_rec ch S hS Q QH A hA m
  have hj : (Pr[J | law]).toReal ≤ (Constants.extractor_recovery_failure_per_sector : ℝ) :=
    h_inj ch S hS Q QH A hA m
  have hw : (Pr[W | law]).toReal = (scheme ch).succ S m A := (h_law ch S A m).symm
  have hfit : 2 * (Constants.eps_f : ℝ) +
      (Constants.extractor_recovery_failure_per_sector : ℝ) ≤ (ledgerRec (simBudget Q) : ℝ) := by
    exact_mod_cast h_monfit (simBudget Q)
  have hs : (ledgerE (simBudget Q) : ℝ) = (ledgerInit : ℝ) +
      (ledgerCmp (simBudget Q) : ℝ) + (ledgerName : ℝ) + (ledgerRec (simBudget Q) : ℝ) := by
    exact_mod_cast h_split (simBudget Q)
  linarith only [hp, hu0, hu1, hu2, hu3, hu4, hu5, hi, hn, hc, hm, hr, hj, hw, hfit, hs]

theorem extraction_of_lemmas (ch : AdmissibleChoice Params.main)
    (h_jset : type_of% @Praxis.Proofs.IndexSelection.jset_total)
    (h_couple : type_of% @Praxis.Proofs.Coupling.couple_half)
    (h_marked : type_of% @Praxis.Proofs.Query.target_marked)
    (h_init : type_of% @Praxis.Proofs.GroupModel.gg_init)
    (h_cmp : type_of% @Praxis.Proofs.GroupModel.gg_cmp)
    (h_name : type_of% @Praxis.Proofs.Names.gg_name)
    (h_ediff : type_of% @Praxis.Proofs.Differences.good_mark_passing)
    (h_mon : type_of% @Praxis.Proofs.Monitor.monitor_at_mark)
    (h_rec : type_of% @Praxis.Proofs.Monitor.recovery_span)
    (h_complete : type_of% @Praxis.Proofs.Reduction.red_complete)
    (h_sound : type_of% @Praxis.Proofs.Reduction.red_sound)
    (h_law : type_of% @Praxis.Proofs.Reduction.red_law)
    (h_inj : type_of% @Praxis.Proofs.Injectivity.jse_inj)
    (h_split : type_of% @Praxis.Proofs.Ledger.ledger_split)
    (h_monfit : type_of% @Praxis.Proofs.MonitorBounds.monfit)
    (h_min : type_of% @Praxis.Proofs.Ledger.ledger_min)
    (h_jsound : type_of% @Praxis.Proofs.Injectivity.jse_sound) :
    ∀ S : Relation (scheme ch).params, InShape (scheme ch).params S →
    ∀ (Q QH : ℕ) (A : Adversary (scheme ch).params), InClass A Q QH →
    ∀ m0 m1 : Msg (scheme ch).params,
      (∀ input ∈ support ((scheme ch).extractInputs S m0 m1 A),
        WithinUnits ((scheme ch).extractor (sparseOf S) input.1 input.2)
            (simBudget Q * (Constants.running_time_extractor_per_w +
                Constants.running_time_extractor_per_w_per_S * size S) +
              Constants.running_time_extractor_setup) ∧
          SmallSamples ((scheme ch).extractor (sparseOf S) input.1 input.2)) ∧
      ((Pr[= true | (scheme ch).extractExp S m0 m1 A]).toReal ≤
          1 / 2 + 1 / 2 * ((ledgerE (simBudget Q) : ℝ) + (scheme ch).succ S m0 A +
            (scheme ch).succ S m1 A) ∧
        (ledgerE (simBudget Q) : ℝ) ≤
          min (((Q : ℝ) + 1) / (Constants.T : ℝ)) (1 - (Constants.ledger_delta : ℝ))) ∧
      ∀ (pub : PubView (scheme ch).params) (tr : List (TrOp (scheme ch).params))
        (x : Vec (Fq (scheme ch).params) (scheme ch).params.N),
        some x ∈ support (runUnits ((scheme ch).extractor (sparseOf S) pub tr)) →
          IsWitness S x := by
  intro S hS Q QH A hA m0 m1
  refine ⟨h_jset ch S hS Q QH A hA m0 m1, ⟨?_, h_min Q hA.Q_lt⟩, ?_⟩
  · have h0 := target_failure_bound h_marked h_init h_cmp h_name h_ediff h_mon h_rec
      h_complete h_sound h_law h_inj h_split h_monfit ch S hS Q QH A hA m0
    have h1 := target_failure_bound h_marked h_init h_cmp h_name h_ediff h_mon h_rec
      h_complete h_sound h_law h_inj h_split h_monfit ch S hS Q QH A hA m1
    have hn0 : 0 ≤ (scheme ch).succ S m0 A := by
      rw [h_law ch S A m0]
      exact ENNReal.toReal_nonneg
    have hn1 : 0 ≤ (scheme ch).succ S m1 A := by
      rw [h_law ch S A m1]
      exact ENNReal.toReal_nonneg
    have hc := h_couple ch S A m0 m1
    linarith only [hc, h0, h1, hn0, hn1]
  · intro pub tr x hx
    have he : (scheme ch).extractor =
        @extractorC (scheme ch).params (scheme ch).prime := by
      unfold scheme
      rfl
    rw [he] at hx
    with_reducible exact (@h_jsound (scheme ch).params (scheme ch).prime S pub tr x hx)

end Praxis.Proofs.Assembly
