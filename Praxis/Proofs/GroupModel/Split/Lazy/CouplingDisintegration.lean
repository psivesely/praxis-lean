import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Probability
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Observed
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Factor
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Coins
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Padding
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingPending
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCountStep
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.NotMono
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitFinal
import Praxis.Proofs.GroupModel.Split.Lazy.FoldDisintegration
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Domination
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Relation
import Praxis.Search

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration

open Classical

section Abstract

variable {α β Ω : Type}

lemma exists_joint_of_dominated (obs : ProbComp Ω) (trials : ProbComp β)
    (E : Ω → Prop) (T : Ω → ProbComp β)
    (hdom : ∀ b, (∑' ω, Pr[= ω | obs] * (if E ω then Pr[= b | T ω] else 0)) ≤
      Pr[= b | trials]) :
    ∃ joint : ProbComp (Ω × β),
      evalSPMF (Prod.fst <$> joint) = evalSPMF obs ∧
      evalSPMF (Prod.snd <$> joint) = evalSPMF trials ∧
      ∀ z ∈ support joint, E z.1 → z.2 ∈ support (T z.1) := by
  exact Domination.exists_joint_of_dominated obs trials E T hdom

end Abstract

section Assembly

variable {ch : AdmissibleChoice P0} {S : Relation P0} {Ω : Type} {i : Kind}

namespace SlotDistribution

def coupling (p : SlotDistribution ch S Ω i) (obs : ProbComp Ω)
    (event : Ω → Prop) (hdom : p.Dominated obs event) :
    SlotCoupling ch S obs i :=
  let h := exists_joint_of_dominated obs p.preparation.trials event p.extract hdom
  { preparation := p.preparation
    joint := h.choose
    world_law := h.choose_spec.1
    trial_law := h.choose_spec.2.1 }

lemma coupling_hit (p : SlotDistribution ch S Ω i) (obs : ProbComp Ω)
    (event : Ω → Prop) (hdom : p.Dominated obs event) (hhit : p.Hits obs event) :
    ∀ z ∈ support (p.coupling obs event hdom).joint,
      event z.1 → (p.coupling obs event hdom).preparation.Hit z.2 := by
  intro y hy he
  let h := exists_joint_of_dominated obs p.preparation.trials event p.extract hdom
  change y ∈ support h.choose at hy
  have hobs : y.1 ∈ support obs := by
    have h1 := h.choose_spec.1
    have hs : y.1 ∈ support (Prod.fst <$> h.choose) := by
      rw [support_map]; exact ⟨y, hy, rfl⟩
    have he : Pr[= y.1 | obs] = Pr[= y.1 | Prod.fst <$> h.choose] := by
      rw [probOutput_def, probOutput_def, h1]
    rw [← probOutput_pos_iff] at hs ⊢
    rwa [he]
  exact hhit y.1 hobs he y.2 (h.choose_spec.2.2 y hy he)

end SlotDistribution

theorem fold_of_distributions (ch : AdmissibleChoice P0) (S : Relation P0) (w : ℕ)
    (obs : ProbComp Ω) (π : Ω → WorldOut P0)
    (events : EventsOn Ω w) (distribution : (i : Kind) → Fin (quota w i) → SlotDistribution ch S Ω i)
    (hcharged : ∀ i j ω, events i j ω → ChargedCmp (ppOf ch S) (π ω))
    (hcover : ∀ ω ∈ support obs, ChargedCmp (ppOf ch S) (π ω) → ∃ i j, events i j ω)
    (hdom : ∀ i j, (distribution i j).Dominated obs (events i j))
    (hhit : ∀ i j, (distribution i j).Hits obs (events i j)) :
    ∃ (coupling : GenericCoupling ch S obs w),
      DeterministicFold ch S obs π w coupling events :=
  ⟨fun i j => (distribution i j).coupling obs (events i j) (hdom i j),
    hcharged, hcover, fun i j z hz he =>
      (distribution i j).coupling_hit obs (events i j) (hdom i j) (hhit i j) z hz he⟩

end Assembly

section Core

variable (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)

lemma observedRun_law :
    evalSPMF (Prod.fst <$> observedRun (ppOf ch S) m A) = evalSPMF (lazyRun ch S m A) := by
  exact ObservedLaw.observedRun_law ch S m A

lemma observedRun_valid :
    ∀ ω ∈ support (observedRun (ppOf ch S) m A),
      ValidCoins (ppOf ch S).qap ω.1.out.coins := by
  exact ObservedLaw.observedRun_valid ch S m A

lemma cons_step (r : Record (ppOf ch S)) (c : Coupling.Symbolic.CoinDomain (ppOf ch S))
    (x : ℕ → k) : Simulation.ConsStep (ppOf ch S) r c x :=
  Simulation.cons_step_proof (ppOf ch S) r c x

lemma cover_step (c : Coupling.Symbolic.CoinDomain (ppOf ch S)) (x : ℕ → k) :
    Simulation.CoverStep (ppOf ch S) c x :=
  Simulation.cover_step_proof (ppOf ch S) c x

lemma count_step (n : ℕ) (r : Record (ppOf ch S))
    (c : Coupling.Symbolic.CoinDomain (ppOf ch S)) (x : ℕ → k) :
    Simulation.CountStep (ppOf ch S) n r c x :=
  Simulation.count_step_proof (ppOf ch S) n r c x

lemma pending_step (r : Record (ppOf ch S)) (c : Coupling.Symbolic.CoinDomain (ppOf ch S))
    (x : ℕ → k) : Simulation.PendingStep (ppOf ch S) r c x :=
  Simulation.pending_step_proof (ppOf ch S) r c x

lemma init_bound (n : ℕ) (r : Record (ppOf ch S))
    (c : Coupling.Symbolic.CoinDomain (ppOf ch S)) (x : ℕ → k) (hr : Simulation.RMono (ppOf ch S) r)
    (hind : ∀ pad, Simulation.IndStmt (ppOf ch S) n r c x pad (A.run r.pv r.header)) :
    Pr[fun ω => Clean n ω ∧ (fullRecord ω).cut n = r ∧ ω.1.out.coins = c.val ∧
        guessValues r ω = x | observedRun (ppOf ch S) m A] ≤
      Pr[fun R => R.cut n = r | genRun (ppOf ch S) A] * Pr[= c | coinLaw (ppOf ch S)] *
        Pr[= x | guessDraw (ppOf ch S) r c] := by
  exact Init.init_bound_proof (ppOf ch S) m A n r c x hind

lemma not_mono (n : ℕ) (r : Record (ppOf ch S))
    (c : Coupling.Symbolic.CoinDomain (ppOf ch S)) (x : ℕ → k)
    (hr : ¬ Simulation.RMono (ppOf ch S) r) :
    Pr[fun ω => Clean n ω ∧ (fullRecord ω).cut n = r ∧ ω.1.out.coins = c.val ∧
        guessValues r ω = x | observedRun (ppOf ch S) m A] = 0 := by
  exact NotMono.not_mono_proof (ppOf ch S) m A n r c x hr

lemma simulation (Q QH : ℕ) (hA : InClass A Q QH) :
    ∃ gen : ProbComp (FullRecord (ppOf ch S)),
      ∀ (n : ℕ) (r : Record (ppOf ch S)) (c : Coupling.Symbolic.CoinDomain (ppOf ch S))
        (x : ℕ → k),
        Pr[fun ω => Clean n ω ∧ (fullRecord ω).cut n = r ∧ ω.1.out.coins = c.val ∧
            guessValues r ω = x | observedRun (ppOf ch S) m A] ≤
          Pr[fun R => R.cut n = r | gen] * Pr[= c | coinLaw (ppOf ch S)] *
            Pr[= x | guessDraw (ppOf ch S) r c] := by
  refine ⟨genRun (ppOf ch S) A, fun n r c x => ?_⟩
  by_cases hr : Simulation.RMono (ppOf ch S) r
  · exact init_bound ch S m A n r c x hr (fun pad =>
      Simulation.ind (ppOf ch S) n r c x pad (cons_step ch S r c x) (cover_step ch S c x)
        (count_step ch S n r c x) (pending_step ch S r c x) hr _)
  · rw [not_mono ch S m A n r c x hr]
    exact zero_le

end Core

section Slots

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind}

lemma FactorSlot.dominated (F : FactorSlot ch S i) (m : Msg P0) (A : Adversary P0)
    (gen : ProbComp (FullRecord (ppOf ch S)))
    (hsimulation : ∀ (n : ℕ) (r : Record (ppOf ch S)) (c : CoinDomain (ppOf ch S)) (x : ℕ → k),
      Pr[fun ω => Clean n ω ∧ (fullRecord ω).cut n = r ∧ ω.1.out.coins = c.val ∧
          guessValues r ω = x | observedRun (ppOf ch S) m A] ≤
        Pr[fun R => R.cut n = r | gen] * Pr[= c | coinLaw (ppOf ch S)] *
          Pr[= x | guessDraw (ppOf ch S) r c])
    (event : WorldOut P0 × ObsState (ppOf ch S) → Prop)
    (hfire : F.FiresOn event (observedRun (ppOf ch S) m A))
    (hK : F.Marginal) :
    (F.toDistribution gen).Dominated (observedRun (ppOf ch S) m A) event := by
  exact F.r1_dominated gen (observedRun (ppOf ch S) m A)
    (observedRun_valid ch S m A) hsimulation event hfire hK

lemma coinLaw_search (s : SearchSample P0) :
    (∑' c : CoinDomain (ppOf ch S),
      if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) = Pr[= s | searchLaw] := by
  exact CoinLaw.coinLaw_search s

lemma coinLaw_resample (s : SearchSample P0) (c' : CoinDomain (ppOf ch S)) :
    (∑' c : CoinDomain (ppOf ch S), if c.val.2.1 = s then
        Pr[= c | coinLaw (ppOf ch S)] * Pr[= c' | resample (ppOf ch S) c] else 0) =
      Pr[= s | searchLaw] * Pr[= c' | coinLaw (ppOf ch S)] := by
  exact CoinLaw.coinLaw_resample s c'

lemma exists_test (i : Kind) : Nonempty (Bounds ch S i) := by
  exact padding_test i

end Slots

section Final

variable (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)

lemma fold_data (hS : InShape P0 S) (Q QH : ℕ) (hA : InClass A Q QH) :
    ∃ (events : EventsOn (WorldOut P0 × ObsState (ppOf ch S)) (simBudget Q))
      (slot : (i : Kind) → Fin (quota (simBudget Q) i) → FactorSlot ch S i),
      (∀ i j ω, events i j ω → ChargedCmp (ppOf ch S) ω.1) ∧
      (∀ ω ∈ support (observedRun (ppOf ch S) m A), ChargedCmp (ppOf ch S) ω.1 →
        ∃ i j, events i j ω) ∧
      (∀ i j, (slot i j).FiresOn (events i j) (observedRun (ppOf ch S) m A)) ∧
      (∀ i j, (slot i j).HitsOn (events i j) (observedRun (ppOf ch S) m A)) ∧
      (∀ i j, (slot i j).Marginal) := by

  exact Fold.fold_data ch S m A hS Q QH hA (fun i => exists_test (ch := ch) (S := S) i)
    (fun s => coinLaw_search (ch := ch) (S := S) s)
    (fun s c' => coinLaw_resample (ch := ch) (S := S) s c')

theorem coupling_fold (hS : InShape P0 S) (Q QH : ℕ) (hA : InClass A Q QH) :
    ∃ (coupling : GenericCoupling ch S (observedRun (ppOf ch S) m A) (simBudget Q))
      (events : EventsOn (WorldOut P0 × ObsState (ppOf ch S)) (simBudget Q)),
      DeterministicFold ch S (observedRun (ppOf ch S) m A) Prod.fst (simBudget Q)
        coupling events := by
  obtain ⟨gen, hgen⟩ := simulation ch S m A Q QH hA
  obtain ⟨events, slot, hc, hcov, hfire, hhit, hK⟩ := fold_data ch S m A hS Q QH hA
  obtain ⟨coupling, hfold⟩ := fold_of_distributions ch S (simBudget Q)
    (observedRun (ppOf ch S) m A) Prod.fst events
    (fun i j => (slot i j).toDistribution gen) hc hcov
    (fun i j => (slot i j).dominated m A gen hgen (events i j) (hfire i j) (hK i j))
    (fun i j => (slot i j).hits gen _ (observedRun_valid ch S m A) (events i j) (hhit i j))
  exact ⟨coupling, events, hfold⟩

lemma charged_observed :
    Pr[ChargedCmp (ppOf ch S) | worldRun (ppOf ch S) m A] =
      Pr[fun ω => ChargedCmp (ppOf ch S) ω.1 | observedRun (ppOf ch S) m A] := by
  have h1 : Pr[ChargedCmp (ppOf ch S) | worldRun (ppOf ch S) m A] =
      Pr[ChargedCmp (ppOf ch S) | lazyRun ch S m A] := by
    rw [← probEvent_evalSPMF, ← lazy_law ch S m A, probEvent_evalSPMF]
  have h2 : Pr[ChargedCmp (ppOf ch S) | lazyRun ch S m A] =
      Pr[fun ω => ChargedCmp (ppOf ch S) ω.1 | observedRun (ppOf ch S) m A] := by
    rw [← probEvent_evalSPMF, ← observedRun_law ch S m A, probEvent_evalSPMF, probEvent_map]
    rfl
  exact h1.trans h2

end Final

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration
