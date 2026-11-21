import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy

open Classical

namespace Bounds

def Sample {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind} :
    Bounds ch S i → Type
  | .light .. => SearchSample P0
  | .field .. | .source1 .. | .source2 .. =>
      {c : Coins P0 // ValidCoins (ppOf ch S).qap c}
  | .guess .. => ℕ → k
  | .reservoir .. => Label P0
  | .kdf .. => Fin (2^126)
  | .seed .. => Fin (2^128)

def sample {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind}
    (t : Bounds ch S i) : ProbComp t.Sample :=
  match t with
  | .light .. => searchLaw
  | .field .. | .source1 .. | .source2 .. => coinLaw (ppOf ch S)
  | .guess t => reservoirDraw t.pool t.nonempty (t.nc + t.ng)
  | .reservoir pool hne .. => draw pool hne
  | .kdf .. => $ᵗ Fin (2^126)
  | .seed .. => $ᵗ Fin (2^128)

def Hit {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind}
    (t : Bounds ch S i) : t.Sample → Prop :=
  match t with
  | .light forms D ι _ =>
      fun s => IdentityAtR (ppOf ch S) (formVec forms) (rField s) D ι
  | .field forms D ι r _ =>
      fun c => valT (ppOf ch S) (formVec forms) ⟨c.val,r⟩ D =
        ι * kappa (ppOf ch S) c.val
  | .source1 E F r _ =>
      fun c => val1 (ppOf ch S) ⟨c.val,r⟩ E = val1 (ppOf ch S) ⟨c.val,r⟩ F
  | .source2 forms E F r _ =>
      fun c => val2 (ppOf ch S) (formVec forms) ⟨c.val,r⟩ E =
        val2 (ppOf ch S) (formVec forms) ⟨c.val,r⟩ F
  | .guess t => fun x => MvPolynomial.eval x t.polynomial = 0
  | .reservoir _ _ _ target => fun x => x = target
  | .kdf target => fun x => x = target
  | .seed target => fun x => x = target

lemma hit_probability {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind}
    (t : Bounds ch S i) :
    Pr[t.Hit | t.sample] = Pr[fun b => b = true | t.run] := by
  cases t <;> simp only [sample, run, GuessTest.run, probEvent_map,
    Function.comp_def, decide_eq_true_eq, Hit] <;> rfl

end Bounds

structure SlotPreparation (ch : AdmissibleChoice P0) (S : Relation P0) (i : Kind) where
  Context : Type
  prepare : ProbComp Context
  test : Context → Bounds ch S i

namespace SlotPreparation

variable {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind}

abbrev Trial (p : SlotPreparation ch S i) := (a : p.Context) × (p.test a).Sample

def trials (p : SlotPreparation ch S i) : ProbComp p.Trial := do
  let a ← p.prepare
  let x ← (p.test a).sample
  pure ⟨a, x⟩

def tests (p : SlotPreparation ch S i) : ProbComp (Bounds ch S i) :=
  p.test <$> p.prepare

def Hit (p : SlotPreparation ch S i) (t : p.Trial) : Prop :=
  (p.test t.1).Hit t.2

lemma hit_probability (p : SlotPreparation ch S i) :
    Pr[p.Hit | p.trials] = Pr[fun b => b = true | p.tests >>= Bounds.run] := by
  simp only [trials, tests, bind_map_left]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro a
  congr 1
  have hm := map_eq_bind_pure_comp ProbComp
    (fun x : (p.test a).Sample => (⟨a, x⟩ : p.Trial)) (p.test a).sample
  simp only [Function.comp_def] at hm
  rw [← hm, probEvent_map]
  exact Bounds.hit_probability (p.test a)

end SlotPreparation

structure SlotCoupling (ch : AdmissibleChoice P0) (S : Relation P0) {Ω : Type}
    (world : ProbComp Ω) (i : Kind) where
  preparation : SlotPreparation ch S i
  joint : ProbComp (Ω × preparation.Trial)
  world_law : evalSPMF (Prod.fst <$> joint) = evalSPMF world
  trial_law : evalSPMF (Prod.snd <$> joint) = evalSPMF preparation.trials

namespace SlotCoupling

variable {ch : AdmissibleChoice P0} {S : Relation P0} {Ω : Type}
  {world : ProbComp Ω} {i : Kind}

lemma dominates (c : SlotCoupling ch S world i) (event : Ω → Prop)
    (h : ∀ z ∈ support c.joint, event z.1 → c.preparation.Hit z.2) :
    Pr[event | world] ≤
      Pr[fun b => b = true | c.preparation.tests >>= Bounds.run] := by
  have hw : Pr[event | world] = Pr[fun z => event z.1 | c.joint] := by
    rw [← probEvent_evalSPMF, ← c.world_law, probEvent_evalSPMF, probEvent_map]
    rfl
  have ht : Pr[fun z => c.preparation.Hit z.2 | c.joint] =
      Pr[c.preparation.Hit | c.preparation.trials] := by
    have he := congrArg (fun d => Pr[c.preparation.Hit | d]) c.trial_law
    simpa only [probEvent_evalSPMF, probEvent_map, Function.comp_def] using he
  calc
    _ = Pr[fun z => event z.1 | c.joint] := hw
    _ ≤ Pr[fun z => c.preparation.Hit z.2 | c.joint] := probEvent_mono h
    _ = Pr[c.preparation.Hit | c.preparation.trials] := ht
    _ = _ := c.preparation.hit_probability

end SlotCoupling

abbrev GenericCoupling (ch : AdmissibleChoice P0) (S : Relation P0) {Ω : Type}
    (world : ProbComp Ω) (w : ℕ) :=
  (i : Kind) → Fin (quota w i) → SlotCoupling ch S world i

def DeterministicFold (ch : AdmissibleChoice P0) (S : Relation P0) {Ω : Type}
    (world : ProbComp Ω) (π : Ω → WorldOut P0) (w : ℕ)
    (coupling : GenericCoupling ch S world w) (events : EventsOn Ω w) : Prop :=
  (∀ (i : Kind) (j : Fin (quota w i)) (ω : Ω),
    events i j ω → ChargedCmp (ppOf ch S) (π ω)) ∧
  (∀ ω ∈ support world, ChargedCmp (ppOf ch S) (π ω) → ∃ i j, events i j ω) ∧
  (∀ (i : Kind) (j : Fin (quota w i))
    (z : Ω × (coupling i j).preparation.Trial),
    z ∈ support (coupling i j).joint →
    events i j z.1 → (coupling i j).preparation.Hit z.2)

lemma stopped_exposure_of_coupling_fold
    (ch : AdmissibleChoice P0) (S : Relation P0) {Ω : Type}
    (world : ProbComp Ω) (π : Ω → WorldOut P0)
    (w : ℕ) (coupling : GenericCoupling ch S world w)
    (events : EventsOn Ω w)
    (fold : DeterministicFold ch S world π w coupling events) :
    ∃ (events : EventsOn Ω w)
      (tests : (i : Kind) → Fin (quota w i) → ProbComp (Bounds ch S i)),
      (∀ i j ω, events i j ω → ChargedCmp (ppOf ch S) (π ω)) ∧
      (∀ ω ∈ support world, ChargedCmp (ppOf ch S) (π ω) →
        ∃ i j, events i j ω) ∧
      (∀ i j, Pr[events i j | world] ≤
        Pr[fun b => b = true | tests i j >>= Bounds.run]) := by
  refine ⟨events, fun i j => (coupling i j).preparation.tests,
    fold.1, fold.2.1, ?_⟩
  intro i j
  exact (coupling i j).dominates (events i j) (fold.2.2 i j)

end Praxis.Proofs.GroupModel.Split.Lazy
