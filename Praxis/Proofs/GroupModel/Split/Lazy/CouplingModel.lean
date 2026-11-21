import Praxis.Proofs.GroupModel.Split.Lazy.Domination
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Relation
import Praxis.Search
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration

open Classical

section SlotDistributions

variable {ch : AdmissibleChoice P0} {S : Relation P0} {Ω : Type} {i : Kind}

structure SlotDistribution (ch : AdmissibleChoice P0) (S : Relation P0) (Ω : Type) (i : Kind) where
  preparation : SlotPreparation ch S i
  extract : Ω → ProbComp preparation.Trial

namespace SlotDistribution

def Dominated (p : SlotDistribution ch S Ω i) (obs : ProbComp Ω) (event : Ω → Prop) : Prop :=
  ∀ t, (∑' ω, Pr[= ω | obs] * (if event ω then Pr[= t | p.extract ω] else 0)) ≤
    Pr[= t | p.preparation.trials]

def Hits (p : SlotDistribution ch S Ω i) (obs : ProbComp Ω) (event : Ω → Prop) : Prop :=
  ∀ ω ∈ support obs, event ω → ∀ t ∈ support (p.extract ω), p.preparation.Hit t

end SlotDistribution

end SlotDistributions

section World

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

abbrev Entry : Type := (q : (AdvModel P0).Domain) × (AdvModel P0).Range q

structure Step (pp : PublicParams P0) where
  entry : Entry
  shadow : State pp
  order : List GuessVar

structure ObsState (pp : PublicParams P0) where
  oracle : OracleState P0
  shadow : State pp
  order : List GuessVar
  steps : List (Step pp)
  stop : Option ℕ

def newGuesses (pp : PublicParams P0) (before after : State pp) :
    GQuery P0 → List GuessVar
  | .lin s _ _ u v =>
      ([(s, u), (s, v)].filter fun g => g ∈ after.guesses ∧ g ∉ before.guesses).dedup
  | .pair u v =>
      [((.g₁ : GroupModel.Sorted.PSort), u), ((.g₂ : GroupModel.Sorted.PSort), v)].filter
        fun g => g ∈ after.guesses ∧ g ∉ before.guesses
  | .name _ => []

def KdfTarget (pp : PublicParams P0) (σ : LabelEncoding P0) (c : Coins P0)
    (st : OracleState P0) (kq : KdfQuery P0) : Prop :=
  (match kq with
    | .ref k => st.names[k]?
    | .guess nm => some nm) = some (labelName (σ .gₜ) (kappa pp c))

def obsHandler (pp : PublicParams P0) (σ : LabelEncoding P0) (c : Coins P0) :
    QueryImpl (AdvModel P0) (StateT (ObsState pp) ProbComp) :=
  fun q => StateT.mk fun st =>
    let shadow : State pp := match q with
      | .inl (.inl (.inr gq)) =>
          observeGroup pp σ st.shadow gq (groupAnswer σ st.oracle.issuedT gq)
      | _ => st.shadow
    let order : List GuessVar := match q with
      | .inl (.inl (.inr gq)) => st.order ++ newGuesses pp st.shadow shadow gq
      | _ => st.order
    let bad : Prop := shadow.first.isSome ∨ (match q with
      | .inr kq => KdfTarget pp σ c st.oracle kq
      | _ => False)
    (fun z => (z.1, (⟨z.2, shadow, order, st.steps ++ [⟨⟨q, z.1⟩, shadow, order⟩],
      st.stop.orElse fun _ => if bad then some st.steps.length else none⟩ : ObsState pp))) <$>
      (gameImpl σ q).run st.oracle

def observedRun (pp : PublicParams P0) [Nonempty {c : Coins P0 // ValidCoins pp.qap c}]
    (m : Msg P0) (A : Adversary P0) : ProbComp (WorldOut P0 × ObsState pp) := do
  let σ ← sampleEncoding
  let e ← (encGame σ pp m).run OracleState.empty
  let st : ObsState pp := ⟨e.2, initialise pp e.1.forms e.1.pv, [], [], none⟩
  let z ← (simulateQ (obsHandler pp σ e.1.coins) (A.run e.1.pv e.1.header)).run st
  pure (⟨σ, e.1, z.1, z.2.oracle⟩, z.2)

structure FullRecord (pp : PublicParams P0) where
  header : Header P0
  forms : FormMatrix P0
  pv : PubView P0
  steps : List (Step pp)

structure Record (pp : PublicParams P0) where
  header : Header P0
  forms : FormMatrix P0
  pv : PubView P0
  steps : List (Step pp)
  pending : Option (AdvModel P0).Domain
  pendingOrder : Option (List GuessVar)

def FullRecord.cut {pp : PublicParams P0} (R : FullRecord pp) (n : ℕ) : Record pp :=
  ⟨R.header, R.forms, R.pv, R.steps.take n, (R.steps[n]?).map fun s => s.entry.1,
    (R.steps[n]?).map Step.order⟩

def fullRecord {pp : PublicParams P0} (ω : WorldOut P0 × ObsState pp) : FullRecord pp :=
  ⟨ω.1.out.header, ω.1.out.forms, ω.1.out.pv, ω.2.steps⟩

def Clean {pp : PublicParams P0} (n : ℕ) (ω : WorldOut P0 × ObsState pp) : Prop :=
  (initialise pp ω.1.out.forms ω.1.out.pv).first = none ∧
    ∀ b, ω.2.stop = some b → n ≤ b

def Record.shadow {pp : PublicParams P0} (r : Record pp) : State pp :=
  ((r.steps.getLast?).map Step.shadow).getD (initialise pp r.forms r.pv)

def Record.lastOrder {pp : PublicParams P0} (r : Record pp) : List GuessVar :=
  ((r.steps.getLast?).map Step.order).getD []

def Record.order {pp : PublicParams P0} (r : Record pp) : List GuessVar :=
  r.pendingOrder.getD r.lastOrder

def Record.pendingShadow {pp : PublicParams P0} (r : Record pp) : State pp :=
  { r.shadow with dict := fun s l => match r.shadow.dict s l with
      | some P => some P
      | none => if (s, l) ∈ r.order then some (MvPolynomial.X (s, l)) else none }

def valueAt (pp : PublicParams P0) (order : List GuessVar) (c : CoinDomain pp)
    (x : ℕ → k) : Poly pp →+* k :=
  MvPolynomial.eval₂Hom (atCoin pp c) (fun v => x (order.idxOf v))

def Record.sortAt {pp : PublicParams P0} (r : Record pp) (t : ℕ) : GroupModel.Sorted.PSort :=
  ((r.order[t]?).map Prod.fst).getD .g₁

def Record.guessShadow {pp : PublicParams P0} (r : Record pp) (t : ℕ) : State pp :=
  ((r.steps.find? fun s => decide (t < s.order.length)).map Step.shadow).getD
    r.pendingShadow

def usedBefore (pp : PublicParams P0) (r : Record pp) (c : CoinDomain pp) (t : ℕ)
    (x : ℕ → k) : Finset k :=
  Finset.univ.filter fun a => ∃ l P, (r.guessShadow t).dict (r.sortAt t) l = some P ∧
    (∀ v ∈ P.vars, r.order.idxOf v < t) ∧ valueAt pp r.order c x P = a

def guessPool (pp : PublicParams P0) (r : Record pp) (c : CoinDomain pp)
    (t : ℕ) (x : ℕ → k) : Finset k :=
  if (Finset.univ \ usedBefore pp r c t x).Nonempty then
    Finset.univ \ usedBefore pp r c t x else Finset.univ

lemma guessPool_nonempty (pp : PublicParams P0) (r : Record pp) (c : CoinDomain pp)
    (t : ℕ) (x : ℕ → k) : (guessPool pp r c t x).Nonempty := by
  unfold guessPool
  split_ifs with h
  · exact h
  · exact Finset.univ_nonempty

def guessDraw (pp : PublicParams P0) (r : Record pp) (c : CoinDomain pp) :
    ProbComp (ℕ → k) :=
  reservoirDraw (guessPool pp r c) (guessPool_nonempty pp r c) r.order.length

def guessValues {pp : PublicParams P0} (r : Record pp) (ω : WorldOut P0 × ObsState pp) :
    ℕ → k :=
  fun t => match r.order[t]? with
    | some v => (Algebra.decodeLabel (ω.1.enc v.1) v.2).getD 0
    | none => 0

structure GenState (pp : PublicParams P0) where
  oracle : OracleState P0
  shadow : State pp
  order : List GuessVar
  steps : List (Step pp)

def genHandler (pp : PublicParams P0) :
    QueryImpl (AdvModel P0) (StateT (GenState pp) ProbComp) := fun q =>
  match q with
  | .inl (.inl (.inr gq)) => StateT.mk fun st => do
      let z ← (referenceGroup pp st.oracle.issuedT gq).run st.shadow
      let w ← (finishGroup gq z.1).run st.oracle
      let order := st.order ++ newGuesses pp st.shadow z.2 gq
      pure (w.1, (⟨w.2, z.2, order, st.steps ++ [⟨⟨.inl (.inl (.inr gq)), w.1⟩, z.2, order⟩]⟩ :
        GenState pp))
  | q => StateT.mk fun st =>
      (fun w => (w.1, (⟨w.2, st.shadow, st.order,
        st.steps ++ [⟨⟨q, w.1⟩, st.shadow, st.order⟩]⟩ : GenState pp))) <$>
        (gameImpl (Classical.arbitrary (LabelEncoding P0)) q).run st.oracle

def genRun (pp : PublicParams P0) (A : Adversary P0) : ProbComp (FullRecord pp) := do
  let seed ← ($ᵗ (Seed P0) : ProbComp (Seed P0))
  let ent ← ((formIndexList P0).mapM fun i => do
    let a ← hfLazy (seed, i)
    pure (i, a)).run OracleState.empty
  let forms : FormMatrix P0 := fun i =>
    ((ent.1.find? fun e => decide (e.1 = i)).map Prod.snd).getD 0
  let cm ← ($ᵗ (Msg P0) : ProbComp (Msg P0))
  let z ← (referenceInitial pp forms).run (empty pp)
  let st : GenState pp :=
    ⟨{ent.2 with issuedT := (z.1.gT.map Prod.snd).toFinset}, z.2, [], []⟩
  let out ← (simulateQ (genHandler pp) (A.run z.1 ⟨seed, cm⟩)).run st
  pure ⟨⟨seed, cm⟩, forms, z.1, out.2.steps⟩

def resample (pp : PublicParams P0) (c : CoinDomain pp) : ProbComp (CoinDomain pp) :=
  (fun s' => (⟨(c.val.1, s', c.val.2.2), c.property⟩ : CoinDomain pp)) <$> searchLaw

end World

section Slots

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind}

structure FactorSlot (ch : AdmissibleChoice P0) (S : Relation P0) (i : Kind) where
  Context : Type
  test : Context → Bounds ch S i
  pad : Context
  fires : Record (ppOf ch S) → Option (SearchSample P0 → Context)
  draw : (a : Context) → CoinDomain (ppOf ch S) → (ℕ → k) → ProbComp (test a).Sample

namespace FactorSlot

variable (F : FactorSlot ch S i)

def firstFire (R : FullRecord (ppOf ch S)) : Option ℕ :=
  if h : ∃ n, (F.fires (R.cut n)).isSome then some (Nat.find h) else none

def contextOf (R : FullRecord (ppOf ch S)) (s : SearchSample P0) : F.Context :=
  match F.firstFire R with
  | some n => match F.fires (R.cut n) with
    | some f => f s
    | none => F.pad
  | none => F.pad

def valuesOf (ω : WorldOut P0 × ObsState (ppOf ch S)) : ℕ → k :=
  match F.firstFire (fullRecord ω) with
  | some n => guessValues ((fullRecord ω).cut n) ω
  | none => fun _ => 0

def preparation (gen : ProbComp (FullRecord (ppOf ch S))) : SlotPreparation ch S i where
  Context := F.Context
  prepare := do
    let R ← gen
    let s ← searchLaw
    pure (F.contextOf R s)
  test := F.test

def extract (gen : ProbComp (FullRecord (ppOf ch S)))
    (ω : WorldOut P0 × ObsState (ppOf ch S)) : ProbComp (F.preparation gen).Trial :=
  @dite _ (ValidCoins (ppOf ch S).qap ω.1.out.coins) (Classical.propDecidable _)
    (fun h => (fun y => ⟨F.contextOf (fullRecord ω) ω.1.out.coins.2.1, y⟩) <$>
      F.draw (F.contextOf (fullRecord ω) ω.1.out.coins.2.1) ⟨ω.1.out.coins, h⟩ (F.valuesOf ω))
    (fun _ => (fun y => ⟨F.contextOf (fullRecord ω) ω.1.out.coins.2.1, y⟩) <$>
      (F.test (F.contextOf (fullRecord ω) ω.1.out.coins.2.1)).sample)

def toDistribution (gen : ProbComp (FullRecord (ppOf ch S))) :
    SlotDistribution ch S (WorldOut P0 × ObsState (ppOf ch S)) i :=
  ⟨F.preparation gen, F.extract gen⟩

def Marginal : Prop :=
  ∀ (r : Record (ppOf ch S)) (f : SearchSample P0 → F.Context), F.fires r = some f →
    ∀ (a : F.Context) (y : (F.test a).Sample),
      (∑' s, if f s = a then (∑' c : CoinDomain (ppOf ch S),
          (if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) *
          ∑' x, Pr[= x | guessDraw (ppOf ch S) r c] * Pr[= y | F.draw a c x]) else 0) ≤
        (∑' s, if f s = a then Pr[= s | searchLaw] else 0) * Pr[= y | (F.test a).sample]

def FiresOn (event : WorldOut P0 × ObsState (ppOf ch S) → Prop)
    (obs : ProbComp (WorldOut P0 × ObsState (ppOf ch S))) : Prop :=
  ∀ ω ∈ support obs, event ω → ∃ n, F.firstFire (fullRecord ω) = some n ∧ Clean n ω

def HitsOn (event : WorldOut P0 × ObsState (ppOf ch S) → Prop)
    (obs : ProbComp (WorldOut P0 × ObsState (ppOf ch S))) : Prop :=
  ∀ ω ∈ support obs, event ω → ∀ h : ValidCoins (ppOf ch S).qap ω.1.out.coins,
    ∀ y ∈ support (F.draw (F.contextOf (fullRecord ω) ω.1.out.coins.2.1)
      ⟨ω.1.out.coins, h⟩ (F.valuesOf ω)),
    (F.test (F.contextOf (fullRecord ω) ω.1.out.coins.2.1)).Hit y

set_option maxRecDepth 200000 in

lemma hits (gen : ProbComp (FullRecord (ppOf ch S)))
    (obs : ProbComp (WorldOut P0 × ObsState (ppOf ch S)))
    (hvalid : ∀ ω ∈ support obs, ValidCoins (ppOf ch S).qap ω.1.out.coins)
    (event : WorldOut P0 × ObsState (ppOf ch S) → Prop) (hhit : F.HitsOn event obs) :
    (F.toDistribution gen).Hits obs event := by
  unfold SlotDistribution.Hits
  intro ω hω he t ht
  have ht' : t ∈ support (F.extract gen ω) := ht
  have hv : ValidCoins (ppOf ch S).qap ω.1.out.coins := by
    clear ht ht' hhit he
    exact hvalid ω hω
  have hx : F.extract gen ω =
      (fun y => ⟨F.contextOf (fullRecord ω) ω.1.out.coins.2.1, y⟩) <$>
        F.draw (F.contextOf (fullRecord ω) ω.1.out.coins.2.1) ⟨ω.1.out.coins, hv⟩
          (F.valuesOf ω) := by
    unfold extract
    rw [dif_pos hv]
    rfl
  rw [hx, support_map] at ht'
  obtain ⟨y, hy, rfl⟩ := ht'
  exact hhit ω hω he hv y hy

end FactorSlot

def FactorSlot.idle (C : Type) (t : C → Bounds ch S i) (pad : C) : FactorSlot ch S i where
  Context := C
  test := t
  pad := pad
  fires := fun _ => none
  draw := fun a _ _ => (t a).sample

lemma FactorSlot.idle_marginal (C : Type) (t : C → Bounds ch S i) (pad : C) :
    (FactorSlot.idle C t pad).Marginal := by
  intro r f hf
  simp [FactorSlot.idle] at hf

lemma FactorSlot.idle_firesOn (C : Type) (t : C → Bounds ch S i) (pad : C)
    (obs : ProbComp (WorldOut P0 × ObsState (ppOf ch S))) :
    (FactorSlot.idle C t pad).FiresOn (fun _ => False) obs := by
  intro ω _ h
  exact h.elim

lemma FactorSlot.idle_hitsOn (C : Type) (t : C → Bounds ch S i) (pad : C)
    (obs : ProbComp (WorldOut P0 × ObsState (ppOf ch S))) :
    (FactorSlot.idle C t pad).HitsOn (fun _ => False) obs := by
  intro ω _ h
  exact h.elim

end Slots

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration
