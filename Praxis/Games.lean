import Praxis.ExtractorCounted
import Praxis.Algebra.Definitions.Games
import Praxis.Constants
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis

open OracleComp OracleSpec GroupModel.Sorted

open Praxis.Algebra (Vec Sat)

variable (P : Params)

abbrev LabelEncoding : Type := PSort → (ZMod P.q ↪ Label P)

inductive GQuery

  | lin (s : PSort) (a b : Fq P) (u v : Label P)

  | pair (u v : Label P)

  | name (v : Label P)

variable {P}

@[reducible] def GQuery.Result : GQuery P → Type
  | .lin .. => Option (Label P)
  | .pair .. => Option (Label P)
  | .name .. => Option (ClassName P)

@[reducible] def GQuery.Answer : GQuery P → Type
  | .lin .. => Option (Label P)
  | .pair .. => Option (Label P)
  | .name .. => Option NameRef

variable (P)

@[reducible] def groupModel : OracleSpec (GQuery P) := GQuery.Answer

@[reducible] def hfModel : OracleSpec (Seed P × FormIndex P) := fun _ => Rq P

@[reducible] def kdfModel : OracleSpec (KdfQuery P) := fun _ => Option (Msg P)

@[reducible] def AdvModel := unifSpec + groupModel P + hfModel P + kdfModel P

variable {P}

noncomputable def groupAnswer (σ : LabelEncoding P) (issued : Finset (Label P)) :
    (qr : GQuery P) → qr.Result
  | .lin s a b u v => (do
      let x ← Algebra.decodeLabel (σ s) u
      let y ← Algebra.decodeLabel (σ s) v
      pure (σ s (a * x + b * y)) : Option (Label P))
  | .pair u v => (do
      let x ← Algebra.decodeLabel (σ .g₁) u
      let y ← Algebra.decodeLabel (σ .g₂) v
      pure (σ .gₜ (x * y)) : Option (Label P))
  | .name v => (if v ∈ issued then do
      let x ← Algebra.decodeLabel (σ .gₜ) v
      pure (labelName (σ .gₜ) x) else none : Option (ClassName P))

def trEntry : (qr : GQuery P) → qr.Result → Option (TrOp P)
  | .lin s a b u v, r => (r : Option (Label P)).map (TrOp.lin s a b u v)
  | .pair u v, r => (r : Option (Label P)).map (TrOp.pair u v)
  | .name v, r => (r : Option (ClassName P)).map (TrOp.name v)

def TrOp.issuedGT : TrOp P → Option (Label P)
  | .lin .gₜ _ _ _ _ res => some res
  | .pair _ _ res => some res
  | _ => none

variable (P)

structure OracleState where
  hf : Seed P × FormIndex P → Option (Rq P)
  kdf : ClassName P → Option (Msg P)
  tr : List (TrOp P)
  kdfLog : List (ℕ × ClassName P)
  issuedT : Finset (Label P)
  names : List (ClassName P)

abbrev GameM : Type → Type := StateT (OracleState P) ProbComp

variable {P}

def OracleState.empty : OracleState P := ⟨fun _ => none, fun _ => none, [], [], ∅, []⟩

def OracleState.programHF (st : OracleState P) (seed : Seed P) (A : FormMatrix P) :
    OracleState P :=
  { st with hf := fun i => if i.1 = seed then some (A i.2) else st.hf i }

noncomputable def hfLazy [NeZero P.q] (i : Seed P × FormIndex P) : GameM P (Rq P) := do
  match (← get).hf i with
  | some a => pure a
  | none =>
    let a ← (StateT.lift ($ᵗ (Rq P)) : GameM P (Rq P))
    modify fun st => { st with hf := Function.update st.hf i (some a) }
    pure a

noncomputable def kdfLazy (nm : ClassName P) : GameM P (Msg P) := do
  match (← get).kdf nm with
  | some y => pure y
  | none =>
    let y ← (StateT.lift ($ᵗ (Msg P)) : GameM P (Msg P))
    modify fun st => { st with kdf := Function.update st.kdf nm (some y) }
    pure y

def nameRef (nm : ClassName P) : GameM P NameRef := do
  let st ← get
  match st.names.findIdx? (· == nm) with
  | some k => pure k
  | none => do
    set { st with names := st.names ++ [nm] }
    pure st.names.length

def handOut : (qr : GQuery P) → qr.Result → GameM P qr.Answer
  | .lin .., r => pure r
  | .pair .., r => pure r
  | .name _, r => match r with
    | none => pure none
    | some nm => some <$> nameRef nm

noncomputable def groupImpl (σ : LabelEncoding P) : QueryImpl (groupModel P) (GameM P) :=
  fun qr => do
    let r := groupAnswer σ (← get).issuedT qr
    match trEntry qr r with
    | some e => modify fun st =>
        { st with
          tr := st.tr ++ [e]
          issuedT := match e.issuedGT with
            | some l => insert l st.issuedT
            | none => st.issuedT }
    | none => pure ()
    handOut qr r

noncomputable def kdfImpl (qk : KdfQuery P) : GameM P (Option (Msg P)) := do
  let st ← get
  let nm? : Option (ClassName P) := match qk with
    | .ref k => st.names[k]?
    | .guess nm => some nm
  match nm? with
  | none => pure none
  | some nm => do
    modify fun st => { st with kdfLog := st.kdfLog ++ [(st.tr.length, nm)] }
    some <$> kdfLazy nm

noncomputable def gameImpl [NeZero P.q] (σ : LabelEncoding P) :
    QueryImpl (AdvModel P) (GameM P) :=
  (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (GameM P) + groupImpl σ) +
    (fun i => hfLazy i : QueryImpl (hfModel P) (GameM P))) +
    (fun qk => kdfImpl qk : QueryImpl (kdfModel P) (GameM P))

variable (P)

structure Adversary where
  run : PubView P → Header P → OracleComp (AdvModel P) Bool

variable {P}

def isGroupQuery : (AdvModel P).Domain → Bool
  | .inl (.inl (.inr _)) => true
  | _ => false

def isHFQuery : (AdvModel P).Domain → Bool
  | .inl (.inr _) => true
  | _ => false

def isKDFQuery : (AdvModel P).Domain → Bool
  | .inr _ => true
  | _ => false

inductive CallKind
  | group | hf | kdf
  deriving DecidableEq

def callCost (i : (AdvModel P).Domain) : QueryCount CallKind
  | .group => if isGroupQuery i then 1 else 0
  | .hf => if isHFQuery i then 1 else 0
  | .kdf => if isKDFQuery i then 1 else 0

def simBudget (Q : ℕ) : ℕ := 2 * Q + Constants.LT

variable (P)

def formIndexList : List (FormIndex P) :=
  (List.finRange P.rows).flatMap fun ρ =>
    (none :: (List.finRange P.cols).map some).map fun j => (ρ, j)

variable {P}

noncomputable def pubView [Fact (Nat.Prime P.q)] (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Vec (Fq P) P.N) (c : Coins P) : PubView P where
  g1 := (none, σ .g₁ 1) :: (g1Order P).map fun i => (some i, σ .g₁ (g1Exp pp c i))
  g2 := (none, σ .g₂ 1) :: (g2Order P).map fun i => (some i, σ .g₂ (g2Exp pp v c i))
  gT := [(none, σ .gₜ 1), (some (), σ .gₜ (gtExp pp c))]

structure EncOut (P : Params) where
  pv : PubView P
  header : Header P
  forms : FormMatrix P
  coins : Coins P

noncomputable def encAt [Fact (Nat.Prime P.q)] (σ : LabelEncoding P) (pp : PublicParams P)
    (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}] (seed : Seed P) :
    GameM P (EncOut P) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  do
    let entries ← (formIndexList P).mapM fun i => do
      let a ← hfLazy (seed, i)
      pure (i, a)
    let A : FormMatrix P := fun i =>
      ((entries.find? fun e => decide (e.1 = i)).map Prod.snd).getD 0
    let c ← (StateT.lift ($ᵗ {c : Coins P // ValidCoins pp.qap c}) : GameM P _)
    let pad ← kdfLazy (labelName (σ .gₜ) (kappa pp c.1))
    let pv := pubView σ pp (formVec A) c.1

    modify fun st => { st with issuedT := st.issuedT ∪ (pv.gT.map Prod.snd).toFinset }
    pure ⟨pv, ⟨seed, m ^^^ pad⟩, A, c.1⟩

noncomputable def encGame [Fact (Nat.Prime P.q)] (σ : LabelEncoding P) (pp : PublicParams P)
    (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}] : GameM P (EncOut P) := do
  let seed ← (StateT.lift ($ᵗ (Seed P)) : GameM P (Seed P))
  encAt σ pp m seed

noncomputable def countedRun [Fact (Nat.Prime P.q)] (σ : LabelEncoding P) (A : Adversary P)
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) :
    ProbComp ((EncOut P × Bool × QueryCount CallKind) × OracleState P) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  (do
    let e ← encGame σ pp m
    let oc ← (simulateQ ((gameImpl σ).withCost callCost) (A.run e.pv e.header)).run
    pure (e, oc)).run OracleState.empty

def MaxCalls [Fact (Nat.Prime P.q)] (A : Adversary P) (c : CallKind) (k : ℕ) : Prop :=
  ∀ (σ : LabelEncoding P) (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P), ∀ z ∈ support (countedRun σ A pp m), z.1.2.2 c ≤ k

structure InClass [Fact (Nat.Prime P.q)] (A : Adversary P) (Q QH : ℕ) : Prop where
  group : MaxCalls A .group Q
  hf : MaxCalls A .hf QH
  kdf : MaxCalls A .kdf QH
  Q_lt : Q < Constants.T
  QH_le : QH ≤ Constants.T

theorem encoding_nonempty [NeZero P.q] (h : P.q ≤ 2 ^ P.labelBits) :
    Nonempty (ZMod P.q ↪ Label P) :=
  ⟨⟨_, Algebra.ofNat_val_injective h⟩⟩

noncomputable def sampleEncoding [NeZero P.q] [Nonempty (ZMod P.q ↪ Label P)] :
    ProbComp (LabelEncoding P) := do
  let σ1 ← $ᵗ (ZMod P.q ↪ Label P)
  let σ2 ← $ᵗ (ZMod P.q ↪ Label P)
  let σT ← $ᵗ (ZMod P.q ↪ Label P)
  pure fun
    | .g₁ => σ1
    | .g₂ => σ2
    | .gₜ => σT

noncomputable def runWith [Fact (Nat.Prime P.q)] (σ : LabelEncoding P) (A : Adversary P)
    (enc : GameM P (EncOut P)) (st0 : OracleState P) :
    ProbComp ((EncOut P × Bool) × OracleState P) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  (do
    let e ← enc
    let o ← simulateQ (gameImpl σ) (A.run e.pv e.header)
    pure (e, o)).run st0

def extractWin [Fact (Nat.Prime P.q)] (S : Relation P) (b o : Bool) :
    Option (Vec (Fq P) P.N) → Bool
  | none => o == b
  | some x => (o == b) && !decide (Sat S x)

abbrev ExtractorLaw (P : Params) : Type :=
  Relation P → PubView P → List (TrOp P) → ProbComp (Option (Vec (Fq P) P.N))

noncomputable def extractGame [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m0 m1 : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (ext : ExtractorLaw P) : ProbComp Bool :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  do
    let b ← $ᵗ Bool
    let σ ← sampleEncoding
    let m := if b then m1 else m0
    let out ← runWith σ A (encGame σ pp m) OracleState.empty
    let x ← ext pp.S out.1.1.pv out.2.tr
    pure (extractWin pp.S b out.1.2 x)

variable (P)

structure RedView where
  pp : PublicParams P
  msg : Msg P
  enc : LabelEncoding P
  out : EncOut P
  state : OracleState P

variable {P}

noncomputable def blackBoxRun {α : Type} [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (post : RedView P → ProbComp α) (forms : FormMatrix P) : ProbComp α :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  do
    let σ ← sampleEncoding
    let seed ← $ᵗ (Seed P)
    let out ← runWith σ A (encAt σ pp m seed) (OracleState.empty.programHF seed forms)
    post ⟨pp, m, σ, out.1.1, out.2⟩

end Praxis
