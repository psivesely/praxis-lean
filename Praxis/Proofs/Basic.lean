import Praxis.Scheme
import Praxis.Ledger
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Forms
import Praxis.Games
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Units
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs

open OracleComp OracleSpec GroupModel.Sorted

open Praxis.Algebra (Vec Mat dot)

abbrev P0 : Params := Params.main

noncomputable def ppOf (ch : AdmissibleChoice Params.main) (S : Relation Params.main) :
    PublicParams Params.main :=
  setup (domainMap ch) S

instance ppOf_coins (ch : AdmissibleChoice Params.main) (S : Relation Params.main) :
    Nonempty {c : Coins Params.main // ValidCoins (ppOf ch S).qap c} :=
  main_validCoins_nonempty _

noncomputable def extF : ExtractorLaw Params.main :=
  fun S pub tr => runUnits (extractorC (sparseOf S) pub tr)

abbrev dimMax : ℕ := 3

abbrev lightRank : ℕ := 4

instance main_neZero : NeZero Params.main.q := ⟨main_prime.out.ne_zero⟩

instance main_K1_neZero : NeZero Params.main.K1 := ⟨by decide⟩

instance main_K2_neZero : NeZero Params.main.K2 := ⟨by decide⟩

theorem main_g_pos : 0 < Params.main.g := by decide

instance main_search_nonempty : Nonempty (SearchSample Params.main) :=
  ⟨(⟨0, main_g_pos⟩, fun _ => ⟨0, main_g_pos⟩)⟩

noncomputable def coinLaw (pp : PublicParams Params.main)
    [Nonempty {c : Coins Params.main // ValidCoins pp.qap c}] :
    ProbComp {c : Coins Params.main // ValidCoins pp.qap c} :=
  letI := SampleableType.ofFintype {c : Coins Params.main // ValidCoins pp.qap c}
  $ᵗ _

noncomputable def searchLaw : ProbComp (SearchSample Params.main) :=
  letI := SampleableType.ofFintype (SearchSample Params.main)
  $ᵗ _

noncomputable def sketchLaw : ProbComp (Sketches Params.main) :=
  letI := SampleableType.ofFintype (Sketches Params.main)
  $ᵗ _

section Spaces

variable {P : Params}

def jointSpace (W : Stack P) : Submodule (Fq P) (Vec (Fq P) P.N) :=
  ⨆ c, LinearMap.range (W c).mulVecLin

def zLin (v : Fin P.n → Vec (Fq P) P.N) : Vec (Fq P) P.N →ₗ[Fq P] (Fin P.n → Fq P) :=
  (Matrix.of fun e i => v e i).mulVecLin

end Spaces

section Runs

variable {P : Params}

variable (P) in

structure WorldOut where

  enc : LabelEncoding P

  out : EncOut P

  o : Bool

  st : OracleState P

noncomputable def worldRun [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) : ProbComp (WorldOut P) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  do
    let σ ← sampleEncoding
    let r ← runWith σ A (encGame σ pp m) OracleState.empty
    pure ⟨σ, r.1.1, r.1.2, r.2⟩

variable (P) in

structure FullOut where
  w : WorldOut P

  wp : Assign P

  w0 : Fin 3 → Assign P
  w1 : Fin 3 → Assign P

  x : Option (Vec (Fq P) P.N)

def recAssign (w0 w1 : Fin 3 → Assign P) : Fin 3 → Sector → Assign P :=
  fun l σ => match σ with
    | .plain => w0 l
    | .alpha => w1 l

noncomputable def worldFull [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (ext : ExtractorLaw P) : ProbComp (FullOut P) := do
  let w ← worldRun pp m A
  let ωp ← sampleAssigns pp 1
  let ω0 ← sampleAssigns pp 3
  let ω1 ← sampleAssigns pp 3
  let x ← ext pp.S w.out.pv w.st.tr
  pure ⟨w, ωp 0, ω0, ω1, x⟩

def formsOfRun (w : WorldOut P) : Fin P.n → Vec (Fq P) P.N := formVec w.out.forms

def realR (w : WorldOut P) : Vec (Fq P) P.N := rField w.out.coins.2.1

def targetName [Fact (Nat.Prime P.q)] (pp : PublicParams P) (w : WorldOut P) : ClassName P :=
  labelName (w.enc .gₜ) (kappa pp w.out.coins)

def TargetQueried [Fact (Nat.Prime P.q)] (pp : PublicParams P) (w : WorldOut P) : Prop :=
  ∃ e ∈ w.st.kdfLog, e.2 = targetName pp w

def ExtFails [Fact (Nat.Prime P.q)] (S : Relation P) (x : Option (Vec (Fq P) P.N)) : Prop :=
  ∀ y, x = some y → ¬ IsWitness S y

def redViewOf (pp : PublicParams P) (m : Msg P) (w : WorldOut P) : RedView P :=
  ⟨pp, m, w.enc, w.out, w.st⟩

noncomputable def chalOf [Fact (1 < P.q)] (hd : P.d ≠ 0) (F : FormMatrix P) :
    MSISChallenge P hd :=
  fun ρ j => (msisRing P hd).coords.symm
    (fun i => F (ρ, some j) (Fin.cast (msisRing P hd).natDegree_eq i))

def RmWins [Fact (Nat.Prime P.q)] (hd : P.d ≠ 0) (pp : PublicParams P) (m : Msg P)
    (f : FullOut P) : Prop :=
  Algebra.MSISWins (msisRing P hd) P.eta (chalOf hd f.w.out.forms)
    (redOutput (redViewOf pp m f.w) f.wp (recAssign f.w0 f.w1))

end Runs

section Formal

variable {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
  (v : Fin P.n → Vec (Fq P) P.N)

def FormalEq1 (E F : Expr1 P) : Prop :=
  ∀ ω : Assign P, ValidCoins pp.qap ω.coins → val1 pp ω E = val1 pp ω F

def FormalEq2 (E F : Expr2 P) : Prop :=
  ∀ ω : Assign P, ValidCoins pp.qap ω.coins → val2 pp v ω E = val2 pp v ω F

def FormalEqT (E F : ExprT P) : Prop :=
  ∀ ω : Assign P, ValidCoins pp.qap ω.coins → valT pp v ω E = valT pp v ω F

def FormalKey (E : ExprT P) : Prop :=
  ∀ ω : Assign P, ValidCoins pp.qap ω.coins → valT pp v ω E = kappa pp ω.coins

def IdentityAtR (r : Vec (Fq P) P.N) (D : ExprT P) (ι : Fq P) : Prop :=
  ∀ c : Coins P, ValidCoins pp.qap c → valT pp v ⟨c, r⟩ D = ι * kappa pp c

end Formal

section Stacks

variable {P : Params}

def exprStack (D : ExprT P) (σ : Sector) : Stack P := fun c i j =>
  D.1 (some (.L1 c.1 i), some (.ZeroCoordinate σ c.2 j)) + D.1 (some (.L1 c.1 i), some (.totR1 σ c.2)) +
    D.1 (some (.totL1 c.1), some (.ZeroCoordinate σ c.2 j)) + D.1 (some (.totL1 c.1), some (.totR1 σ c.2))

def exprSC (D : ExprT P) (σ : Sector) (c : Cell P) : Vec (Fq P) P.N := fun i =>
  -(D.1 (some (.L1 c.1 i), some (.SC σ c.2)) + D.1 (some (.totL1 c.1), some (.SC σ c.2)))

open Classical in

noncomputable def markSector (D : ExprT P) : Sector :=
  if exprStack D .plain = 0 then .alpha else .plain

noncomputable def markStack (D : ExprT P) : Stack P := exprStack D (markSector D)

def sketchesOf (D : ExprT P) (sk : Sketches P) : Fin 3 → Sector → Vec (Fq P) P.N :=
  fun l σ => ∑ c, (exprStack D σ c).mulVec (sk c l σ)

def gradSpan [Fact (Nat.Prime P.q)] (pp : PublicParams P) (ωs : Fin 3 → Sector → Assign P)
    (D : ExprT P) (σ : Sector) : Submodule (Fq P) (Vec (Fq P) P.N) :=
  Submodule.span (Fq P) (Set.range fun l => rGrad pp (ωs l σ) D σ)

end Stacks

section Ideal

variable {P : Params}

variable (P) in

inductive Mark

  | init

  | g1
  | g2

  | diff (D : ExprT P)

  | key (D : ExprT P)

  | keyFormal

  | guessName

variable (P) in

structure IdealState where
  d1 : Label P → Option (Expr1 P)
  d2 : Label P → Option (Expr2 P)
  dT : Label P → Option (ExprT P)
  named : Label P → Bool
  mark : Option (Mark P)

variable (P) in

structure IdealCtx where
  eq1 : Expr1 P → Expr1 P → Prop
  eq2 : Expr2 P → Expr2 P → Prop
  eqT : ExprT P → ExprT P → Prop
  isKey : ExprT P → Prop

  keyLabels : List (Label P × Fq P)
  target : ClassName P

open Classical

section Steps

variable (cx : IdealCtx P)

noncomputable def ideal1 (k : Mark P) (st : IdealState P) (l : Label P) (F : Expr1 P) :
    IdealState P :=
  match st.d1 l with
  | none => { st with d1 := Function.update st.d1 l (some F) }
  | some E => if cx.eq1 F E then st else { st with mark := some k }

noncomputable def ideal2 (k : Mark P) (st : IdealState P) (l : Label P) (F : Expr2 P) :
    IdealState P :=
  match st.d2 l with
  | none => { st with d2 := Function.update st.d2 l (some F) }
  | some E => if cx.eq2 F E then st else { st with mark := some k }

noncomputable def idealT (initial : Bool) (st : IdealState P) (l : Label P) (F : ExprT P) :
    IdealState P :=
  match st.dT l with
  | none => { st with dT := Function.update st.dT l (some F) }
  | some E => if cx.eqT F E then st else
      { st with mark := some (if initial then .init else .diff (F - E)) }

noncomputable def recordT (st : IdealState P) (u w : Label P) : IdealState P :=
  { st with dT := fun l => if (l = u ∨ l = w) ∧ (st.dT l).isNone then some 0 else st.dT l }

noncomputable def idealOp (st : IdealState P) : TrOp P → IdealState P
  | .lin .g₁ a b u w res => ideal1 cx .g1 st res (a • (st.d1 u).getD 0 + b • (st.d1 w).getD 0)
  | .lin .g₂ a b u w res => ideal2 cx .g2 st res (a • (st.d2 u).getD 0 + b • (st.d2 w).getD 0)
  | .lin .gₜ a b u w res =>
    idealT cx false (recordT st u w) res (a • (st.dT u).getD 0 + b • (st.dT w).getD 0)
  | .pair u w res => idealT cx false st res (pairExpr ((st.d1 u).getD 0) ((st.d2 w).getD 0))
  | .name u res =>
    if st.named u then st else
      idealT cx false { st with named := Function.update st.named u true } (otherLabel u res)
        (-(st.dT u).getD 0)

noncomputable def idealKdf (st : IdealState P) (nm : ClassName P) : IdealState P :=
  if nm = cx.target then
    match cx.keyLabels.find? (fun kl => match st.dT kl.1 with
        | some E => decide (¬ cx.isKey (kl.2 • E))
        | none => false) with
    | some kl => { st with mark := some (.key (kl.2 • (st.dT kl.1).getD 0)) }
    | none =>
      if cx.keyLabels.any (fun kl => (st.dT kl.1).isSome) then { st with mark := some .keyFormal }
      else { st with mark := some .guessName }
  else st

noncomputable def idealEvent (st : IdealState P) (e : MonEvent P) : IdealState P :=
  match st.mark with
  | some _ => st
  | none =>
    match e with
    | .op o => idealOp cx st o
    | .kdf nm => idealKdf cx st nm

noncomputable def idealInit (pv : PubView P) : IdealState P :=
  let s0 : IdealState P := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => false, none⟩
  let s1 := pv.g1.foldl (fun st e => match st.mark with
    | some _ => st
    | none => ideal1 cx .init st e.2 (Pi.single e.1 1)) s0
  let s2 := pv.g2.foldl (fun st e => match st.mark with
    | some _ => st
    | none => ideal2 cx .init st e.2 (Pi.single e.1 1)) s1
  pv.gT.foldl (fun st e => match st.mark with
    | some _ => st
    | none => idealT cx true st e.2 (gtInit e.1)) s2

noncomputable def idealMonitor (pv : PubView P) (tr : List (TrOp P))
    (kl : List (ℕ × ClassName P)) : Option (Mark P) :=
  ((monEvents tr kl).foldl (idealEvent cx) (idealInit cx pv)).mark

end Steps

variable [Fact (Nat.Prime P.q)]

noncomputable def idealCtx (pp : PublicParams P) (w : WorldOut P) : IdealCtx P where
  eq1 := FormalEq1 pp
  eq2 := FormalEq2 pp (formsOfRun w)
  eqT := FormalEqT pp (formsOfRun w)
  isKey := FormalKey pp (formsOfRun w)
  keyLabels := [(w.enc .gₜ (kappa pp w.out.coins), 1), (w.enc .gₜ (-kappa pp w.out.coins), -1)]
  target := targetName pp w

noncomputable def firstMark (pp : PublicParams P) (w : WorldOut P) : Option (Mark P) :=
  idealMonitor (idealCtx pp w) w.out.pv w.st.tr w.st.kdfLog

end Ideal

section Classes

variable {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)

def Mark.data : Mark P → Option (ExprT P × Fq P)
  | .diff D => some (D, 0)
  | .key D => some (D, 1)
  | _ => none

def GoodCmp (w : WorldOut P) (D : ExprT P) (ι : Fq P) : Prop :=
  IdentityAtR pp (formsOfRun w) (realR w) D ι ∧ markStack D ≠ 0 ∧ Heavy (markStack D)

def GoodMark (w : WorldOut P) (D : ExprT P) (ι : Fq P) : Prop :=
  ∃ k, firstMark pp w = some k ∧ k.data = some (D, ι) ∧ GoodCmp pp w D ι

def ChargedCmp (w : WorldOut P) : Prop :=
  ∃ k, firstMark pp w = some k ∧
    (k = .g1 ∨ k = .g2 ∨ k = .keyFormal ∨ ∃ D ι, k.data = some (D, ι) ∧ ¬ GoodCmp pp w D ι)

def InjCase (w : WorldOut P) : Prop :=
  ∃ D ι, GoodMark pp w D ι ∧ jointSpace (markStack D) ⊓ LinearMap.ker (zLin (formsOfRun w)) = ⊥ ∧
    Module.finrank (Fq P) (jointSpace (markStack D)) ≤ dimMax

end Classes

section Terms

open Praxis.Constants

def ledgerInit : ℚ := (choose2 L1 + choose2 L2 + choose2 LT + (L : ℚ)) * eps_f

def ledgerName : ℚ := 2 * (T : ℚ) / (N_free : ℚ)

def ledgerRec (w : ℕ) : ℚ := (8 * (w : ℚ) + 8) * eps_f

def ledgerCmp (w : ℕ) : ℚ :=
  ledgerJ w * theta + ledgerJ w * eps_f +
    choose2 (L + 3 * w) * eps_f + ((L + 3 * w : ℕ) : ℚ) * eps_f +
    (2 * (L : ℚ) + 4 * (w : ℚ) + 2 * (T : ℚ)) / (N_free : ℚ) +
    4 * (w : ℚ) / 2 ^ 126 + statistical_seed

end Terms

end Praxis.Proofs
