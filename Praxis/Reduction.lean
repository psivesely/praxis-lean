import Praxis.Games
import Praxis.Algebra.Stmt.Short
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis

open OracleComp OracleSpec GroupModel.Sorted

open Praxis.Algebra (Vec dot CoeffVec MSISWins)

variable {P : Params}

instance oneLtOfPrime [h : Fact (Nat.Prime P.q)] : Fact (1 < P.q) := ⟨h.out.one_lt⟩

variable (P) in

structure Assign where
  coins : Coins P
  r : Vec (Fq P) P.N

def Assign.ofCoins (c : Coins P) : Assign P := ⟨c, rField c.2.1⟩

section Exponents

variable [Fact (Nat.Prime P.q)] (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)

def r1ExpAt (ω : Assign P) (l : Leg P) (j : Fin (P.N + 1)) : Fq P :=
  (legScale ω.coins l * (ω.r j + (pp.qap.A j).eval (coin ω.coins .tau)) + legMask v ω.coins l j) -
    coin ω.coins .Om12 / coin ω.coins .Om22 * H2 pp ω.coins l j

def e1At (ω : Assign P) : Option (G1Idx P) → Fq P
  | none => 1
  | some i => g1Exp pp ω.coins i

noncomputable def e2At (ω : Assign P) : Option (G2Idx P) → Fq P
  | none => 1
  | some (.ZeroCoordinate σ l j) => sectorScale ω.coins σ * r1ExpAt pp v ω l j
  | some (.totR1 σ l) => sectorScale ω.coins σ * ∑ j, r1ExpAt pp v ω l j
  | some i => g2Exp pp v ω.coins i

end Exponents

variable (P) in

abbrev Expr1 : Type := Option (G1Idx P) → Fq P

variable (P) in

abbrev Expr2 : Type := Option (G2Idx P) → Fq P

variable (P) in

abbrev ExprT : Type := (Option (G1Idx P) × Option (G2Idx P) → Fq P) × Fq P

variable (P) in

def keys1 : List (Option (G1Idx P)) := none :: (g1Order P).map some

variable (P) in

def keys2 : List (Option (G2Idx P)) := none :: (g2Order P).map some

def pairExpr (A : Expr1 P) (B : Expr2 P) : ExprT P := (fun ab => A ab.1 * B ab.2, 0)

def gtInit : Option Unit → ExprT P
  | none => (Pi.single (none, none) 1, 0)
  | some () => (0, 1)

section Values

variable [Fact (Nat.Prime P.q)] (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
  (ω : Assign P)

def val1 (E : Expr1 P) : Fq P := ((keys1 P).map fun a => E a * e1At pp ω a).sum

noncomputable def val2 (E : Expr2 P) : Fq P := ((keys2 P).map fun b => E b * e2At pp v ω b).sum

noncomputable def valT (E : ExprT P) : Fq P :=
  ((keys1 P).map fun a => ((keys2 P).map fun b =>
    E.1 (a, b) * (e1At pp ω a * e2At pp v ω b)).sum).sum + E.2 * gtExp pp ω.coins

end Values

variable (P) in

inductive MonStop

  | running

  | noStack

  | stack (D : ExprT P)

variable (P) in

structure MonState where
  d1 : Label P → Option (Expr1 P)
  d2 : Label P → Option (Expr2 P)
  dT : Label P → Option (ExprT P)
  named : Label P → Bool
  stop : MonStop P

variable (P) in

structure MonCtx where
  priv1 : Expr1 P → Fq P
  priv2 : Expr2 P → Fq P
  privT : ExprT P → Fq P

  keyLabels : List (Label P × Fq P)

  keyPriv : Fq P

  target : ClassName P

variable (P) in

inductive MonEvent
  | op (o : TrOp P)
  | kdf (nm : ClassName P)

def monEvents (tr : List (TrOp P)) (kl : List (ℕ × ClassName P)) : List (MonEvent P) :=
  (List.range (tr.length + 1)).flatMap fun k =>
    (kl.filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
      (tr[k]?).toList.map MonEvent.op

def monInit (pv : PubView P) : MonState P where
  d1 := pv.g1.foldl (fun t e => keepEarliest t e.2 (Pi.single e.1 1)) fun _ => none
  d2 := pv.g2.foldl (fun t e => keepEarliest t e.2 (Pi.single e.1 1)) fun _ => none
  dT := pv.gT.foldl (fun t e => keepEarliest t e.2 (gtInit e.1)) fun _ => none
  named := fun _ => false
  stop := .running

section Monitor

variable (cx : MonCtx P)

def monNew1 (st : MonState P) (res : Label P) (F : Expr1 P) : MonState P :=
  match st.d1 res with
  | none => { st with d1 := Function.update st.d1 res (some F) }
  | some E => if cx.priv1 F = cx.priv1 E then st else { st with stop := .noStack }

def monNew2 (st : MonState P) (res : Label P) (F : Expr2 P) : MonState P :=
  match st.d2 res with
  | none => { st with d2 := Function.update st.d2 res (some F) }
  | some E => if cx.priv2 F = cx.priv2 E then st else { st with stop := .noStack }

def monNewT (st : MonState P) (res : Label P) (F : ExprT P) : MonState P :=
  match st.dT res with
  | none => { st with dT := Function.update st.dT res (some F) }
  | some E => if cx.privT F = cx.privT E then st else { st with stop := .stack (F - E) }

def monRecordT (st : MonState P) (u w : Label P) : MonState P :=
  { st with dT := fun l => if (l = u ∨ l = w) ∧ (st.dT l).isNone then some 0 else st.dT l }

def monOp (st : MonState P) : TrOp P → MonState P
  | .lin .g₁ a b u w res => monNew1 cx st res (a • (st.d1 u).getD 0 + b • (st.d1 w).getD 0)
  | .lin .g₂ a b u w res => monNew2 cx st res (a • (st.d2 u).getD 0 + b • (st.d2 w).getD 0)
  | .lin .gₜ a b u w res =>
    monNewT cx (monRecordT st u w) res (a • (st.dT u).getD 0 + b • (st.dT w).getD 0)
  | .pair u w res => monNewT cx st res (pairExpr ((st.d1 u).getD 0) ((st.d2 w).getD 0))
  | .name u res =>
    if st.named u then st else
      monNewT cx { st with named := Function.update st.named u true } (otherLabel u res)
        (-(st.dT u).getD 0)

def monKdf (st : MonState P) (nm : ClassName P) : MonState P :=
  if nm = cx.target then
    cx.keyLabels.foldl (fun st' kl =>
      match st'.stop, st'.dT kl.1 with
      | .running, some E =>
        if kl.2 * cx.privT E = cx.keyPriv then st' else { st' with stop := .stack (kl.2 • E) }
      | _, _ => st') st
  else st

def monEvent (st : MonState P) (e : MonEvent P) : MonState P :=
  match st.stop with
  | .running =>
    match e with
    | .op o => monOp cx st o
    | .kdf nm => monKdf cx st nm
  | _ => st

def monitor (pv : PubView P) (tr : List (TrOp P)) (kl : List (ℕ × ClassName P)) : MonStop P :=
  ((monEvents tr kl).foldl (monEvent cx) (monInit pv)).stop

end Monitor

def rGrad [Fact (Nat.Prime P.q)] (pp : PublicParams P) (ω : Assign P) (D : ExprT P)
    (σ : Sector) : Vec (Fq P) P.N := fun j =>
  ((legList P).map fun l => sectorScale ω.coins σ * legScale ω.coins l *
    ((keys1 P).map fun a =>
      e1At pp ω a * (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l)))).sum).sum

def rrefK {F : Type*} [Field F] [DecidableEq F] {k : ℕ} (rows : List (Fin k → F)) :
    List (Fin k × (Fin k → F)) :=
  ((List.finRange k).foldl
    (fun (st : List (Fin k → F) × List (Fin k × (Fin k → F))) col =>
      match st.1.find? (fun r => decide (r col ≠ 0)) with
      | none => st
      | some r =>
        let r' := (r col)⁻¹ • r
        let elim := fun w : Fin k → F => w - w col • r'
        ((st.1.erase r).map elim, (st.2.map fun b => (b.1, elim b.2)) ++ [(col, r')]))
    (rows, [])).2

def firstNull {F : Type*} [Field F] {k : ℕ} (R : List (Fin k × (Fin k → F))) :
    Option (Fin k → F) :=
  match (List.finRange k).find? (fun f => !(R.any fun b => decide (b.1 = f))) with
  | none => none
  | some f => some fun i =>
    if i = f then 1 else
      match R.find? (fun b => decide (b.1 = i)) with
      | some b => -(b.2 f)
      | none => 0

def kernelVec [Fact (Nat.Prime P.q)] (forms : FormMatrix P) (g : Fin 3 → Vec (Fq P) P.N) :
    Option (Vec (Fq P) P.N) :=
  let B := (rref [g 0, g 1, g 2]).map Prod.snd
  let eqs : List (Fin B.length → Fq P) :=
    ((List.finRange P.n).map fun e => fun l => dot (formVec forms e) (B.getD l.val 0)) ++
      [fun l => (B.getD l.val 0) 0]
  (firstNull (rrefK eqs)).map fun c => ∑ l, c l • B.getD l.val 0

def convertLIFT [NeZero P.q] (v : Vec (Fq P) P.N) : Option (Vec ℤ P.N) :=
  Algebra.Short.bruteForce P.q P.eta v

def packCore (z : Vec ℤ P.N) : CoeffVec P.d P.cols :=
  fun c t => if h : c.val * P.d + t.val < P.N then z (Fin.succ ⟨c.val * P.d + t.val, h⟩) else 0

noncomputable def monCtx [Fact (Nat.Prime P.q)] (rv : RedView P) (ωp : Assign P) : MonCtx P :=
  let v := formVec rv.out.forms
  let κ := kappa rv.pp rv.out.coins
  { priv1 := val1 rv.pp ωp
    priv2 := val2 rv.pp v ωp
    privT := valT rv.pp v ωp
    keyLabels := [(rv.enc .gₜ κ, 1), (rv.enc .gₜ (-κ), -1)]
    keyPriv := kappa rv.pp ωp.coins
    target := labelName (rv.enc .gₜ) κ }

noncomputable def chooseVec [Fact (Nat.Prime P.q)] (rv : RedView P)
    (ωs : Fin 3 → Sector → Assign P) (D : ExprT P) : Option (Vec (Fq P) P.N) :=
  let kv := fun σ : Sector => kernelVec rv.out.forms fun l => rGrad rv.pp (ωs l σ) D σ
  (kv .plain).orElse fun _ => kv .alpha

noncomputable def redOutput [Fact (Nat.Prime P.q)] (rv : RedView P) (ωp : Assign P)
    (ωs : Fin 3 → Sector → Assign P) : Option (CoeffVec P.d P.cols) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  match monitor (monCtx rv ωp) rv.out.pv rv.state.tr rv.state.kdfLog with
  | .stack D => ((chooseVec rv ωs D).bind convertLIFT).map packCore
  | _ => none

noncomputable def sampleAssigns [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (k : ℕ) : ProbComp (Fin k → Assign P) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  do
    let cs ← $ᵗ (Fin k → {c : Coins P // ValidCoins pp.qap c})
    let rs ← $ᵗ (Fin k → Vec (Fq P) P.N)
    pure fun i => ⟨(cs i).1, rs i⟩

noncomputable def redPost [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (rv : RedView P) :
    ProbComp (Option (CoeffVec P.d P.cols)) := do
  let ωp ← sampleAssigns pp 1
  let ω0 ← sampleAssigns pp 3
  let ω1 ← sampleAssigns pp 3
  pure (redOutput rv (ωp 0) fun l σ => match σ with
    | .plain => ω0 l
    | .alpha => ω1 l)

noncomputable def reduction [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (hd : P.d ≠ 0) (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (A : Adversary P) (chal : MSISChallenge P hd) :
    ProbComp (Option (CoeffVec P.d P.cols)) := do
  let aStar ← $ᵗ (Fin P.rows → Rq P)
  blackBoxRun pp m A (redPost pp) (formsOfChallenge P hd chal aStar)

noncomputable def msisSucc {p d rows cols : ℕ} [NeZero p] (R : Algebra.MSISRing p d) (B : ℕ)
    (red : Algebra.RingMatrix R rows cols → ProbComp (Option (CoeffVec d cols))) : ℝ := by
  classical
  haveI : Nonempty (Algebra.RingMatrix R rows cols) := ⟨0⟩
  letI := SampleableType.ofFintype (Algebra.RingMatrix R rows cols)
  exact (Pr[= true | do
    let chal ← $ᵗ (Algebra.RingMatrix R rows cols)
    let out ← red chal
    pure (decide (MSISWins R B chal out))]).toReal

end Praxis
