import Praxis.Setting
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.QueryBound

namespace Praxis

open OracleComp OracleSpec

def unitWordBits : ℕ := 256

inductive FieldStep (q : ℕ) where
  | add (x y : ZMod q)
  | sub (x y : ZMod q)
  | mul (x y : ZMod q)
  | neg (x : ZMod q)
  | inv (x : ZMod q)
  | eq (x y : ZMod q)
  | write (x : ZMod q)

@[reducible] def fieldStepModel (q : ℕ) : OracleSpec (FieldStep q)
  | .eq _ _ => Bool
  | .add _ _ => ZMod q
  | .sub _ _ => ZMod q
  | .mul _ _ => ZMod q
  | .neg _ => ZMod q
  | .inv _ => ZMod q
  | .write _ => ZMod q

def fieldStepAnswer {q : ℕ} : (s : FieldStep q) → fieldStepModel q s
  | .add x y => x + y
  | .sub x y => x - y
  | .mul x y => x * y
  | .neg x => -x
  | .inv x => x⁻¹
  | .eq x y => decide (x = y)
  | .write x => x

inductive Charge where

  | xor

  | intStep

  | tableStep

  | oracleCall

  | bigIntUnit
  deriving DecidableEq, Repr

@[reducible] def chargeModel : OracleSpec Charge := fun _ => Unit

@[reducible] def unitModel (q : ℕ) := unifSpec + fieldStepModel q + chargeModel

abbrev UnitComp (q : ℕ) (α : Type) := OracleComp (unitModel q) α

section Primitives

variable {q : ℕ}

def fstep (s : FieldStep q) : UnitComp q (fieldStepModel q s) :=
  liftM ((unitModel q).query (.inl (.inr s)))

def fadd (x y : ZMod q) : UnitComp q (ZMod q) := fstep (.add x y)

def fsub (x y : ZMod q) : UnitComp q (ZMod q) := fstep (.sub x y)

def fmul (x y : ZMod q) : UnitComp q (ZMod q) := fstep (.mul x y)

def fneg (x : ZMod q) : UnitComp q (ZMod q) := fstep (.neg x)

def finv (x : ZMod q) : UnitComp q (ZMod q) := fstep (.inv x)

def feq (x y : ZMod q) : UnitComp q Bool := fstep (.eq x y)

def fwrite (x : ZMod q) : UnitComp q (ZMod q) := fstep (.write x)

def charge (c : Charge) : UnitComp q Unit :=
  liftM ((unitModel q).query (.inr c))

def sampleFin (n : ℕ) : UnitComp q (Fin (n + 1)) :=
  liftM ((unitModel q).query (.inl (.inl n)))

def sampleF : UnitComp q (ZMod q) := do
  let i ← sampleFin (q - 1)
  pure (i.val : ZMod q)

def vecOfM {n : ℕ} (f : Fin n → UnitComp q (ZMod q)) : UnitComp q (Fin n → ZMod q) := do
  let l ← (List.finRange n).mapM f
  pure fun i => l.getD i.val 0

def funOfM {ι β : Type} [DecidableEq ι] (idx : List ι) (d : β) (f : ι → UnitComp q β) :
    UnitComp q (ι → β) := do
  let l ← idx.mapM fun i => do
    let b ← f i
    pure (i, b)
  pure fun i => ((l.find? fun e => decide (e.1 = i)).map Prod.snd).getD d

end Primitives

def isUnit {q : ℕ} : (unitModel q).Domain → Prop := fun _ => True

instance {q : ℕ} : DecidablePred (@isUnit q) := fun _ => isTrue trivial

def WithinUnits {q : ℕ} {α : Type} (c : UnitComp q α) (k : ℕ) : Prop :=
  IsQueryBoundP c isUnit k

def isLargeSample {q : ℕ} : (unitModel q).Domain → Prop
  | .inl (.inl n) => 2 ^ unitWordBits < n + 1
  | _ => False

instance {q : ℕ} : DecidablePred (@isLargeSample q) := fun i => by
  rcases i with (n | s) | c
  · exact inferInstanceAs (Decidable (2 ^ unitWordBits < n + 1))
  · exact isFalse id
  · exact isFalse id

def SmallSamples {q : ℕ} {α : Type} (c : UnitComp q α) : Prop :=
  IsQueryBoundP c isLargeSample 0

def unitImpl (q : ℕ) : QueryImpl (unitModel q) ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr s) => pure (fieldStepAnswer s)
  | .inr _ => pure ()

def runUnits {q : ℕ} {α : Type} (c : UnitComp q α) : ProbComp α :=
  simulateQ (unitImpl q) c

end Praxis
