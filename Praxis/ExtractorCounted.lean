import Praxis.Extractor
import Praxis.Units
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis

open OracleComp OracleSpec

open Praxis.Algebra (Vec Sat)

open GroupModel.Sorted (PSort)

variable {P : Params}

def sumC {q : ℕ} : List (ZMod q) → UnitComp q (ZMod q)
  | [] => fwrite 0
  | x :: xs => xs.foldlM fadd x

def sumMulC {q : ℕ} : List (ZMod q × ZMod q) → UnitComp q (ZMod q)
  | [] => fwrite 0
  | (a, b) :: xs => do
    let p ← fmul a b
    xs.foldlM (fun acc e => do
      let t ← fmul e.1 e.2
      fadd acc t) p

def linV (a b : Fq P) (A B : Vec (Fq P) P.N) : UnitComp P.q (Vec (Fq P) P.N) :=
  vecOfM fun i => do
    let x ← fmul a (A i)
    let y ← fmul b (B i)
    fadd x y

def addV (A B : Vec (Fq P) P.N) : UnitComp P.q (Vec (Fq P) P.N) := vecOfM fun i => fadd (A i) (B i)

def subV (A B : Vec (Fq P) P.N) : UnitComp P.q (Vec (Fq P) P.N) := vecOfM fun i => fsub (A i) (B i)

def negV (A : Vec (Fq P) P.N) : UnitComp P.q (Vec (Fq P) P.N) := vecOfM fun i => fneg (A i)

def smulV (a : Fq P) (A : Vec (Fq P) P.N) : UnitComp P.q (Vec (Fq P) P.N) :=
  vecOfM fun i => fmul a (A i)

variable (P)

def g2Keys : List (Cell P × Fin 3 × Sector) :=
  (cellList P).flatMap fun c => (List.finRange 3).flatMap fun l =>
    [Sector.plain, Sector.alpha].map fun s => (c, l, s)

def gtKeys : List (Fin 3 × Sector) :=
  (List.finRange 3).flatMap fun l => [Sector.plain, Sector.alpha].map fun s => (l, s)

variable {P}

def lookupC {α : Type} (t : Label P → Option α) (l : Label P) : UnitComp P.q (Option α) := do
  charge .tableStep
  pure (t l)

def insertC {α : Type} (t : Label P → Option α) (l : Label P) (a : α) :
    UnitComp P.q (Label P → Option α) := do
  charge .tableStep
  pure (keepEarliest t l a)

def linG1 (a b : Fq P) (A B : Fin P.K1 → Vec (Fq P) P.N) :
    UnitComp P.q (Fin P.K1 → Vec (Fq P) P.N) :=
  funOfM (List.finRange P.K1) 0 fun k => linV a b (A k) (B k)

def linG2 (a b : Fq P) (A B : Cell P → Fin 3 → Sector → Fq P) :
    UnitComp P.q (Cell P → Fin 3 → Sector → Fq P) := do
  let t ← funOfM (g2Keys P) 0 fun e => do
    let x ← fmul a (A e.1 e.2.1 e.2.2)
    let y ← fmul b (B e.1 e.2.1 e.2.2)
    fadd x y
  pure fun c l s => t (c, l, s)

def mapGT (f : Vec (Fq P) P.N → UnitComp P.q (Vec (Fq P) P.N))
    (F : Fin 3 → Sector → Vec (Fq P) P.N) : UnitComp P.q (Fin 3 → Sector → Vec (Fq P) P.N) := do
  let t ← funOfM gtKeys 0 fun e => f (F e.1 e.2)
  pure fun l s => t (l, s)

def mapGT2 (f : Vec (Fq P) P.N → Vec (Fq P) P.N → UnitComp P.q (Vec (Fq P) P.N))
    (F G : Fin 3 → Sector → Vec (Fq P) P.N) : UnitComp P.q (Fin 3 → Sector → Vec (Fq P) P.N) := do
  let t ← funOfM gtKeys 0 fun e => f (F e.1 e.2) (G e.1 e.2)
  pure fun l s => t (l, s)

def pairC (α : Fin P.K1 → Vec (Fq P) P.N) (β : Cell P → Fin 3 → Sector → Fq P) :
    UnitComp P.q (Fin 3 → Sector → Vec (Fq P) P.N) := do
  let t ← funOfM gtKeys 0 fun e => do
    let cb ← funOfM (List.finRange P.K1) 0 fun k1 =>
      sumC ((legList P).map fun leg => β (k1, leg) e.1 e.2)
    vecOfM fun i => sumMulC ((List.finRange P.K1).map fun k1 => (cb k1, α k1 i))
  pure fun l s => t (l, s)

def findPivotC (col : Fin (P.N + 1)) : List (Vec (Fq P) P.N) → ℕ → UnitComp P.q (Option ℕ)
  | [], _ => pure none
  | r :: rs, k => do
    let z ← feq (r col) 0
    if z then findPivotC col rs (k + 1) else pure (some k)

def elimC (col : Fin (P.N + 1)) (r' w : Vec (Fq P) P.N) : UnitComp P.q (Vec (Fq P) P.N) :=
  vecOfM fun i => do
    let t ← fmul (w col) (r' i)
    fsub (w i) t

def rrefC (rows : List (Vec (Fq P) P.N)) :
    UnitComp P.q (List (Fin (P.N + 1) × Vec (Fq P) P.N)) := do
  let st ← (List.finRange (P.N + 1)).foldlM
    (fun (st : List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N)) col => do
      match ← findPivotC col st.1 0 with
      | none => pure st
      | some k =>
        let r := st.1.getD k 0
        let piv ← finv (r col)
        let r' ← smulV piv r
        let rest ← (st.1.eraseIdx k).mapM (elimC col r')
        let basis ← st.2.mapM fun b => do
          let v ← elimC col r' b.2
          pure (b.1, v)
        pure (rest, basis ++ [(col, r')]))
    (rows, [])
  pure st.2

def candidatesC (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N)) :
    UnitComp P.q (List (Vec (Fq P) P.N)) :=
  match basis with
  | [] => pure []
  | b :: rest =>
    if b.1 = 0 then rest.sublists.mapM fun T => T.foldlM (fun acc r => addV acc r.2) b.2
    else pure []

def allC {q : ℕ} {ι : Type} : List ι → (ι → UnitComp q Bool) → UnitComp q Bool
  | [], _ => pure true
  | i :: is, f => do
    let b ← f i
    if b then allC is f else pure false

def dotC (a : SparseForm P) (x : Vec (Fq P) P.N) : UnitComp P.q (Fq P) :=
  sumMulC (a.map fun e => (e.2, x e.1))

def satC (S : SparseRelation P) (x : Vec (Fq P) P.N) : UnitComp P.q Bool := do
  let h0 ← feq (x 0) 1
  if !h0 then return false
  let hb ← allC (List.finRange P.N) fun i => do
    let z ← feq (x i.succ) 0
    if z then pure true else feq (x i.succ) 1
  if !hb then return false
  allC (List.finRange P.gatesMax) fun t => do
    let prods ← (List.finRange (S t).products).mapM fun f => do
      let a ← dotC ((S t).left f) x
      let b ← dotC ((S t).right f) x
      fmul a b
    let lhs ← sumC prods
    let c ← dotC (S t).linear x
    let rhs ← fmul (x 0) c
    feq lhs rhs

def firstC (S : SparseRelation P) : List (Vec (Fq P) P.N) → UnitComp P.q (Option (Vec (Fq P) P.N))
  | [] => pure none
  | x :: xs => do
    let ok ← satC S x
    if ok then pure (some x) else firstC S xs

def testSketchesC (S : SparseRelation P) (s : Fin 3 → Vec (Fq P) P.N) :
    UnitComp P.q (Option (Vec (Fq P) P.N)) := do
  let basis ← rrefC [s 0, s 1, s 2]
  let cands ← candidatesC basis
  firstC S cands

def testExprC (S : SparseRelation P) (F : Fin 3 → Sector → Vec (Fq P) P.N) :
    UnitComp P.q (Option (Vec (Fq P) P.N)) := do
  match ← testSketchesC S fun l => F l .plain with
  | some x => pure (some x)
  | none => testSketchesC S fun l => F l .alpha

def gtStepC (S : SparseRelation P) (st : ExState P) (F : Fin 3 → Sector → Vec (Fq P) P.N)
    (res : Label P) : UnitComp P.q (ExState P) := do
  let old ← lookupC st.dT res
  let dT ← insertC st.dT res F
  match ← testExprC S F with
  | some x => pure { st with dT := dT, found := some x }
  | none =>
    match old with
    | none => pure { st with dT := dT, found := none }
    | some E => do
      let D ← mapGT2 subV F E
      let r ← testExprC S D
      pure { st with dT := dT, found := r }

def exStepC (S : SparseRelation P) (st : ExState P) (op : TrOp P) : UnitComp P.q (ExState P) :=
  match st.found with
  | some _ => pure st
  | none =>
    match op with
    | .lin .g₁ a b u v res => do
      let A ← lookupC st.d1 u
      let B ← lookupC st.d1 v
      let R ← linG1 a b (A.getD 0) (B.getD 0)
      let d1 ← insertC st.d1 res R
      pure { st with d1 := d1 }
    | .lin .g₂ a b u v res => do
      let A ← lookupC st.d2 u
      let B ← lookupC st.d2 v
      let R ← linG2 a b (A.getD 0) (B.getD 0)
      let d2 ← insertC st.d2 res R
      pure { st with d2 := d2 }
    | .lin .gₜ a b u v res => do
      let A ← lookupC st.dT u
      let B ← lookupC st.dT v
      let F ← mapGT2 (linV a b) (A.getD 0) (B.getD 0)
      gtStepC S st F res
    | .pair u v res => do
      let A ← lookupC st.d1 u
      let B ← lookupC st.d2 v
      let F ← pairC (A.getD 0) (B.getD 0)
      gtStepC S st F res
    | .name v res => do
      charge .tableStep
      if st.named v then pure st else do
        charge .tableStep
        let st' := { st with named := Function.update st.named v true }
        let A ← lookupC st.dT v
        let F ← mapGT negV (A.getD 0)
        gtStepC S st' F (otherLabel v res)

def drawSketchesC : UnitComp P.q (Sketches P) := do
  let t ← funOfM (g2Keys P) 0 fun _ => vecOfM fun _ => sampleF
  pure fun c l s => t (c, l, s)

def initG2C (sk : Sketches P) : Option (G2Idx P) → UnitComp P.q (Cell P → Fin 3 → Sector → Fq P)
  | some (.totR1 σ leg) => do
    let t ← funOfM (((cellList P).filter fun c => decide (c.2 = leg)).flatMap fun c =>
        (List.finRange 3).map fun l => (c, l)) 0 fun e =>
      sumC ((List.finRange (P.N + 1)).map fun j => sk e.1 e.2 σ j)
    pure fun c l σ' => if σ' = σ ∧ c.2 = leg then t (c, l) else 0
  | i => pure (initG2 sk i)

def initStateC (pub : PubView P) (sk : Sketches P) : UnitComp P.q (ExState P) := do
  let d1 ← pub.g1.foldlM (fun t e => insertC t e.2 (initG1 e.1)) fun _ => none
  let d2 ← pub.g2.foldlM (fun t e => do
      let D ← initG2C sk e.1
      insertC t e.2 D) fun _ => none
  let dT ← pub.gT.foldlM (fun t e => insertC t e.2 0) fun _ => none
  pure { d1 := d1, d2 := d2, dT := dT, named := fun _ => false, found := none }

def extractorC [Fact (Nat.Prime P.q)] (S : SparseRelation P) (pub : PubView P)
    (tr : List (TrOp P)) : UnitComp P.q (Option (Vec (Fq P) P.N)) := do
  let sk ← drawSketchesC
  let st0 ← initStateC pub sk
  let st ← tr.foldlM (exStepC S) st0
  pure st.found

end Praxis
