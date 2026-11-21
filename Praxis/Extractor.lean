import Praxis.Dec
import Praxis.Encryption.GroupModel
import Praxis.Encryption.BN254
import VCVio.OracleComp.QueryTracking.QueryBound
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat dot Sat)

open GroupModel.Sorted (PSort)

variable (P : Params)

structure PubView where
  g1 : List (Option (G1Idx P) × Label P)
  g2 : List (Option (G2Idx P) × Label P)

  gT : List (Option Unit × Label P)

inductive TrOp
  | lin (s : PSort) (a b : Fq P) (u v res : Label P)
  | pair (u v res : Label P)
  | name (v : Label P) (res : ClassName P)

abbrev Sketches : Type := Cell P → Fin 3 → Sector → Vec (Fq P) P.N

structure ExState where
  d1 : Label P → Option (Fin P.K1 → Vec (Fq P) P.N)
  d2 : Label P → Option (Cell P → Fin 3 → Sector → Fq P)
  dT : Label P → Option (Fin 3 → Sector → Vec (Fq P) P.N)
  named : Label P → Bool
  found : Option (Vec (Fq P) P.N)

variable {P}

def keepEarliest {α : Type*} (t : Label P → Option α) (l : Label P) (a : α) :
    Label P → Option α :=
  match t l with
  | some _ => t
  | none => Function.update t l (some a)

def rref [Fact (Nat.Prime P.q)] (rows : List (Vec (Fq P) P.N)) :
    List (Fin (P.N + 1) × Vec (Fq P) P.N) :=
  ((List.finRange (P.N + 1)).foldl
    (fun (st : List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N)) col =>
      match st.1.find? (fun r => decide (r col ≠ 0)) with
      | none => st
      | some r =>
        let r' := (r col)⁻¹ • r
        let elim := fun w : Vec (Fq P) P.N => w - w col • r'
        ((st.1.erase r).map elim, (st.2.map fun b => (b.1, elim b.2)) ++ [(col, r')]))
    (rows, [])).2

def candidates (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N)) : List (Vec (Fq P) P.N) :=
  match basis with
  | [] => []
  | b :: rest =>
    if b.1 = 0 then rest.sublists.map fun T => b.2 + (T.map Prod.snd).sum else []

def testSketches [Fact (Nat.Prime P.q)] (S : Relation P) (s : Fin 3 → Vec (Fq P) P.N) :
    Option (Vec (Fq P) P.N) :=
  (candidates (rref [s 0, s 1, s 2])).find? fun v => decide (Sat S v)

def testExpr [Fact (Nat.Prime P.q)] (S : Relation P) (F : Fin 3 → Sector → Vec (Fq P) P.N) :
    Option (Vec (Fq P) P.N) :=
  (testSketches S fun l => F l .plain).orElse fun _ => testSketches S fun l => F l .alpha

def gtStep [Fact (Nat.Prime P.q)] (S : Relation P) (st : ExState P)
    (F : Fin 3 → Sector → Vec (Fq P) P.N) (res : Label P) : ExState P :=
  let st' := { st with dT := keepEarliest st.dT res F }
  let r1 := testExpr S F
  let r2 := match st.dT res with
    | some E => testExpr S (F - E)
    | none => none
  { st' with found := r1.orElse fun _ => r2 }

def otherLabel (l : Label P) (res : ClassName P) : Label P :=
  Sym2.lift ⟨fun a b => if a = l then b else if b = l then a else l, by
    intro a b; by_cases ha : a = l <;> by_cases hb : b = l <;> simp [ha, hb]⟩ res

def exStep [Fact (Nat.Prime P.q)] (S : Relation P) (st : ExState P) (op : TrOp P) :
    ExState P :=
  match st.found with
  | some _ => st
  | none =>
    match op with
    | .lin .g₁ a b u v res =>
      let A := (st.d1 u).getD 0
      let B := (st.d1 v).getD 0
      { st with d1 := keepEarliest st.d1 res (a • A + b • B) }
    | .lin .g₂ a b u v res =>
      let A := (st.d2 u).getD 0
      let B := (st.d2 v).getD 0
      { st with d2 := keepEarliest st.d2 res (a • A + b • B) }
    | .lin .gₜ a b u v res =>
      gtStep S st (a • (st.dT u).getD 0 + b • (st.dT v).getD 0) res
    | .pair u v res =>
      let α := (st.d1 u).getD 0
      let β := (st.d2 v).getD 0
      gtStep S st (fun l σ => ∑ k1 : Fin P.K1,
        (∑ leg : Leg P, β (k1, leg) l σ) • α k1) res
    | .name v res =>
      if st.named v then st else
      let st' := { st with named := Function.update st.named v true }
      gtStep S st' (-(st.dT v).getD 0) (otherLabel v res)

def initG1 : Option (G1Idx P) → Fin P.K1 → Vec (Fq P) P.N
  | some (.L1 k1 i) => fun k => if k = k1 then Pi.single i 1 else 0
  | some (.totL1 k1) => fun k => if k = k1 then fun _ => 1 else 0
  | _ => 0

def initG2 (sk : Sketches P) : Option (G2Idx P) → Cell P → Fin 3 → Sector → Fq P
  | some (.ZeroCoordinate σ leg j) => fun c l σ' => if σ' = σ ∧ c.2 = leg then sk c l σ j else 0
  | some (.totR1 σ leg) => fun c l σ' => if σ' = σ ∧ c.2 = leg then ∑ j, sk c l σ j else 0
  | _ => 0

def initState (pub : PubView P) (sk : Sketches P) : ExState P where
  d1 := pub.g1.foldl (fun t e => keepEarliest t e.2 (initG1 e.1)) fun _ => none
  d2 := pub.g2.foldl (fun t e => keepEarliest t e.2 (initG2 sk e.1)) fun _ => none
  dT := pub.gT.foldl (fun t e => keepEarliest t e.2 0) fun _ => none
  named := fun _ => false
  found := none

def extractWith [Fact (Nat.Prime P.q)] (S : Relation P) (pub : PubView P) (tr : List (TrOp P))
    (sk : Sketches P) : Option (Vec (Fq P) P.N) :=
  (tr.foldl (exStep S) (initState pub sk)).found

noncomputable def extractorRef [Fact (Nat.Prime P.q)] (S : Relation P) (pub : PubView P)
    (tr : List (TrOp P)) : ProbComp (Option (Vec (Fq P) P.N)) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (Sketches P)
  do
    let sk ← $ᵗ (Sketches P)
    pure (extractWith S pub tr sk)

end Praxis
