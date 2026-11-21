import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.View.SZ.Grid
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold

open Classical

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

section Defs

abbrev World (pp : PublicParams P0) := WorldOut P0 × ObsState pp

def keyCmp (pp : PublicParams P0) (z : WorldOut P0) (sh : State pp) : Option (Collision pp) :=
  match sh.dict .gₜ (z.enc .gₜ (kappa pp z.out.coins)) with
  | some P => some ⟨.gₜ, z.enc .gₜ (kappa pp z.out.coins), P, key pp⟩
  | none => match sh.dict .gₜ (z.enc .gₜ (-kappa pp z.out.coins)) with
    | some P => some ⟨.gₜ, z.enc .gₜ (-kappa pp z.out.coins), scalar pp (-1) * P, key pp⟩
    | none => none

def badCmp {pp : PublicParams P0} (ω : World pp) : Option (Collision pp) :=
  match ω.2.stop with
  | none => none
  | some b => match ω.2.steps[b]? with
    | none => none
    | some st => match st.entry.1 with
      | .inl (.inl (.inr _)) => st.shadow.first
      | .inr _ => keyCmp pp ω.1 st.shadow
      | _ => none

def _root_.Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic.Collision.diff {pp : PublicParams P0}
    (e : Collision pp) : Poly pp := e.new - e.old

def _root_.Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic.Collision.value {pp : PublicParams P0}
    (e : Collision pp) : Exposure.Coeff pp :=
  MvPolynomial.constantCoeff e.diff

def GuessFree {pp : PublicParams P0} (e : Collision pp) : Prop :=
  e.diff = MvPolynomial.C e.value

def IdentityAt {pp : PublicParams P0} (f : Exposure.Coeff pp) (r : Vec k P0.N) : Prop :=
  ∀ (c : Coins P0) (hc : ValidCoins pp.qap c), f ⟨⟨c, r⟩, hc⟩ = 0

def LightCmp (pp : PublicParams P0) (forms : FormMatrix P0) (f : Exposure.Coeff pp) : Prop :=
  ∃ (D : ExprT P0) (ι : k),
    f = Exposure.valueT pp (formVec forms) D - ι • Exposure.valueKey pp ∧ Light (markStack D)

def BadAt {pp : PublicParams P0} (ω : World pp) (e : Collision pp) : Prop :=
  ∃ b, ω.2.stop = some b ∧ Clean b ω ∧ badCmp ω = some e

def BadGuess {pp : PublicParams P0} (ω : World pp) : Prop :=
  ∃ e, BadAt ω e ∧ ¬ GuessFree e

def BadField {pp : PublicParams P0} (ω : World pp) : Prop :=
  ∃ e, BadAt ω e ∧ GuessFree e ∧ ¬ IdentityAt e.value (realR ω.1)

def BadLight {pp : PublicParams P0} (ω : World pp) : Prop :=
  ∃ e, BadAt ω e ∧ GuessFree e ∧ IdentityAt e.value (realR ω.1) ∧ e.sort = .gₜ ∧
    LightCmp pp ω.1.out.forms e.value

def Catches {pp : PublicParams P0} {J : Type} (cmp : J → Record pp → Option (Collision pp))
    (j : J) (ω : World pp) (e : Collision pp) : Prop :=
  ∃ n, Clean n ω ∧ (∀ n' < n, cmp j ((fullRecord ω).cut n') = none) ∧
    ∃ e', cmp j ((fullRecord ω).cut n) = some e' ∧ e'.sort = e.sort ∧ e'.diff = e.diff ∧
      e'.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset

end Defs

section StdSlots

variable {ch : AdmissibleChoice P0} {S : Relation P0}

def pick {α : Type} (p : α → Prop) : Option {a // p a} :=
  @dite _ (∃ a, p a) (Classical.propDecidable _) (fun h => some ⟨h.choose, h.choose_spec⟩)
    (fun _ => none)

lemma pick_isSome {α : Type} {p : α → Prop} (h : ∃ a, p a) : (pick p).isSome := by
  unfold pick
  rw [dif_pos h]
  rfl

def lightTestOf (forms : FormMatrix P0) (f : Exposure.Coeff (ppOf ch S)) :
    Option (Bounds ch S .light) :=
  if h : LightCmp (ppOf ch S) forms f then
    some (.light forms h.choose h.choose_spec.choose h.choose_spec.choose_spec.2)
  else none

def fieldTestOf (forms : FormMatrix P0) (e : Collision (ppOf ch S)) (r : Vec k P0.N) :
    Option (Bounds ch S .field) :=
  match e.sort with
  | .g₁ =>
      (pick fun E : Expr1 P0 => e.value = Exposure.value1 (ppOf ch S) E ∧
          ¬ FormalEq1 (ppOf ch S) E 0).map fun E => .source1 E.1 0 r E.2.2
  | .g₂ =>
      (pick fun E : Expr2 P0 => e.value = Exposure.value2 (ppOf ch S) (formVec forms) E ∧
          ¬ FormalEq2 (ppOf ch S) (formVec forms) E 0).map fun E => .source2 forms E.1 0 r E.2.2
  | .gₜ =>
      (pick fun Dι : ExprT P0 × k =>
          e.value = Exposure.valueT (ppOf ch S) (formVec forms) Dι.1 -
            Dι.2 • Exposure.valueKey (ppOf ch S) ∧
          ¬ IdentityAtR (ppOf ch S) (formVec forms) r Dι.1 Dι.2).map fun Dι =>
        .field forms Dι.1.1 Dι.1.2 r Dι.2.2

def lightSlot (pad : Bounds ch S .light)
    (fires : Record (ppOf ch S) → Option (Bounds ch S .light)) : FactorSlot ch S .light where
  Context := Bounds ch S .light
  test := id
  pad := pad
  fires := fun r => (fires r).map fun t _ => t
  draw := fun a c _ => match a with
    | .light .. => pure c.val.2.1

def fieldSlot (pad : Bounds ch S .field)
    (fires : Record (ppOf ch S) → Option (SearchSample P0 → Bounds ch S .field)) :
    FactorSlot ch S .field where
  Context := Bounds ch S .field
  test := id
  pad := pad
  fires := fires
  draw := fun a c _ => match a with
    | .field .. => resample (ppOf ch S) c
    | .source1 .. => resample (ppOf ch S) c
    | .source2 .. => resample (ppOf ch S) c

def nCoin : ℕ := Fintype.card (View.CoinVar P0)

def coinIdx : View.CoinVar P0 ≃ Fin nCoin := Fintype.equivFin _

def encode (c : Coins P0) (x : ℕ → k) : ℕ → k :=
  fun j => if h : j < nCoin then View.coinVar c (coinIdx.symm ⟨j, h⟩) else x (j - nCoin)

def decodeCoins (s : SearchSample P0) (y : ℕ → k) : Coins P0 :=
  (fun i => y (coinIdx (.inl i)), s, fun sc => y (coinIdx (.inr sc)))

def stdPool (pp : PublicParams P0) (r : Record pp) (s : SearchSample P0) :
    ℕ → (ℕ → k) → Finset k :=
  fun j y => if h : j < nCoin then View.sampleSet pp.qap (coinIdx.symm ⟨j, h⟩)
    else if hv : ValidCoins pp.qap (decodeCoins s y) then
      guessPool pp r ⟨decodeCoins s y, hv⟩ (j - nCoin) (fun t => y (nCoin + t))
    else Finset.univ

def StdGuess (pp : PublicParams P0) (r : Record pp) (s : SearchSample P0) (t : GuessTest) :
    Prop :=
  t.nc = nCoin ∧ t.ng = r.order.length ∧ t.pool = stdPool pp r s

def guessSlot (pad : SearchSample P0 × Bounds ch S .guess)
    (fires : Record (ppOf ch S) → Option (SearchSample P0 → Bounds ch S .guess)) :
    FactorSlot ch S .guess where
  Context := SearchSample P0 × Bounds ch S .guess
  test := Prod.snd
  pad := pad
  fires := fun r => (fires r).map fun f s => (s, f s)
  draw := fun a c x => match a with
    | (_, .guess _) => pure (encode c.val x)

end StdSlots

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold
