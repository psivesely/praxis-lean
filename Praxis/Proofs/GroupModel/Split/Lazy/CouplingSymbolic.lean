import Praxis.Proofs.GroupModel.Split.Lazy.CouplingInitial
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.Coupling
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 4096

namespace Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

open Classical

lemma decodeLabel_eq_some_iff {p n : ℕ} (τ : ZMod p ↪ BitVec n)
    (t : BitVec n) (v : ZMod p) : Algebra.decodeLabel τ t = some v ↔ τ v = t := by
  unfold Algebra.decodeLabel
  constructor
  · intro h
    split at h
    · next hex =>
        have hv : hex.choose = v := Option.some.inj h
        rw [← hv]
        exact hex.choose_spec
    · simp at h
  · intro h
    have hex : ∃ x, τ x = t := ⟨v, h⟩
    rw [dif_pos hex]
    exact congrArg some (τ.injective (hex.choose_spec.trans h.symm))

abbrev GuessVar := GroupModel.Sorted.PSort × Label P0

abbrev CoinDomain (pp : PublicParams P0) := {c : Coins P0 // ValidCoins pp.qap c}

abbrev Coeff (pp : PublicParams P0) := Exposure.Coeff pp

abbrev Poly (pp : PublicParams P0) := MvPolynomial GuessVar (Coeff pp)

def base1 (pp : PublicParams P0) (E : Expr1 P0) : Poly pp :=
  MvPolynomial.C (fun ω => val1 pp ω.val E)

def base2 (pp : PublicParams P0) (A : FormMatrix P0)
    (E : Expr2 P0) : Poly pp :=
  MvPolynomial.C (fun ω => val2 pp (formVec A) ω.val E)

def baseT (pp : PublicParams P0) (A : FormMatrix P0)
    (E : ExprT P0) : Poly pp :=
  MvPolynomial.C (fun ω => valT pp (formVec A) ω.val E)

def scalar (pp : PublicParams P0) (a : k) : Poly pp := MvPolynomial.C (fun _ => a)

def key (pp : PublicParams P0) : Poly pp := MvPolynomial.C (fun ω => kappa pp ω.val.coins)

def atCoin (pp : PublicParams P0) (c : CoinDomain pp) : Coeff pp →+* k where
  toFun f := f ⟨Assign.ofCoins c.val, c.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def evaluate (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp) :
    Poly pp →+* k :=
  MvPolynomial.eval₂Hom (atCoin pp c) (fun v => (Algebra.decodeLabel (σ v.1) v.2).getD 0)

lemma evaluate_guess (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (x : k)
    (hx : Algebra.decodeLabel (σ s) l = some x) :
    evaluate pp σ c (MvPolynomial.X (s, l)) = x := by simp [evaluate, hx]

abbrev Dict (pp : PublicParams P0) := GroupModel.Sorted.PSort → Label P0 → Option (Poly pp)

def record (pp : PublicParams P0) (d : Dict pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) : Dict pp := by
  classical
  exact Function.update d s (Function.update (d s) l (some P))

lemma record_same (pp : PublicParams P0) (d : Dict pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) : record pp d s l P s l = some P := by
  classical
  simp [record]

structure Collision (pp : PublicParams P0) where
  sort : GroupModel.Sorted.PSort
  label : Label P0
  new : Poly pp
  old : Poly pp

structure State (pp : PublicParams P0) where
  dict : Dict pp
  guesses : Finset GuessVar
  excluded : GroupModel.Sorted.PSort → Finset (Label P0)
  first : Option (Collision pp)

def empty (pp : PublicParams P0) : State pp := ⟨fun _ _ => none, ∅, fun _ => ∅, none⟩

def resolve (pp : PublicParams P0) (σ : LabelEncoding P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) : Option (Poly pp) × State pp := by
  classical
  exact match st.dict s l with
  | some P => (some P, st)
  | none => match Algebra.decodeLabel (σ s) l with
    | none => (none, {st with excluded := Function.update st.excluded s (insert l (st.excluded s))})
    | some _ =>
      let P : Poly pp := MvPolynomial.X (s, l)
      (some P, {st with dict := record pp st.dict s l P, guesses := insert (s, l) st.guesses})

def insertResult (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) : State pp := by
  classical
  exact match st.dict s l with
  | none => {st with dict := record pp st.dict s l P}
  | some Q => if P = Q then st else
      {st with first := st.first.orElse (fun _ => some ⟨s, l, P, Q⟩)}

def Faithful (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) : Prop :=
  ∀ s l P, st.dict s l = some P → σ s (evaluate pp σ c P) = l

def IsCollision (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (e : Collision pp) : Prop :=
  e.new ≠ e.old ∧ evaluate pp σ c e.new = evaluate pp σ c e.old ∧
    σ e.sort (evaluate pp σ c e.new) = e.label

lemma resolve_known (pp : PublicParams P0) (σ : LabelEncoding P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (h : st.dict s l = some P) : resolve pp σ st s l = (some P, st) := by
  simp [resolve, h]

lemma insertResult_first_of_new (pp : PublicParams P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P Q : Poly pp)
    (h : st.dict s l = some Q) (hne : P ≠ Q) (hf : st.first = none) :
    (insertResult pp st s l P).first = some ⟨s, l, P, Q⟩ := by
  simp [insertResult, h, hne, hf]

lemma insertResult_collision (pp : PublicParams P0) (σ : LabelEncoding P0)
    (c : CoinDomain pp) (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) (hs : Faithful pp σ c st) (hv : σ s (evaluate pp σ c P) = l)
    (hf : st.first = none) (e : Collision pp)
    (he : (insertResult pp st s l P).first = some e) : IsCollision pp σ c e := by
  classical
  unfold insertResult at he
  split at he
  · simp [hf] at he
  · rename_i Q hQ
    split at he
    · simp [hf] at he
    · rename_i hne
      simp only [hf, Option.orElse_none, Option.some.injEq] at he
      cases he
      exact ⟨hne, (σ s).injective (hv.trans (hs s l Q hQ).symm), hv⟩

lemma record_faithful (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hs : Faithful pp σ c st) (hv : σ s (evaluate pp σ c P) = l) :
    Faithful pp σ c {st with dict := record pp st.dict s l P} := by
  classical
  intro s' l' Q hQ
  by_cases hss : s' = s
  · subst s'
    by_cases hll : l' = l
    · subst l'
      have he : P = Q := Option.some.inj (by simpa [record] using hQ)
      simpa [← he] using hv
    · exact hs s l' Q (by simpa [record, hll] using hQ)
  · exact hs s' l' Q (by simpa [record, hss] using hQ)

lemma resolve_faithful (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (hs : Faithful pp σ c st) : Faithful pp σ c (resolve pp σ st s l).2 := by
  classical
  unfold resolve
  split
  · exact hs
  · split
    · exact hs
    · rename_i x hx
      apply record_faithful pp σ c st s l _ hs
      rw [evaluate_guess pp σ c s l x hx]
      exact (decodeLabel_eq_some_iff _ _ _).mp hx

lemma resolve_value (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hs : Faithful pp σ c st) (hP : (resolve pp σ st s l).1 = some P) :
    Algebra.decodeLabel (σ s) l = some (evaluate pp σ c P) := by
  classical
  unfold resolve at hP
  split at hP
  · rename_i Q hQ
    cases Option.some.inj hP
    exact (decodeLabel_eq_some_iff _ _ _).mpr (hs s l P hQ)
  · split at hP
    · simp at hP
    · rename_i x hx
      cases Option.some.inj hP
      rw [evaluate_guess pp σ c s l x hx]
      exact hx

lemma resolve_first (pp : PublicParams P0) (σ : LabelEncoding P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) :
    (resolve pp σ st s l).2.first = st.first := by
  classical
  unfold resolve
  split
  · rfl
  · split <;> rfl

lemma insertResult_faithful (pp : PublicParams P0) (σ : LabelEncoding P0)
    (c : CoinDomain pp) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) (hs : Faithful pp σ c st)
    (hv : σ s (evaluate pp σ c P) = l) :
    Faithful pp σ c (insertResult pp st s l P) := by
  classical
  unfold insertResult
  split
  · exact record_faithful pp σ c st s l P hs hv
  · split <;> exact hs

lemma insertResult_eq_of_no_collision (pp : PublicParams P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P Q : Poly pp)
    (hQ : st.dict s l = some Q) (hf : (insertResult pp st s l P).first = none) : P = Q := by
  classical
  by_contra hne
  simp only [insertResult, hQ, if_neg hne] at hf
  cases st.first <;> simp at hf

lemma evaluate_scalar (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (a : k) : evaluate pp σ c (scalar pp a) = a := by
  simp [evaluate, scalar, atCoin]

def Sound (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) : Prop :=
  Faithful pp σ c st ∧ ∀ e, st.first = some e → IsCollision pp σ c e

lemma resolve_sound (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (hs : Sound pp σ c st) : Sound pp σ c (resolve pp σ st s l).2 := by
  refine ⟨resolve_faithful pp σ c st s l hs.1, ?_⟩
  intro e he
  rw [resolve_first] at he
  exact hs.2 e he

lemma insertResult_retains_first (pp : PublicParams P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp) (e : Collision pp)
    (he : st.first = some e) : (insertResult pp st s l P).first = some e := by
  classical
  unfold insertResult
  split
  · exact he
  · split
    · exact he
    · simp [he]

lemma insertResult_sound (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hs : Sound pp σ c st) (hv : σ s (evaluate pp σ c P) = l) :
    Sound pp σ c (insertResult pp st s l P) := by
  refine ⟨insertResult_faithful pp σ c st s l P hs.1 hv, ?_⟩
  intro e he
  cases hf : st.first with
  | none => exact insertResult_collision pp σ c st s l P hs.1 hv hf e he
  | some e' =>
    have he' := insertResult_retains_first pp st s l P e' hf
    have heq := Option.some.inj (he.symm.trans he')
    exact heq ▸ hs.2 e' hf

lemma otherLabel_name (σ : k ↪ Label P0) (x : k) :
    otherLabel (σ x) (labelName σ x) = σ (-x) := by
  simp [otherLabel, labelName]

def observeGroup (pp : PublicParams P0) (σ : LabelEncoding P0) (st : State pp)
    (q : GQuery P0) (answer : q.Result) : State pp :=
  match q with
  | .lin s a b u v =>
    let x := resolve pp σ st s u
    let y := resolve pp σ x.2 s v
    match x.1, y.1, answer with
    | some P, some Q, some l => insertResult pp y.2 s l (scalar pp a * P + scalar pp b * Q)
    | _, _, _ => y.2
  | .pair u v =>
    let x := resolve pp σ st .g₁ u
    let y := resolve pp σ x.2 .g₂ v
    match x.1, y.1, answer with
    | some P, some Q, some l => insertResult pp y.2 .gₜ l (P * Q)
    | _, _, _ => y.2
  | .name u =>
    match answer with
    | none => st
    | some nm => insertResult pp st .gₜ (otherLabel u nm) (-((st.dict .gₜ u).getD 0))

lemma observeGroup_sound (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (st : State pp) (issued : Finset (Label P0)) (q : GQuery P0)
    (hs : Sound pp σ c st)
    (hissued : ∀ l ∈ issued, ∃ P, st.dict .gₜ l = some P) :
    Sound pp σ c (observeGroup pp σ st q (groupAnswer σ issued q)) := by
  classical
  cases q with
  | lin s a b u v =>
    let x := resolve pp σ st s u
    let y := resolve pp σ x.2 s v
    have hx := resolve_sound pp σ c st s u hs
    have hy := resolve_sound pp σ c x.2 s v hx
    change Sound pp σ c (match x.1, y.1, groupAnswer σ issued (.lin s a b u v) with
      | some P, some Q, some l => insertResult pp y.2 s l (scalar pp a * P + scalar pp b * Q)
      | _, _, _ => y.2)
    cases hp : x.1 with
    | none => simpa [hp] using hy
    | some P =>
      cases hq : y.1 with
      | none => simpa [hp, hq] using hy
      | some Q =>
        have hu := resolve_value pp σ c st s u P hs.1 hp
        have hv := resolve_value pp σ c x.2 s v Q hx.1 hq
        have hr : groupAnswer σ issued (.lin s a b u v) =
            some (σ s (a * evaluate pp σ c P + b * evaluate pp σ c Q)) := by
          simp [groupAnswer, hu, hv]
        rw [hr]
        apply insertResult_sound pp σ c y.2 s _ _ hy
        rw [map_add, map_mul, map_mul, evaluate_scalar, evaluate_scalar]
  | pair u v =>
    let x := resolve pp σ st .g₁ u
    let y := resolve pp σ x.2 .g₂ v
    have hx := resolve_sound pp σ c st .g₁ u hs
    have hy := resolve_sound pp σ c x.2 .g₂ v hx
    change Sound pp σ c (match x.1, y.1, groupAnswer σ issued (.pair u v) with
      | some P, some Q, some l => insertResult pp y.2 .gₜ l (P * Q)
      | _, _, _ => y.2)
    cases hp : x.1 with
    | none => simpa [hp] using hy
    | some P =>
      cases hq : y.1 with
      | none => simpa [hp, hq] using hy
      | some Q =>
        have hu := resolve_value pp σ c st .g₁ u P hs.1 hp
        have hv := resolve_value pp σ c x.2 .g₂ v Q hx.1 hq
        have hr : groupAnswer σ issued (.pair u v) =
            some (σ .gₜ (evaluate pp σ c P * evaluate pp σ c Q)) := by
          simp [groupAnswer, hu, hv]
        rw [hr]
        apply insertResult_sound pp σ c y.2 .gₜ _ _ hy
        rw [map_mul]
  | name u =>
    by_cases hi : u ∈ issued
    · obtain ⟨P, hP⟩ := hissued u hi
      have hu : Algebra.decodeLabel (σ .gₜ) u = some (evaluate pp σ c P) :=
        (decodeLabel_eq_some_iff _ _ _).mpr (hs.1 .gₜ u P hP)
      have hr : groupAnswer σ issued (.name u) = some (labelName (σ .gₜ) (evaluate pp σ c P)) := by
        simp [groupAnswer, hi, hu]
      simp only [observeGroup, hr, hP, Option.getD_some]
      apply insertResult_sound pp σ c st .gₜ _ _ hs
      rw [map_neg, ← hs.1 .gₜ u P hP, otherLabel_name]
    · simpa [observeGroup, groupAnswer, hi] using hs

lemma evaluate_key (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp) :
    evaluate pp σ c (key pp) = kappa pp c.val := by simp [evaluate, key, atCoin, Assign.ofCoins]

def initialEntries (pp : PublicParams P0) (A : FormMatrix P0)
    (pv : PubView P0) : List (GroupModel.Sorted.PSort × Label P0 × Poly pp) :=
  pv.g1.map (fun e => (.g₁, e.2, base1 pp (Pi.single e.1 1))) ++
    pv.g2.map (fun e => (.g₂, e.2, base2 pp A (Pi.single e.1 1))) ++
    pv.gT.map (fun e => (.gₜ, e.2, baseT pp A (gtInit e.1)))

def initialise (pp : PublicParams P0) (A : FormMatrix P0)
    (pv : PubView P0) : State pp :=
  (initialEntries pp A pv).foldl
    (fun st e => insertResult pp st e.1 e.2.1 e.2.2) (empty pp)

lemma evaluate_base1 (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (E : Expr1 P0) :
    evaluate pp σ c (base1 pp E) = val1 pp (Assign.ofCoins c.val) E := by
  simp [evaluate, base1, atCoin]

lemma evaluate_base2 (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (A : FormMatrix P0) (E : Expr2 P0) :
    evaluate pp σ c (base2 pp A E) = val2 pp (formVec A) (Assign.ofCoins c.val) E := by
  simp [evaluate, base2, atCoin]

lemma evaluate_baseT (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (A : FormMatrix P0) (E : ExprT P0) :
    evaluate pp σ c (baseT pp A E) = valT pp (formVec A) (Assign.ofCoins c.val) E := by
  simp [evaluate, baseT, atCoin]

lemma e2At_real (pp : PublicParams P0) (A : FormMatrix P0) (c : Coins P0)
    (i : Option (G2Idx P0)) :
    e2At pp (formVec A) (Assign.ofCoins c) i =
      (match i with | none => 1 | some j => g2Exp pp (formVec A) c j) := by
  cases i with
  | none => rfl
  | some i => cases i <;> rfl

lemma initialEntries_real (pp : PublicParams P0) (σ : LabelEncoding P0)
    (c : CoinDomain pp) (A : FormMatrix P0)
    (e : GroupModel.Sorted.PSort × Label P0 × Poly pp)
    (he : e ∈ initialEntries pp A (pubView σ pp (formVec A) c.val)) :
    σ e.1 (evaluate pp σ c e.2.2) = e.2.1 := by
  classical
  simp only [initialEntries, List.mem_append, List.mem_map] at he
  rcases he with (⟨e', he', rfl⟩ | ⟨e', he', rfl⟩) | ⟨e', he', rfl⟩
  · rw [evaluate_base1, val1_single]
    rcases List.mem_cons.mp he' with he' | he'
    · cases he'; simp [e1At, Assign.ofCoins]
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he'
      simp [e1At, Assign.ofCoins]
  · rw [evaluate_base2, val2_single, e2At_real]
    rcases List.mem_cons.mp he' with he' | he'
    · cases he'; simp
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he'
      simp
  · rw [evaluate_baseT, valT_gtInit]
    simp only [pubView, List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl <;> rfl

lemma fold_insert_sound (pp : PublicParams P0) (σ : LabelEncoding P0) (c : CoinDomain pp)
    (entries : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp)
    (hs : Sound pp σ c st)
    (hv : ∀ e ∈ entries, σ e.1 (evaluate pp σ c e.2.2) = e.2.1) :
    Sound pp σ c (entries.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st) := by
  induction entries generalizing st with
  | nil => exact hs
  | cons e es ih =>
    apply ih _ (insertResult_sound pp σ c st _ _ _ hs (hv e (by simp)))
    exact fun f hf => hv f (List.mem_cons_of_mem e hf)

lemma initialise_sound (pp : PublicParams P0) (σ : LabelEncoding P0)
    (c : CoinDomain pp) (A : FormMatrix P0) :
    Sound pp σ c (initialise pp A (pubView σ pp (formVec A) c.val)) := by
  apply fold_insert_sound
  · constructor
    · intro s l P h; simp [empty] at h
    · intro e h; simp [empty] at h
  · exact initialEntries_real pp σ c A

def labelOf (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (P : Poly pp) : Option (Label P0) := by
  classical
  exact if h : ∃ l, st.dict s l = some P then some h.choose else none

lemma labelOf_some (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (P : Poly pp) (l : Label P0) (h : labelOf pp st s P = some l) : st.dict s l = some P := by
  classical
  unfold labelOf at h
  split at h
  · rename_i hex
    cases Option.some.inj h
    exact hex.choose_spec
  · simp at h

lemma labelOf_none (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (P : Poly pp) (h : labelOf pp st s P = none) : ∀ l, st.dict s l ≠ some P := by
  classical
  unfold labelOf at h
  split at h
  · simp at h
  · rename_i hn
    exact fun l hl => hn ⟨l, hl⟩

def genericResolve (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (valid : Bool) : Option (Poly pp) × State pp := by
  classical
  exact match st.dict s l with
  | some P => (some P, st)
  | none => if valid then
      let P : Poly pp := MvPolynomial.X (s, l)
      (some P, {st with dict := record pp st.dict s l P, guesses := insert (s, l) st.guesses})
    else (none, {st with excluded := Function.update st.excluded s (insert l (st.excluded s))})

def genericInsert (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (P : Poly pp) (fresh : Label P0) : Label P0 × State pp :=
  match labelOf pp st s P with
  | some l => (l, st)
  | none => (fresh, {st with dict := record pp st.dict s fresh P})

lemma insertResult_of_same (pp : PublicParams P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (P : Poly pp) (l : Label P0)
    (hd : st.dict s l = some P) : insertResult pp st s l P = st := by
  unfold insertResult
  simp [hd]

lemma insertResult_of_none (pp : PublicParams P0) (st : State pp)
    (s : GroupModel.Sorted.PSort) (P : Poly pp) (l : Label P0)
    (hd : st.dict s l = none) :
    insertResult pp st s l P = {st with dict := record pp st.dict s l P} := by
  simp only [insertResult, hd]

def assigned (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort) :
    Finset (Label P0) := by classical exact Finset.univ.filter fun l => (st.dict s l).isSome

def available (pp : PublicParams P0) (st : State pp) (s : GroupModel.Sorted.PSort) :
    Finset (Label P0) := Finset.univ \ (assigned pp st s ∪ st.excluded s)

def referenceResolve (pp : PublicParams P0) (s : GroupModel.Sorted.PSort) (l : Label P0) :
    StateT (State pp) ProbComp (Option (Poly pp)) := do
  let st ← get
  match st.dict s l with
  | some P => pure (some P)
  | none =>
    if l ∈ st.excluded s then pure none else do
      let u ← StateT.lift ($[0..(2 ^ P0.labelBits - (assigned pp st s).card - (st.excluded s).card - 1)])
      let z := genericResolve pp st s l (u.val < P0.q - (assigned pp st s).card)
      set z.2
      pure z.1

def referenceInsert (pp : PublicParams P0) (s : GroupModel.Sorted.PSort) (P : Poly pp) :
    StateT (State pp) ProbComp (Label P0) := do
  let st ← get
  match labelOf pp st s P with
  | some l => pure l
  | none =>
    let l ← StateT.lift (uniform (available pp st s))
    set {st with dict := record pp st.dict s l P}
    pure l

def referenceGroup (pp : PublicParams P0) (issued : Finset (Label P0)) :
    (q : GQuery P0) → StateT (State pp) ProbComp q.Result
  | .lin s a b u v => do
    let x ← referenceResolve pp s u
    let y ← referenceResolve pp s v
    match x, y with
    | some P, some Q => some <$> referenceInsert pp s (scalar pp a * P + scalar pp b * Q)
    | _, _ => pure none
  | .pair u v => do
    let x ← referenceResolve pp .g₁ u
    let y ← referenceResolve pp .g₂ v
    match x, y with
    | some P, some Q => some <$> referenceInsert pp .gₜ (P * Q)
    | _, _ => pure none
  | .name u => do
    if u ∈ issued then
      match (← get).dict .gₜ u with
      | none => pure none
      | some P =>
        let neg ← referenceInsert pp .gₜ (-P)
        pure (some s(u, neg))
    else pure none

def finishGroup (q : GQuery P0) (answer : q.Result) : GameM P0 q.Answer := do
  match trEntry q answer with
  | none => pure ()
  | some e => modify fun st => {st with tr := st.tr ++ [e], issuedT :=
      match e.issuedGT with | none => st.issuedT | some l => insert l st.issuedT}
  handOut q answer

def referenceInitial (pp : PublicParams P0) (A : FormMatrix P0) :
    StateT (State pp) ProbComp (PubView P0) := do
  let g1 ← (keys1 P0).mapM fun i => do
    let l ← referenceInsert pp .g₁ (base1 pp (Pi.single i 1))
    pure (i, l)
  let g2 ← (keys2 P0).mapM fun i => do
    let l ← referenceInsert pp .g₂ (base2 pp A (Pi.single i 1))
    pure (i, l)
  let gt ← ([none, some ()] : List (Option Unit)).mapM fun i => do
    let l ← referenceInsert pp .gₜ (baseT pp A (gtInit i))
    pure (i, l)
  pure ⟨g1, g2, gt⟩

end Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic
