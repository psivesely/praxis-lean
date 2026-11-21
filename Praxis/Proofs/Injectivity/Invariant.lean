import Praxis.Proofs.Injectivity.Projections
import Praxis.Proofs.Injectivity.Invariants
import Praxis.Extractor
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra

variable {P : Params}

def AgreeT (sk : Sketches P) (is : IdealState P) (es : ExState P) : Prop :=
  ∀ l, es.dT l = (is.dT l).map (fun D => sketchesOf D sk) ∨
    (es.dT l = none ∧ is.dT l = some 0)

structure Agree (sk : Sketches P) (is : IdealState P) (es : ExState P) : Prop where
  d1 : ∀ l, es.d1 l = (is.d1 l).map proj1
  d2 : ∀ l, es.d2 l = (is.d2 l).map (proj2 sk)
  dT : AgreeT sk is es
  named : es.named = is.named

variable [Fact (Nat.Prime P.q)]

def Quiet (S : Relation P) (sk : Sketches P) (is : IdealState P) : Prop :=
  ∀ l E, is.dT l = some E → testExpr S (sketchesOf E sk) = none

def CheckedMark (S : Relation P) (sk : Sketches P) (is : IdealState P) : Prop :=
  ∀ k D i, is.mark = some k → k.data = some (D, i) → testExpr S (sketchesOf D sk) = none

def Tracked (S : Relation P) (sk : Sketches P) (is : IdealState P) (es : ExState P) : Prop :=
  (is.mark = none → Agree sk is es ∧ Quiet S sk is) ∧ CheckedMark S sk is

open Classical

theorem ideal1_shape (cx : IdealCtx P) (k : Mark P) (st : IdealState P) (l : Label P) (F : Expr1 P) :
    ideal1 cx k st l F =
      { st with d1 := keepEarliest st.d1 l F
                mark := (match st.d1 l with
          | none => st.mark
          | some E => if cx.eq1 F E then st.mark else some k) } := by
  cases ht : st.d1 l with
  | none => simp only [ideal1, keepEarliest, ht]
  | some E =>
    by_cases h : cx.eq1 F E <;> simp only [ideal1, keepEarliest, ht, h, ↓reduceIte]

theorem ideal2_shape (cx : IdealCtx P) (k : Mark P) (st : IdealState P) (l : Label P) (F : Expr2 P) :
    ideal2 cx k st l F =
      { st with d2 := keepEarliest st.d2 l F
                mark := (match st.d2 l with
          | none => st.mark
          | some E => if cx.eq2 F E then st.mark else some k) } := by
  cases ht : st.d2 l with
  | none => simp only [ideal2, keepEarliest, ht]
  | some E =>
    by_cases h : cx.eq2 F E <;> simp only [ideal2, keepEarliest, ht, h, ↓reduceIte]

theorem idealT_shape (cx : IdealCtx P) (initial : Bool) (st : IdealState P) (l : Label P) (F : ExprT P) :
    idealT cx initial st l F =
      { st with dT := keepEarliest st.dT l F
                mark := (match st.dT l with
          | none => st.mark
          | some E => if cx.eqT F E then st.mark else some (if initial then .init else .diff (F - E))) } := by
  cases ht : st.dT l with
  | none => simp only [idealT, keepEarliest, ht]
  | some E =>
    by_cases h : cx.eqT F E <;> simp only [idealT, keepEarliest, ht, h, ↓reduceIte]

theorem Agree.put1 {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (l : Label P) (F : Expr1 P) (m : Option (Mark P)) :
    Agree sk { is with d1 := keepEarliest is.d1 l F, mark := m }
      { es with d1 := keepEarliest es.d1 l (proj1 F) } := by
  constructor
  · intro j
    have hd : es.d1 = fun j => (is.d1 j).map proj1 := funext h.d1
    change keepEarliest es.d1 l (proj1 F) j = ((keepEarliest is.d1 l F) j).map proj1
    rw [hd, ← map_keepEarliest]
  · exact h.d2
  · exact h.dT
  · exact h.named

theorem Agree.put2 {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (l : Label P) (F : Expr2 P) (m : Option (Mark P)) :
    Agree sk { is with d2 := keepEarliest is.d2 l F, mark := m }
      { es with d2 := keepEarliest es.d2 l (proj2 sk F) } := by
  constructor
  · exact h.d1
  · intro j
    have hd : es.d2 = fun j => (is.d2 j).map (proj2 sk) := funext h.d2
    change keepEarliest es.d2 l (proj2 sk F) j = ((keepEarliest is.d2 l F) j).map (proj2 sk)
    rw [hd, ← map_keepEarliest]
  · exact h.dT
  · exact h.named

theorem keepEarliest_other {X : Type*} (t : Label P → Option X) (l j : Label P) (F : X)
    (hj : j ≠ l) : keepEarliest t l F j = t j := by
  cases ht : t l <;> simp [keepEarliest, ht, Function.update_of_ne hj]

theorem Agree.putT {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (l : Label P) (F : ExprT P) (m : Option (Mark P)) (found : Option (Vec (Fq P) P.N))
    (hzero : is.dT l = some 0 → sketchesOf F sk = 0) :
    Agree sk { is with dT := keepEarliest is.dT l F, mark := m }
      { es with dT := keepEarliest es.dT l (sketchesOf F sk), found := found } := by
  constructor
  · exact h.d1
  · exact h.d2
  · intro j
    change keepEarliest es.dT l (sketchesOf F sk) j =
        (keepEarliest is.dT l F j).map (fun D => sketchesOf D sk) ∨
      (keepEarliest es.dT l (sketchesOf F sk) j = none ∧ keepEarliest is.dT l F j = some 0)
    by_cases hj : j = l
    · subst j
      apply Or.inl
      rcases h.dT l with he | ⟨he, hi⟩
      · cases ht : is.dT l <;> simp [keepEarliest, ht, he]
      · simp [keepEarliest, he, hi, hzero hi]
    · simpa only [keepEarliest_other _ _ _ _ hj] using h.dT j
  · exact h.named

theorem Agree.recordT {sk : Sketches P} {is : IdealState P} {es : ExState P}
    (h : Agree sk is es) (u v : Label P) : Agree sk (recordT is u v) es := by
  refine ⟨h.d1, h.d2, ?_, h.named⟩
  intro j
  change es.dT j = (if (j = u ∨ j = v) ∧ (is.dT j).isNone then some 0 else is.dT j).map
      (fun D => sketchesOf D sk) ∨
    (es.dT j = none ∧ (if (j = u ∨ j = v) ∧ (is.dT j).isNone then some 0 else is.dT j) = some 0)
  split_ifs with hr
  · have hi : is.dT j = none := Option.isNone_iff_eq_none.mp hr.2
    rcases h.dT j with he | ⟨he, _⟩
    · exact Or.inr ⟨by simpa [hi] using he, rfl⟩
    · exact Or.inr ⟨he, rfl⟩
  · exact h.dT j

theorem stored_keep {X : Type*} (t : Label P → Option X) (l j : Label P) (F E : X)
    (h : keepEarliest t l F j = some E) : t j = some E ∨ E = F := by
  unfold keepEarliest at h
  cases ht : t l with
  | some A => simp only [ht] at h; exact Or.inl h
  | none =>
    simp only [ht] at h
    by_cases hj : j = l
    · subst j; simp only [Function.update_self, Option.some.injEq] at h; exact Or.inr h.symm
    · exact Or.inl (by simpa [Function.update_of_ne hj] using h)

theorem Quiet.putT {S : Relation P} {sk : Sketches P} {is : IdealState P}
    (h : Quiet S sk is) (l : Label P) (F : ExprT P) (m : Option (Mark P))
    (hF : testExpr S (sketchesOf F sk) = none) :
    Quiet S sk { is with dT := keepEarliest is.dT l F, mark := m } := by
  intro j E he
  rcases stored_keep is.dT l j F E he with he | rfl
  · exact h j E he
  · exact hF

theorem Quiet.recordT {S : Relation P} {sk : Sketches P} {is : IdealState P}
    (h : Quiet S sk is) (u v : Label P) : Quiet S sk (recordT is u v) := by
  intro j E he
  change (if (j = u ∨ j = v) ∧ (is.dT j).isNone then some 0 else is.dT j) = some E at he
  split_ifs at he with hr
  · cases he
    simp
  · exact h j E he

theorem agree_ideal1 {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (cx : IdealCtx P) (k : Mark P) (l : Label P) (F : Expr1 P) :
    Agree sk (ideal1 cx k is l F) { es with d1 := keepEarliest es.d1 l (proj1 F) } := by
  rw [ideal1_shape]
  exact h.put1 l F _

theorem agree_ideal2 {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (cx : IdealCtx P) (k : Mark P) (l : Label P) (F : Expr2 P) :
    Agree sk (ideal2 cx k is l F) { es with d2 := keepEarliest es.d2 l (proj2 sk F) } := by
  rw [ideal2_shape]
  exact h.put2 l F _

theorem checked_ideal1 (S : Relation P) (sk : Sketches P) (cx : IdealCtx P) (k : Mark P)
    (is : IdealState P) (l : Label P) (F : Expr1 P) (hm : is.mark = none) (hk : k.data = none) :
    CheckedMark S sk (ideal1 cx k is l F) := by
  unfold ideal1
  cases ht : is.d1 l with
  | none => simp [CheckedMark, hm]
  | some E =>
    simp only [ht]
    split <;> simp_all [CheckedMark]
    intro k' a b i hkk hd
    subst k'
    rw [hk] at hd
    cases hd

theorem checked_ideal2 (S : Relation P) (sk : Sketches P) (cx : IdealCtx P) (k : Mark P)
    (is : IdealState P) (l : Label P) (F : Expr2 P) (hm : is.mark = none) (hk : k.data = none) :
    CheckedMark S sk (ideal2 cx k is l F) := by
  unfold ideal2
  cases ht : is.d2 l with
  | none => simp [CheckedMark, hm]
  | some E =>
    simp only [ht]
    split <;> simp_all [CheckedMark]
    intro k' a b i hkk hd
    subst k'
    rw [hk] at hd
    cases hd

theorem agree_quiet_idealT (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (es : ExState P) (l : Label P) (F : ExprT P)
    (ha : Agree sk is es) (hq : Quiet S sk is)
    (hf : (gtStep S es (sketchesOf F sk) l).found = none) (initial : Bool)
    (hzero : ∀ F, cx.eqT F 0 → sketchesOf F sk = 0)
    (hn : (idealT cx initial is l F).mark = none) :
    Agree sk (idealT cx initial is l F) (gtStep S es (sketchesOf F sk) l) ∧
      Quiet S sk (idealT cx initial is l F) := by
  have ht := (gtStep_failed S es (sketchesOf F sk) l hf).1
  rw [idealT_shape]
  refine ⟨ha.putT l F _ _ ?_, hq.putT l F _ ht⟩
  intro hi
  apply hzero F
  by_contra hne
  simp [idealT, hi, hne] at hn

theorem checked_idealT (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (es : ExState P) (l : Label P) (F : ExprT P)
    (ha : Agree sk is es) (hm : is.mark = none)
    (hf : (gtStep S es (sketchesOf F sk) l).found = none) (initial : Bool) :
    CheckedMark S sk (idealT cx initial is l F) := by
  intro k D i hk hd
  unfold idealT at hk
  cases ht : is.dT l with
  | none => simp [ht, hm] at hk
  | some E =>
    simp only [ht] at hk
    split at hk
    · simp [hm] at hk
    · cases initial with
      | true => simp [Mark.data] at hk hd; subst k; simp [Mark.data] at hd
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hk
        subst k
        simp only [Mark.data, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        rw [sketches_sub]
        rcases ha.dT l with he | ⟨_, hi⟩
        · exact (gtStep_failed S es (sketchesOf F sk) l hf).2 (sketchesOf E sk)
            (by simpa only [ht, Option.map_some] using he)
        · rw [ht, Option.some.injEq] at hi
          subst E
          simpa only [sketches_zero, sub_zero] using
            (gtStep_failed S es (sketchesOf F sk) l hf).1

end Praxis.Proofs.Injectivity
