import Praxis.Proofs.Basic
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Reduction

namespace Praxis.Proofs.GroupModel

open Classical

open GroupModel.Sorted

variable {P : Params} (cx : IdealCtx P)

private theorem ideal1_mark (st : IdealState P) (l : Label P) (F : Expr1 P)
    (h : st.mark ≠ some .init) : (ideal1 cx .g1 st l F).mark ≠ some .init := by
  unfold ideal1
  split <;> simp_all
  split <;> simp_all

private theorem ideal2_mark (st : IdealState P) (l : Label P) (F : Expr2 P)
    (h : st.mark ≠ some .init) : (ideal2 cx .g2 st l F).mark ≠ some .init := by
  unfold ideal2
  split <;> simp_all
  split <;> simp_all

private theorem idealT_mark (st : IdealState P) (l : Label P) (F : ExprT P)
    (h : st.mark ≠ some .init) : (idealT cx false st l F).mark ≠ some .init := by
  unfold idealT
  split <;> simp_all
  split <;> simp_all

private theorem idealOp_mark (st : IdealState P) (op : TrOp P)
    (h : st.mark ≠ some .init) : (idealOp cx st op).mark ≠ some .init := by
  cases op with
  | lin s a b u v res =>
    cases s <;> simp only [idealOp]
    · exact ideal1_mark cx _ _ _ h
    · exact ideal2_mark cx _ _ _ h
    · exact idealT_mark cx _ _ _ h
  | pair u v res => exact idealT_mark cx _ _ _ h
  | name u res =>
    simp only [idealOp]
    split
    · exact h
    · apply idealT_mark
      exact h

private theorem idealKdf_mark (st : IdealState P) (nm : ClassName P)
    (h : st.mark ≠ some .init) : (idealKdf cx st nm).mark ≠ some .init := by
  unfold idealKdf
  split
  · split
    · simp
    · split <;> simp
  · exact h

private theorem idealEvent_mark (st : IdealState P) (e : MonEvent P)
    (h : st.mark ≠ some .init) : (idealEvent cx st e).mark ≠ some .init := by
  unfold idealEvent
  split
  · exact h
  · cases e with
    | op op => exact idealOp_mark cx st op h
    | kdf nm => exact idealKdf_mark cx st nm h

theorem fold_events_init (st : IdealState P) (es : List (MonEvent P)) :
    (es.foldl (idealEvent cx) st).mark = some .init ↔ st.mark = some .init := by
  constructor
  · intro h
    by_contra hn
    have keep : ∀ (es : List (MonEvent P)) (st : IdealState P),
        st.mark ≠ some .init → (es.foldl (idealEvent cx) st).mark ≠ some .init := by
      intro es
      induction es with
      | nil => intro st hs; exact hs
      | cons e es ih =>
        intro st hs
        exact ih _ (idealEvent_mark cx st e hs)
    exact keep es st hn h
  · intro h
    induction es generalizing st with
    | nil => exact h
    | cons e es ih =>
      apply ih
      simp [idealEvent, h]

theorem firstMark_init_iff [Fact (Nat.Prime P.q)] (pp : PublicParams P) (w : WorldOut P) :
    firstMark pp w = some .init ↔ (idealInit (idealCtx pp w) w.out.pv).mark = some .init := by
  exact fold_events_init _ _ _

theorem fold_consistent {S A L E M : Type} (mark : S → Option M)
    (dict : S → L → Option E) (label : A → L) (expr : A → E)
    (rel : E → E → Prop) (step : S → A → S)
    (step_ok : ∀ st a, mark st = none →
      (∀ old, dict st (label a) = some old → rel (expr a) old) →
      mark (step st a) = none ∧
      ∀ l old, dict (step st a) l = some old →
        dict st l = some old ∨ (l = label a ∧ old = expr a))
    (all todo : List A) (st : S)
    (hsub : ∀ a ∈ todo, a ∈ all)
    (hmark : mark st = none)
    (hentries : ∀ l old, dict st l = some old →
      ∃ a ∈ all, label a = l ∧ expr a = old)
    (hcompat : ∀ a ∈ all, ∀ b ∈ all, label a = label b → rel (expr a) (expr b)) :
    mark (todo.foldl step st) = none := by
  induction todo generalizing st with
  | nil => exact hmark
  | cons a todo ih =>
    have ha : a ∈ all := hsub a (by simp)
    have hs : ∀ b ∈ todo, b ∈ all := by
      intro b hb
      exact hsub b (by simp [hb])
    have hr : ∀ old, dict st (label a) = some old → rel (expr a) old := by
      intro old hold
      obtain ⟨b, hb, hl, he⟩ := hentries _ _ hold
      rw [← he]
      exact hcompat a ha b hb hl.symm
    obtain ⟨hm, hd⟩ := step_ok st a hmark hr
    apply ih (step st a) hs hm
    intro l old hold
    rcases hd l old hold with hold | ⟨rfl, rfl⟩
    · exact hentries _ _ hold
    · exact ⟨a, ha, rfl, rfl⟩

private noncomputable def initStep1 (st : IdealState P) (a : Option (G1Idx P) × Label P) : IdealState P :=
  match st.mark with
  | some _ => st
  | none => ideal1 cx .init st a.2 (Pi.single a.1 1)

private noncomputable def initStep2 (st : IdealState P) (a : Option (G2Idx P) × Label P) : IdealState P :=
  match st.mark with
  | some _ => st
  | none => ideal2 cx .init st a.2 (Pi.single a.1 1)

private noncomputable def initStepT (st : IdealState P) (a : Option Unit × Label P) : IdealState P :=
  match st.mark with
  | some _ => st
  | none => idealT cx true st a.2 (gtInit a.1)

private theorem initStep1_ok (st : IdealState P) (a : Option (G1Idx P) × Label P)
    (hm : st.mark = none)
    (hr : ∀ old, st.d1 a.2 = some old → cx.eq1 (Pi.single a.1 1) old) :
    (initStep1 cx st a).mark = none ∧
      ∀ l old, (initStep1 cx st a).d1 l = some old →
        st.d1 l = some old ∨ (l = a.2 ∧ old = Pi.single a.1 1) := by
  simp only [initStep1, hm, ideal1]
  split
  · constructor
    · rfl
    · intro l old h
      by_cases hl : l = a.2
      · subst l
        simp at h
        exact Or.inr ⟨rfl, h.symm⟩
      · exact Or.inl (by simpa [Function.update, hl] using h)
  · rename_i old hold
    simp only [hr old hold, if_true]
    exact ⟨hm, fun _ _ h => Or.inl h⟩

private theorem initStep2_ok (st : IdealState P) (a : Option (G2Idx P) × Label P)
    (hm : st.mark = none)
    (hr : ∀ old, st.d2 a.2 = some old → cx.eq2 (Pi.single a.1 1) old) :
    (initStep2 cx st a).mark = none ∧
      ∀ l old, (initStep2 cx st a).d2 l = some old →
        st.d2 l = some old ∨ (l = a.2 ∧ old = Pi.single a.1 1) := by
  simp only [initStep2, hm, ideal2]
  split
  · constructor
    · rfl
    · intro l old h
      by_cases hl : l = a.2
      · subst l
        simp at h
        exact Or.inr ⟨rfl, h.symm⟩
      · exact Or.inl (by simpa [Function.update, hl] using h)
  · rename_i old hold
    simp only [hr old hold, if_true]
    exact ⟨hm, fun _ _ h => Or.inl h⟩

private theorem initStepT_ok (st : IdealState P) (a : Option Unit × Label P)
    (hm : st.mark = none)
    (hr : ∀ old, st.dT a.2 = some old → cx.eqT (gtInit a.1) old) :
    (initStepT cx st a).mark = none ∧
      ∀ l old, (initStepT cx st a).dT l = some old →
        st.dT l = some old ∨ (l = a.2 ∧ old = gtInit a.1) := by
  simp only [initStepT, hm, idealT]
  split
  · constructor
    · rfl
    · intro l old h
      by_cases hl : l = a.2
      · subst l
        simp at h
        exact Or.inr ⟨rfl, h.symm⟩
      · exact Or.inl (by simpa [Function.update, hl] using h)
  · rename_i old hold
    simp only [hr old hold, if_true]
    exact ⟨hm, fun _ _ h => Or.inl h⟩

private theorem initStep1_d2 (st : IdealState P) (a : Option (G1Idx P) × Label P) :
    (initStep1 cx st a).d2 = st.d2 := by
  cases hm : st.mark <;> cases hd : st.d1 a.2 <;>
    simp [initStep1, ideal1, hm, hd] <;> split <;> rfl

private theorem initStep1_dT (st : IdealState P) (a : Option (G1Idx P) × Label P) :
    (initStep1 cx st a).dT = st.dT := by
  cases hm : st.mark <;> cases hd : st.d1 a.2 <;>
    simp [initStep1, ideal1, hm, hd] <;> split <;> rfl

private theorem initStep2_dT (st : IdealState P) (a : Option (G2Idx P) × Label P) :
    (initStep2 cx st a).dT = st.dT := by
  cases hm : st.mark <;> cases hd : st.d2 a.2 <;>
    simp [initStep2, ideal2, hm, hd] <;> split <;> rfl

private theorem fold_preserves {S A D : Type} (proj : S → D) (step : S → A → S)
    (h : ∀ st a, proj (step st a) = proj st) (xs : List A) (st : S) :
    proj (xs.foldl step st) = proj st := by
  induction xs generalizing st with
  | nil => rfl
  | cons a xs ih => simp only [List.foldl_cons, ih, h]

def InitConflict (pv : PubView P) : Prop :=
  (∃ a ∈ pv.g1, ∃ b ∈ pv.g1, a.2 = b.2 ∧ ¬ cx.eq1 (Pi.single a.1 1) (Pi.single b.1 1)) ∨
  (∃ a ∈ pv.g2, ∃ b ∈ pv.g2, a.2 = b.2 ∧ ¬ cx.eq2 (Pi.single a.1 1) (Pi.single b.1 1)) ∨
  (∃ a ∈ pv.gT, ∃ b ∈ pv.gT, a.2 = b.2 ∧ ¬ cx.eqT (gtInit a.1) (gtInit b.1))

theorem init_mark_conflict (pv : PubView P) :
    (idealInit cx pv).mark = some .init → InitConflict cx pv := by
  intro hm
  by_contra hn
  have hc1 : ∀ a ∈ pv.g1, ∀ b ∈ pv.g1, a.2 = b.2 →
      cx.eq1 (Pi.single a.1 1) (Pi.single b.1 1) := by
    intro a ha b hb hl
    by_contra he
    exact hn (Or.inl ⟨a, ha, b, hb, hl, he⟩)
  have hc2 : ∀ a ∈ pv.g2, ∀ b ∈ pv.g2, a.2 = b.2 →
      cx.eq2 (Pi.single a.1 1) (Pi.single b.1 1) := by
    intro a ha b hb hl
    by_contra he
    exact hn (Or.inr (Or.inl ⟨a, ha, b, hb, hl, he⟩))
  have hcT : ∀ a ∈ pv.gT, ∀ b ∈ pv.gT, a.2 = b.2 →
      cx.eqT (gtInit a.1) (gtInit b.1) := by
    intro a ha b hb hl
    by_contra he
    exact hn (Or.inr (Or.inr ⟨a, ha, b, hb, hl, he⟩))
  let s0 : IdealState P := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => false, none⟩
  let s1 := pv.g1.foldl (initStep1 cx) s0
  let s2 := pv.g2.foldl (initStep2 cx) s1
  have h1 : s1.mark = none := by
    apply fold_consistent IdealState.mark IdealState.d1 Prod.snd (fun a => Pi.single a.1 1)
      cx.eq1 (initStep1 cx) (initStep1_ok cx) pv.g1 pv.g1 s0
    · exact fun _ h => h
    · rfl
    · simp [s0]
    · exact hc1
  have hd2 : s1.d2 = fun _ => none := by
    exact fold_preserves IdealState.d2 (initStep1 cx) (initStep1_d2 cx) pv.g1 s0
  have h2 : s2.mark = none := by
    apply fold_consistent IdealState.mark IdealState.d2 Prod.snd (fun a => Pi.single a.1 1)
      cx.eq2 (initStep2 cx) (initStep2_ok cx) pv.g2 pv.g2 s1
    · exact fun _ h => h
    · exact h1
    · simp [hd2]
    · exact hc2
  have hdT1 : s1.dT = fun _ => none := by
    exact fold_preserves IdealState.dT (initStep1 cx) (initStep1_dT cx) pv.g1 s0
  have hdT2 : s2.dT = fun _ => none := by
    rw [show s2.dT = s1.dT from
      fold_preserves IdealState.dT (initStep2 cx) (initStep2_dT cx) pv.g2 s1]
    exact hdT1
  have hT : (pv.gT.foldl (initStepT cx) s2).mark = none := by
    apply fold_consistent IdealState.mark IdealState.dT Prod.snd (fun a => gtInit a.1)
      cx.eqT (initStepT cx) (initStepT_ok cx) pv.gT pv.gT s2
    · exact fun _ h => h
    · exact h2
    · simp [hdT2]
    · exact hcT
  change (pv.gT.foldl (initStepT cx) s2).mark = some .init at hm
  rw [hT] at hm
  contradiction

theorem firstMark_init_conflict [Fact (Nat.Prime P.q)] (pp : PublicParams P) (w : WorldOut P)
    (h : firstMark pp w = some .init) : InitConflict (idealCtx pp w) w.out.pv :=
  init_mark_conflict _ _ ((firstMark_init_iff _ _).mp h)

end Praxis.Proofs.GroupModel
