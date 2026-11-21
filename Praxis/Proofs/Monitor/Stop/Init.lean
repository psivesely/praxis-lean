import Praxis.Proofs.Monitor.Stop.Sync
import Praxis.Extractor
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.Reduction

namespace Praxis.Proofs.Monitor

noncomputable section

variable {P : Params}

private def forgetMark (s : IdealState P) : MonState P :=
  ⟨s.d1, s.d2, s.dT, s.named, .running⟩

private theorem fold_unmarked {α β γ δ : Type*} (mark : β → Option δ)
    (f : β → γ) (step : β → α → β) (next : γ → α → γ)
    (persist : ∀ s x k, mark s = some k → step s x = s)
    (agree : ∀ s x, mark s = none → mark (step s x) = none →
      f (step s x) = next (f s) x)
    (xs : List α) (s : β) (h : mark (xs.foldl step s) = none) :
    f (xs.foldl step s) = xs.foldl next (f s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons] at h ⊢
    have hs : mark s = none := by
      cases hm : mark s with
      | none => rfl
      | some k =>
        have hp : ∀ ys : List α, ys.foldl step s = s := by
          intro ys
          induction ys with
          | nil => rfl
          | cons y ys ih => simp only [List.foldl_cons, persist s y k hm, ih]
        rw [persist s x k hm, hp, hm] at h
        contradiction
    have hx : mark (step s x) = none := by
      cases hm : mark (step s x) with
      | none => rfl
      | some k =>
        have hp : ∀ ys : List α, ys.foldl step (step s x) = step s x := by
          intro ys
          induction ys with
          | nil => rfl
          | cons y ys ih => simp only [List.foldl_cons, persist (step s x) y k hm, ih]
        rw [hp, hm] at h
        contradiction
    rw [ih _ h, agree s x hs hx]

private def init1 (cx : IdealCtx P) (s : IdealState P) (e : Option (G1Idx P) × Label P) :
    IdealState P :=
  match s.mark with
  | some _ => s
  | none => ideal1 cx .init s e.2 (Pi.single e.1 1)

private def init2 (cx : IdealCtx P) (s : IdealState P) (e : Option (G2Idx P) × Label P) :
    IdealState P :=
  match s.mark with
  | some _ => s
  | none => ideal2 cx .init s e.2 (Pi.single e.1 1)

private def initT (cx : IdealCtx P) (s : IdealState P) (e : Option Unit × Label P) :
    IdealState P :=
  match s.mark with
  | some _ => s
  | none => idealT cx true s e.2 (gtInit e.1)

private def pub1 (s : MonState P) (e : Option (G1Idx P) × Label P) : MonState P :=
  { s with d1 := keepEarliest s.d1 e.2 (Pi.single e.1 1) }

private def pub2 (s : MonState P) (e : Option (G2Idx P) × Label P) : MonState P :=
  { s with d2 := keepEarliest s.d2 e.2 (Pi.single e.1 1) }

private def pubT (s : MonState P) (e : Option Unit × Label P) : MonState P :=
  { s with dT := keepEarliest s.dT e.2 (gtInit e.1) }

private theorem init1_agree (cx : IdealCtx P) (s : IdealState P)
    (e : Option (G1Idx P) × Label P) (h : s.mark = none)
    (h' : (init1 cx s e).mark = none) :
    forgetMark (init1 cx s e) = pub1 (forgetMark s) e := by
  classical
  simp only [init1, h] at h' ⊢
  cases hd : s.d1 e.2 with
  | none => simp [ideal1, hd, forgetMark, pub1, keepEarliest]
  | some E =>
    by_cases he : cx.eq1 (Pi.single e.1 1) E
    · simp [ideal1, hd, he, forgetMark, pub1, keepEarliest]
    · simp [ideal1, hd, he] at h'

private theorem init2_agree (cx : IdealCtx P) (s : IdealState P)
    (e : Option (G2Idx P) × Label P) (h : s.mark = none)
    (h' : (init2 cx s e).mark = none) :
    forgetMark (init2 cx s e) = pub2 (forgetMark s) e := by
  classical
  simp only [init2, h] at h' ⊢
  cases hd : s.d2 e.2 with
  | none => simp [ideal2, hd, forgetMark, pub2, keepEarliest]
  | some E =>
    by_cases he : cx.eq2 (Pi.single e.1 1) E
    · simp [ideal2, hd, he, forgetMark, pub2, keepEarliest]
    · simp [ideal2, hd, he] at h'

private theorem initT_agree (cx : IdealCtx P) (s : IdealState P)
    (e : Option Unit × Label P) (h : s.mark = none)
    (h' : (initT cx s e).mark = none) :
    forgetMark (initT cx s e) = pubT (forgetMark s) e := by
  classical
  simp only [initT, h] at h' ⊢
  cases hd : s.dT e.2 with
  | none => simp [idealT, hd, forgetMark, pubT, keepEarliest]
  | some E =>
    by_cases he : cx.eqT (gtInit e.1) E
    · simp [idealT, hd, he, forgetMark, pubT, keepEarliest]
    · simp [idealT, hd, he] at h'

private theorem fold_none_initial {α β δ : Type*} (mark : β → Option δ)
    (step : β → α → β)
    (persist : ∀ s x k, mark s = some k → step s x = s)
    (xs : List α) (s : β) (h : mark (xs.foldl step s) = none) : mark s = none := by
  cases hm : mark s with
  | none => rfl
  | some k =>
    have hp : ∀ ys : List α, ys.foldl step s = s := by
      intro ys
      induction ys with
      | nil => rfl
      | cons y ys ih => simp only [List.foldl_cons, persist s y k hm, ih]
    rw [hp, hm] at h
    contradiction

private theorem init1_persist (cx : IdealCtx P) (s : IdealState P)
    (e : Option (G1Idx P) × Label P) (k : Mark P) (h : s.mark = some k) :
    init1 cx s e = s := by simp [init1, h]

private theorem init2_persist (cx : IdealCtx P) (s : IdealState P)
    (e : Option (G2Idx P) × Label P) (k : Mark P) (h : s.mark = some k) :
    init2 cx s e = s := by simp [init2, h]

private theorem initT_persist (cx : IdealCtx P) (s : IdealState P)
    (e : Option Unit × Label P) (k : Mark P) (h : s.mark = some k) :
    initT cx s e = s := by simp [initT, h]

private theorem pub1_fold (xs : List (Option (G1Idx P) × Label P)) (s : MonState P) :
    xs.foldl pub1 s = { s with d1 := (xs.foldl
      (fun t e => keepEarliest t e.2 (Pi.single e.1 1)) s.d1) } := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => simp [List.foldl_cons, ih, pub1]

private theorem pub2_fold (xs : List (Option (G2Idx P) × Label P)) (s : MonState P) :
    xs.foldl pub2 s = { s with d2 := (xs.foldl
      (fun t e => keepEarliest t e.2 (Pi.single e.1 1)) s.d2) } := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => simp [List.foldl_cons, ih, pub2]

private theorem pubT_fold (xs : List (Option Unit × Label P)) (s : MonState P) :
    xs.foldl pubT s = { s with dT := (xs.foldl
      (fun t e => keepEarliest t e.2 (gtInit e.1)) s.dT) } := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => simp [List.foldl_cons, ih, pubT]

theorem init_sameTables (cx : IdealCtx P) (pv : PubView P)
    (h : (idealInit cx pv).mark = none) :
    SameTables (idealInit cx pv) (monInit pv) := by
  let s0 : IdealState P := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => false, none⟩
  let s1 := pv.g1.foldl (init1 cx) s0
  let s2 := pv.g2.foldl (init2 cx) s1
  have hT : (pv.gT.foldl (initT cx) s2).mark = none := h
  have h2 : s2.mark = none := fold_none_initial _ _ (initT_persist cx) _ _ hT
  have h1 : s1.mark = none := fold_none_initial _ _ (init2_persist cx) _ _ h2
  have e1 := fold_unmarked _ forgetMark (init1 cx) pub1 (init1_persist cx)
    (init1_agree cx) pv.g1 s0 h1
  have e2 := fold_unmarked _ forgetMark (init2 cx) pub2 (init2_persist cx)
    (init2_agree cx) pv.g2 s1 h2
  have eT := fold_unmarked _ forgetMark (initT cx) pubT (initT_persist cx)
    (initT_agree cx) pv.gT s2 hT
  have he : forgetMark (idealInit cx pv) = monInit pv := by
    change forgetMark (pv.gT.foldl (initT cx) s2) = monInit pv
    rw [eT, e2, e1, pubT_fold, pub2_fold, pub1_fold]
    rfl
  exact ⟨congrArg MonState.d1 he, congrArg MonState.d2 he,
    congrArg MonState.dT he, congrArg MonState.named he⟩

private def OnlyInit (s : IdealState P) : Prop := s.mark = none ∨ s.mark = some .init

private theorem init1_only (cx : IdealCtx P) (s : IdealState P)
    (e : Option (G1Idx P) × Label P) (h : OnlyInit s) : OnlyInit (init1 cx s e) := by
  classical
  rcases h with h | h
  · simp only [init1, h]
    unfold ideal1
    split
    · exact Or.inl h
    · split
      · exact Or.inl h
      · exact Or.inr rfl
  · simpa [init1, h, OnlyInit] using h

private theorem init2_only (cx : IdealCtx P) (s : IdealState P)
    (e : Option (G2Idx P) × Label P) (h : OnlyInit s) : OnlyInit (init2 cx s e) := by
  classical
  rcases h with h | h
  · simp only [init2, h]
    unfold ideal2
    split
    · exact Or.inl h
    · split
      · exact Or.inl h
      · exact Or.inr rfl
  · simpa [init2, h, OnlyInit] using h

private theorem initT_only (cx : IdealCtx P) (s : IdealState P)
    (e : Option Unit × Label P) (h : OnlyInit s) : OnlyInit (initT cx s e) := by
  classical
  rcases h with h | h
  · simp only [initT, h]
    unfold idealT
    split
    · exact Or.inl h
    · split
      · exact Or.inl h
      · exact Or.inr rfl
  · simpa [initT, h, OnlyInit] using h

private theorem fold_only {α : Type} (step : IdealState P → α → IdealState P)
    (hstep : ∀ s e, OnlyInit s → OnlyInit (step s e))
    (xs : List α) (s : IdealState P) (h : OnlyInit s) : OnlyInit (xs.foldl step s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih => exact ih _ (hstep s x h)

theorem init_mark_cases (cx : IdealCtx P) (pv : PubView P) :
    (idealInit cx pv).mark = none ∨ (idealInit cx pv).mark = some .init := by
  apply fold_only (initT cx) (initT_only cx)
  apply fold_only (init2 cx) (init2_only cx)
  apply fold_only (init1 cx) (init1_only cx)
  exact Or.inl rfl

end

end Praxis.Proofs.Monitor
