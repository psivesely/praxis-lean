import Praxis.Proofs.Injectivity.Invariant
import Praxis.Extractor
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Injectivity.Projections
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem Tracked.main {S : Relation P} {sk : Sketches P} {is : IdealState P} {es : ExState P}
    (h : Tracked S sk is es) (hm : is.mark ≠ none) (es' : ExState P) : Tracked S sk is es' :=
  ⟨fun hn => (hm hn).elim, h.2⟩

def exInit1 (es : ExState P) (e : Option (G1Idx P) × Label P) : ExState P :=
  { es with d1 := keepEarliest es.d1 e.2 (initG1 e.1) }

def exInit2 (sk : Sketches P) (es : ExState P) (e : Option (G2Idx P) × Label P) : ExState P :=
  { es with d2 := keepEarliest es.d2 e.2 (initG2 sk e.1) }

def exInitT (es : ExState P) (e : Option Unit × Label P) : ExState P :=
  { es with dT := keepEarliest es.dT e.2 0 }

noncomputable def idInit1 (cx : IdealCtx P) (is : IdealState P) (e : Option (G1Idx P) × Label P) :
    IdealState P := match is.mark with
  | some _ => is
  | none => ideal1 cx .init is e.2 (Pi.single e.1 1)

noncomputable def idInit2 (cx : IdealCtx P) (is : IdealState P) (e : Option (G2Idx P) × Label P) :
    IdealState P := match is.mark with
  | some _ => is
  | none => ideal2 cx .init is e.2 (Pi.single e.1 1)

noncomputable def idInitT (cx : IdealCtx P) (is : IdealState P) (e : Option Unit × Label P) :
    IdealState P := match is.mark with
  | some _ => is
  | none => idealT cx true is e.2 (gtInit e.1)

theorem tracked_init1 (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (es : ExState P) (h : Tracked S sk is es) (e : Option (G1Idx P) × Label P) :
    Tracked S sk (idInit1 cx is e) (exInit1 es e) := by
  cases hm : is.mark with
  | some k =>
    simp only [idInit1, hm]
    exact h.main (by simp [hm]) _
  | none =>
    simp only [idInit1, hm]
    obtain ⟨ha, hq⟩ := h.1 hm
    refine ⟨fun _ => ⟨?_, ?_⟩, checked_ideal1 S sk cx .init is e.2 _ hm rfl⟩
    · simpa only [proj1_init, exInit1] using agree_ideal1 ha cx .init e.2 (Pi.single e.1 1)
    · rw [ideal1_shape]
      exact hq

theorem tracked_init2 (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (es : ExState P) (h : Tracked S sk is es) (e : Option (G2Idx P) × Label P) :
    Tracked S sk (idInit2 cx is e) (exInit2 sk es e) := by
  cases hm : is.mark with
  | some k =>
    simp only [idInit2, hm]
    exact h.main (by simp [hm]) _
  | none =>
    simp only [idInit2, hm]
    obtain ⟨ha, hq⟩ := h.1 hm
    refine ⟨fun _ => ⟨?_, ?_⟩, checked_ideal2 S sk cx .init is e.2 _ hm rfl⟩
    · simpa only [proj2_init, exInit2] using agree_ideal2 ha cx .init e.2 (Pi.single e.1 1)
    · rw [ideal2_shape]
      exact hq

theorem checked_idealT_initial (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (l : Label P) (F : ExprT P) (hm : is.mark = none) :
    CheckedMark S sk (idealT cx true is l F) := by
  classical
  unfold idealT
  cases ht : is.dT l with
  | none => simp [CheckedMark, hm]
  | some E =>
    simp only [ht]
    split <;> simp_all [CheckedMark, Mark.data]
    intro k a b i hk hd
    subst k
    simp [Mark.data] at hd

theorem tracked_initT (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (es : ExState P) (h : Tracked S sk is es) (e : Option Unit × Label P) :
    Tracked S sk (idInitT cx is e) (exInitT es e) := by
  cases hm : is.mark with
  | some k =>
    simp only [idInitT, hm]
    exact h.main (by simp [hm]) _
  | none =>
    simp only [idInitT, hm]
    obtain ⟨ha, hq⟩ := h.1 hm
    refine ⟨fun _ => ⟨?_, ?_⟩, checked_idealT_initial S sk cx is e.2 _ hm⟩
    · rw [idealT_shape]
      simpa only [sketches_gtInit, exInitT] using
        ha.putT e.2 (gtInit e.1) _ es.found (fun _ => sketches_gtInit sk e.1)
    · rw [idealT_shape]
      exact hq.putT e.2 _ _ (by simp)

theorem fold_relation {A X Y : Type*} (R : X → Y → Prop) (xs : List A)
    (f : X → A → X) (g : Y → A → Y)
    (hs : ∀ x y, R x y → ∀ a ∈ xs, R (f x a) (g y a))
    (x : X) (y : Y) (h : R x y) : R (xs.foldl f x) (xs.foldl g y) := by
  induction xs generalizing x y with
  | nil => exact h
  | cons a as ih =>
    exact ih (fun x y h b hb => hs x y h b (by simp [hb])) _ _ (hs x y h a (by simp))

theorem fold_exInit1 (xs : List (Option (G1Idx P) × Label P)) (es : ExState P) :
    xs.foldl exInit1 es = { es with d1 := xs.foldl (fun t e => keepEarliest t e.2 (initG1 e.1)) es.d1 } := by
  induction xs generalizing es with
  | nil => rfl
  | cons e es' ih => simp only [List.foldl_cons, ih, exInit1]

theorem fold_exInit2 (sk : Sketches P) (xs : List (Option (G2Idx P) × Label P)) (es : ExState P) :
    xs.foldl (exInit2 sk) es =
      { es with d2 := xs.foldl (fun t e => keepEarliest t e.2 (initG2 sk e.1)) es.d2 } := by
  induction xs generalizing es with
  | nil => rfl
  | cons e es' ih => simp only [List.foldl_cons, ih, exInit2]

theorem fold_exInitT (xs : List (Option Unit × Label P)) (es : ExState P) :
    xs.foldl exInitT es = { es with dT := xs.foldl (fun t e => keepEarliest t e.2 0) es.dT } := by
  induction xs generalizing es with
  | nil => rfl
  | cons e es' ih => simp only [List.foldl_cons, ih, exInitT]

theorem tracked_init (S : Relation P) (sk : Sketches P) (cx : IdealCtx P) (pub : PubView P) :
    Tracked S sk (idealInit cx pub) (initState pub sk) := by
  let is0 : IdealState P := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => false, none⟩
  let es0 : ExState P := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => false, none⟩
  have h0 : Tracked S sk is0 es0 := by
    refine ⟨fun _ => ⟨?_, ?_⟩, ?_⟩
    · constructor <;> simp [AgreeT, is0, es0]
    · intro l E h; cases h
    · intro k D i h; cases h
  have h1 := fold_relation (Tracked S sk) pub.g1 (idInit1 cx) exInit1
    (fun is es h e _ => tracked_init1 S sk cx is es h e) is0 es0 h0
  have h2 := fold_relation (Tracked S sk) pub.g2 (idInit2 cx) (exInit2 sk)
    (fun is es h e _ => tracked_init2 S sk cx is es h e) _ _ h1
  have h3 := fold_relation (Tracked S sk) pub.gT (idInitT cx) exInitT
    (fun is es h e _ => tracked_initT S sk cx is es h e) _ _ h2
  simp only [fold_exInitT, fold_exInit2, fold_exInit1] at h3
  exact h3

end Praxis.Proofs.Injectivity
