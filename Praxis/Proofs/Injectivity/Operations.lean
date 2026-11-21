import Praxis.Proofs.Injectivity.Initial
import Praxis.Proofs.Injectivity.Events
import Praxis.Extractor
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Injectivity.Invariant
import Praxis.Proofs.Injectivity.Projections
import Praxis.Proofs.Injectivity.Invariants
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem Agree.get1 {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (l : Label P) : (es.d1 l).getD 0 = proj1 ((is.d1 l).getD 0) := by
  rw [h.d1 l, map_getD_zero _ proj1_zero]

theorem Agree.get2 {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (l : Label P) : (es.d2 l).getD 0 = proj2 sk ((is.d2 l).getD 0) := by
  rw [h.d2 l, map_getD_zero _ (proj2_zero sk)]

theorem Agree.getT {sk : Sketches P} {is : IdealState P} {es : ExState P} (h : Agree sk is es)
    (l : Label P) : (es.dT l).getD 0 = sketchesOf ((is.dT l).getD 0) sk := by
  rcases h.dT l with he | ⟨he, hi⟩
  · rw [he, map_getD_zero _ (sketches_zero sk)]
  · rw [he, hi]; simp

theorem tracked_newT (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (es : ExState P) (l : Label P) (F : ExprT P)
    (ha : Agree sk is es) (hq : Quiet S sk is) (hm : is.mark = none)
    (hf : (gtStep S es (sketchesOf F sk) l).found = none)
    (hzero : ∀ F, cx.eqT F 0 → sketchesOf F sk = 0) :
    Tracked S sk (idealT cx false is l F) (gtStep S es (sketchesOf F sk) l) :=
  ⟨fun hn => agree_quiet_idealT S sk cx is es l F ha hq hf false hzero hn,
    checked_idealT S sk cx is es l F ha hm hf false⟩

theorem tracked_op (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (is : IdealState P) (es : ExState P) (op : TrOp P)
    (h : Tracked S sk is es) (hm : is.mark = none) (hf : es.found = none)
    (hnext : (exStep S es op).found = none)
    (hzero : ∀ F, cx.eqT F 0 → sketchesOf F sk = 0) :
    Tracked S sk (idealOp cx is op) (exStep S es op) := by
  obtain ⟨ha, hq⟩ := h.1 hm
  cases op with
  | lin sort a b u v l =>
    cases sort with
    | g₁ =>
      have hp : proj1 (a • (is.d1 u).getD 0 + b • (is.d1 v).getD 0) =
          a • (es.d1 u).getD 0 + b • (es.d1 v).getD 0 := by
        rw [proj1_add, proj1_smul, proj1_smul, ← ha.get1 u, ← ha.get1 v]
      simp only [idealOp, exStep, hf]
      rw [← hp]
      have hag := agree_ideal1 ha cx .g1 l (a • (is.d1 u).getD 0 + b • (is.d1 v).getD 0)
      simp only [hf] at hag
      refine ⟨fun _ => ⟨hag, ?_⟩,
        checked_ideal1 S sk cx .g1 is l _ hm rfl⟩
      rw [ideal1_shape]
      exact hq
    | g₂ =>
      have hp : proj2 sk (a • (is.d2 u).getD 0 + b • (is.d2 v).getD 0) =
          a • (es.d2 u).getD 0 + b • (es.d2 v).getD 0 := by
        rw [proj2_add, proj2_smul, proj2_smul, ← ha.get2 u, ← ha.get2 v]
      simp only [idealOp, exStep, hf]
      rw [← hp]
      have hag := agree_ideal2 ha cx .g2 l (a • (is.d2 u).getD 0 + b • (is.d2 v).getD 0)
      simp only [hf] at hag
      refine ⟨fun _ => ⟨hag, ?_⟩,
        checked_ideal2 S sk cx .g2 is l _ hm rfl⟩
      rw [ideal2_shape]
      exact hq
    | gₜ =>
      have hp : sketchesOf (a • (is.dT u).getD 0 + b • (is.dT v).getD 0) sk =
          a • (es.dT u).getD 0 + b • (es.dT v).getD 0 := by
        rw [sketches_add, sketches_smul, sketches_smul, ← ha.getT u, ← ha.getT v]
      simp only [idealOp, exStep, hf] at hnext ⊢
      rw [← hp] at hnext ⊢
      exact tracked_newT S sk cx (recordT is u v) es l _
        (ha.recordT u v) (hq.recordT u v) hm hnext hzero
  | pair u v l =>
    have hp : sketchesOf (pairExpr ((is.d1 u).getD 0) ((is.d2 v).getD 0)) sk =
        (fun l s => ∑ k : Fin P.K1, (∑ leg : Leg P, (es.d2 v).getD 0 (k, leg) l s) •
          (es.d1 u).getD 0 k) := by
      rw [sketches_pair, ← ha.get1 u, ← ha.get2 v]
    simp only [idealOp, exStep, hf] at hnext ⊢
    rw [← hp] at hnext ⊢
    exact tracked_newT S sk cx is es l _ ha hq hm hnext hzero
  | name u l =>
    have hn : es.named u = is.named u := congrFun ha.named u
    simp only [idealOp, exStep, hf, hn] at hnext ⊢
    cases hu : is.named u with
    | true => simpa only [hu, ↓reduceIte] using h
    | false =>
      simp only [hu, Bool.false_eq_true, ↓reduceIte] at hnext ⊢
      have hp : sketchesOf (-(is.dT u).getD 0) sk = -(es.dT u).getD 0 := by
        rw [sketches_neg, ← ha.getT u]
      rw [← hp] at hnext ⊢
      have han : Agree sk { is with named := Function.update is.named u true }
          { es with named := Function.update es.named u true } :=
        ⟨ha.d1, ha.d2, ha.dT, by simp only [ha.named]⟩
      simp only [hf] at han
      exact tracked_newT S sk cx _ _ _ _ han hq hm hnext hzero

open Classical

theorem idealKdf_fields (cx : IdealCtx P) (is : IdealState P) (nm : ClassName P) :
    (idealKdf cx is nm).d1 = is.d1 ∧ (idealKdf cx is nm).d2 = is.d2 ∧
      (idealKdf cx is nm).dT = is.dT ∧ (idealKdf cx is nm).named = is.named := by
  unfold idealKdf
  split
  · split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem checked_kdf (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (hsign : ∀ kl ∈ cx.keyLabels, kl.2 = 1 ∨ kl.2 = -1)
    (is : IdealState P) (nm : ClassName P) (hm : is.mark = none) (hq : Quiet S sk is) :
    CheckedMark S sk (idealKdf cx is nm) := by
  intro k D i hk hd
  unfold idealKdf at hk
  split at hk
  · split at hk
    · rename_i kl hfind
      have hmem := List.mem_of_find?_eq_some hfind
      have hp := List.find?_some hfind
      cases he : is.dT kl.1 with
      | none => simp [he] at hp
      | some E =>
        simp only [Option.some.injEq] at hk
        subst k
        simp only [Mark.data, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        simp only [he, Option.getD_some]
        rcases hsign kl hmem with hs | hs
        · simpa only [hs, one_smul] using hq kl.1 E he
        · simpa only [hs, neg_one_smul, sketches_neg, testExpr_neg] using hq kl.1 E he
    · split at hk <;> simp only [Option.some.injEq] at hk <;> subst k <;> simp [Mark.data] at hd
  · simp [hm] at hk

theorem tracked_kdf (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (hsign : ∀ kl ∈ cx.keyLabels, kl.2 = 1 ∨ kl.2 = -1)
    (is : IdealState P) (es : ExState P) (nm : ClassName P)
    (h : Tracked S sk is es) (hm : is.mark = none) :
    Tracked S sk (idealKdf cx is nm) es := by
  obtain ⟨ha, hq⟩ := h.1 hm
  obtain ⟨h1, h2, hT, hn⟩ := idealKdf_fields cx is nm
  refine ⟨fun _ => ⟨?_, ?_⟩, checked_kdf S sk cx hsign is nm hm hq⟩
  · constructor
    · intro l; rw [h1]; exact ha.d1 l
    · intro l; rw [h2]; exact ha.d2 l
    · intro l; rw [hT]; exact ha.dT l
    · rw [hn]; exact ha.named
  · intro l E he
    rw [hT] at he
    exact hq l E he

theorem tracked_event (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (hsign : ∀ kl ∈ cx.keyLabels, kl.2 = 1 ∨ kl.2 = -1)
    (is : IdealState P) (es : ExState P) (e : MonEvent P)
    (h : Tracked S sk is es) (hf : es.found = none) (hnext : (exEvent S es e).found = none)
    (hzero : ∀ F, cx.eqT F 0 → sketchesOf F sk = 0) :
    Tracked S sk (idealEvent cx is e) (exEvent S es e) := by
  cases hm : is.mark with
  | some k =>
    simp only [idealEvent, hm]
    exact h.main (by simp [hm]) _
  | none =>
    simp only [idealEvent, hm]
    cases e with
    | op op => exact tracked_op S sk cx is es op h hm hf hnext hzero
    | kdf nm => exact tracked_kdf S sk cx hsign is es nm h hm

theorem tracked_events (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (hsign : ∀ kl ∈ cx.keyLabels, kl.2 = 1 ∨ kl.2 = -1)
    (events : List (MonEvent P)) (is : IdealState P) (es : ExState P)
    (h : Tracked S sk is es) (hf : (events.foldl (exEvent S) es).found = none)
    (hzero : ∀ F, cx.eqT F 0 → sketchesOf F sk = 0) :
    Tracked S sk (events.foldl (idealEvent cx) is) (events.foldl (exEvent S) es) := by
  induction events generalizing is es with
  | nil => exact h
  | cons e events ih =>
    have hnext : (exEvent S es e).found = none := event_fold_none S _ events hf
    exact ih _ _ (tracked_event S sk cx hsign is es e h (event_fold_none S es (e :: events) hf) hnext hzero) hf

theorem monitor_book (S : Relation P) (sk : Sketches P) (cx : IdealCtx P)
    (hsign : ∀ kl ∈ cx.keyLabels, kl.2 = 1 ∨ kl.2 = -1)
    (pub : PubView P) (tr : List (TrOp P)) (kl : List (ℕ × ClassName P))
    (k : Mark P) (D : ExprT P) (i : Fq P)
    (hm : idealMonitor cx pub tr kl = some k) (hd : k.data = some (D, i))
    (hf : extractWith S pub tr sk = none)
    (hzero : ∀ F, cx.eqT F 0 → sketchesOf F sk = 0) :
    testExpr S (sketchesOf D sk) = none := by
  have h := tracked_events S sk cx hsign (monEvents tr kl) (idealInit cx pub) (initState pub sk)
    (tracked_init S sk cx pub) (by rw [monEvents_fold]; exact hf) hzero
  exact h.2 k D i hm hd

end Praxis.Proofs.Injectivity
