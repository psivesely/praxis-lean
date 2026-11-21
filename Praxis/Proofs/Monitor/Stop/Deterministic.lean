import Praxis.Proofs.Basic
import Praxis.Enc
import Praxis.Extractor
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec Classical

set_option maxHeartbeats 20000

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem valT_zero (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) : valT pp v ω 0 = 0 := by
  simp [valT]

private theorem list_sum_map_sub {α : Type} (xs : List α) (f g : α → Fq P) :
    (xs.map fun x => f x - g x).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private theorem list_sum_map_mul {α : Type} (xs : List α) (a : Fq P) (f : α → Fq P) :
    (xs.map fun x => a * f x).sum = a * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem valT_sub (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (E F : ExprT P) :
    valT pp v ω (E - F) = valT pp v ω E - valT pp v ω F := by
  simp only [valT, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul]
  simp_rw [list_sum_map_sub]
  ring

theorem valT_smul (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (a : Fq P) (E : ExprT P) :
    valT pp v ω (a • E) = a * valT pp v ω E := by
  change ((keys1 P).map fun i => ((keys2 P).map fun j =>
    (a * E.1 (i, j)) * (e1At pp ω i * e2At pp v ω j)).sum).sum +
      (a * E.2) * gtExp pp ω.coins = a * valT pp v ω E
  simp only [mul_assoc]
  simp_rw [list_sum_map_mul]
  simp only [valT, mul_add, mul_assoc]

theorem formalEqT_sub_zero (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (E F : ExprT P) : FormalEqT pp v (E - F) 0 ↔ FormalEqT pp v E F := by
  simp only [FormalEqT, valT_sub, valT_zero, sub_eq_zero]

def SoundMark (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N) : Mark P → Prop
  | .diff D => ¬ FormalEqT pp v D 0
  | .key D => ¬ FormalKey pp v D
  | _ => True

def SoundState (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (st : IdealState P) : Prop := ∀ k, st.mark = some k → SoundMark pp v k

theorem ideal1_sound (pp : PublicParams P) (w : WorldOut P) (k : Mark P)
    (st : IdealState P) (l : Label P) (F : Expr1 P)
    (hk : SoundMark pp (formsOfRun w) k) (h : SoundState pp (formsOfRun w) st) :
    SoundState pp (formsOfRun w) (ideal1 (idealCtx pp w) k st l F) := by
  intro k' hm
  unfold ideal1 at hm
  split at hm
  · exact h k' hm
  · split at hm
    · exact h k' hm
    · simp only [Option.some.injEq] at hm
      subst k'
      exact hk

theorem ideal2_sound (pp : PublicParams P) (w : WorldOut P) (k : Mark P)
    (st : IdealState P) (l : Label P) (F : Expr2 P)
    (hk : SoundMark pp (formsOfRun w) k) (h : SoundState pp (formsOfRun w) st) :
    SoundState pp (formsOfRun w) (ideal2 (idealCtx pp w) k st l F) := by
  intro k' hm
  unfold ideal2 at hm
  split at hm
  · exact h k' hm
  · split at hm
    · exact h k' hm
    · simp only [Option.some.injEq] at hm
      subst k'
      exact hk

theorem idealT_sound (pp : PublicParams P) (w : WorldOut P) (initial : Bool)
    (st : IdealState P) (l : Label P) (F : ExprT P)
    (h : SoundState pp (formsOfRun w) st) :
    SoundState pp (formsOfRun w) (idealT (idealCtx pp w) initial st l F) := by
  intro k hk
  unfold idealT at hk
  split at hk
  · exact h k hk
  · rename_i E hE
    split at hk
    · exact h k hk
    · rename_i hne
      cases initial with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hk
        subst k
        simpa [SoundMark, idealCtx, formalEqT_sub_zero] using hne
      | true =>
        simp only [↓reduceIte, Option.some.injEq] at hk
        subst k
        trivial

theorem idealKdf_sound (pp : PublicParams P) (w : WorldOut P)
    (st : IdealState P) (nm : ClassName P) (h : SoundState pp (formsOfRun w) st) :
    SoundState pp (formsOfRun w) (idealKdf (idealCtx pp w) st nm) := by
  intro k hk
  unfold idealKdf at hk
  split at hk
  · split at hk
    · rename_i kl hfind
      have hf := List.find?_some hfind
      cases hd : st.dT kl.1 with
      | none => simp [hd] at hf
      | some E =>
        simp only [hd, decide_eq_true_eq] at hf
        simp only [Option.some.injEq, hd, Option.getD_some] at hk
        subst k
        simpa [SoundMark, idealCtx] using hf
    · split at hk <;> simp only [Option.some.injEq] at hk <;> subst k <;> trivial
  · exact h k hk

theorem idealOp_sound (pp : PublicParams P) (w : WorldOut P)
    (st : IdealState P) (op : TrOp P) (h : SoundState pp (formsOfRun w) st) :
    SoundState pp (formsOfRun w) (idealOp (idealCtx pp w) st op) := by
  cases op with
  | lin s a b u v res =>
    cases s with
    | g₁ => exact ideal1_sound pp w .g1 st res _ trivial h
    | g₂ => exact ideal2_sound pp w .g2 st res _ trivial h
    | gₜ => exact idealT_sound pp w false (recordT st u v) res _ h
  | pair u v res => exact idealT_sound pp w false st res _ h
  | name u res =>
    simp only [idealOp]
    split
    · exact h
    · apply idealT_sound
      intro k hk
      exact h k hk

theorem idealEvent_sound (pp : PublicParams P) (w : WorldOut P)
    (st : IdealState P) (e : MonEvent P) (h : SoundState pp (formsOfRun w) st) :
    SoundState pp (formsOfRun w) (idealEvent (idealCtx pp w) st e) := by
  unfold idealEvent
  split
  · exact h
  · cases e with
    | op o => exact idealOp_sound pp w st o h
    | kdf nm => exact idealKdf_sound pp w st nm h

theorem ideal_fold_sound (pp : PublicParams P) (w : WorldOut P)
    (es : List (MonEvent P)) (st : IdealState P) (h : SoundState pp (formsOfRun w) st) :
    SoundState pp (formsOfRun w) (es.foldl (idealEvent (idealCtx pp w)) st) := by
  induction es generalizing st with
  | nil => exact h
  | cons e es ih =>
    simp only [List.foldl_cons]
    exact ih _ (idealEvent_sound pp w st e h)

theorem idealInit_sound (pp : PublicParams P) (w : WorldOut P) (pv : PubView P) :
    SoundState pp (formsOfRun w) (idealInit (idealCtx pp w) pv) := by
  have h1 : ∀ (es : List (Option (G1Idx P) × Label P)) (st : IdealState P),
      SoundState pp (formsOfRun w) st →
      SoundState pp (formsOfRun w) (es.foldl (fun st e => match st.mark with
        | some _ => st
        | none => ideal1 (idealCtx pp w) .init st e.2 (Pi.single e.1 1)) st) := by
    intro es
    induction es with
    | nil => intro st h; exact h
    | cons e es ih =>
      intro st h
      simp only [List.foldl_cons]
      apply ih
      cases hm : st.mark with
      | none => simp only [hm]; exact ideal1_sound pp w .init st e.2 _ trivial h
      | some k => simp only [hm]; exact h
  have h2 : ∀ (es : List (Option (G2Idx P) × Label P)) (st : IdealState P),
      SoundState pp (formsOfRun w) st →
      SoundState pp (formsOfRun w) (es.foldl (fun st e => match st.mark with
        | some _ => st
        | none => ideal2 (idealCtx pp w) .init st e.2 (Pi.single e.1 1)) st) := by
    intro es
    induction es with
    | nil => intro st h; exact h
    | cons e es ih =>
      intro st h
      simp only [List.foldl_cons]
      apply ih
      cases hm : st.mark with
      | none => simp only [hm]; exact ideal2_sound pp w .init st e.2 _ trivial h
      | some k => simp only [hm]; exact h
  have hT : ∀ (es : List (Option Unit × Label P)) (st : IdealState P),
      SoundState pp (formsOfRun w) st →
      SoundState pp (formsOfRun w) (es.foldl (fun st e => match st.mark with
        | some _ => st
        | none => idealT (idealCtx pp w) true st e.2 (gtInit e.1)) st) := by
    intro es
    induction es with
    | nil => intro st h; exact h
    | cons e es ih =>
      intro st h
      simp only [List.foldl_cons]
      apply ih
      cases hm : st.mark with
      | none => simp only [hm]; exact idealT_sound pp w true st e.2 _ h
      | some k => simp only [hm]; exact h
  apply hT
  apply h2
  apply h1
  intro k hk
  cases hk

theorem firstMark_sound (pp : PublicParams P) (w : WorldOut P) (k : Mark P)
    (hk : firstMark pp w = some k) : SoundMark pp (formsOfRun w) k := by
  exact ideal_fold_sound pp w _ _ (idealInit_sound pp w _) k hk

theorem goodMark_nonformal (pp : PublicParams P) (w : WorldOut P)
    (D : ExprT P) (ι : Fq P) (h : GoodMark pp w D ι) :
    ¬ (∀ ω, ValidCoins pp.qap ω.coins →
      valT pp (formsOfRun w) ω D = ι * kappa pp ω.coins) := by
  obtain ⟨k, hk, hd, _⟩ := h
  have hs := firstMark_sound pp w k hk
  cases k <;> simp only [Mark.data, Option.some.injEq, Prod.mk.injEq] at hd
  all_goals rcases hd with ⟨rfl, rfl⟩
  · simpa [SoundMark, FormalEqT, valT_zero] using hs
  · simpa [SoundMark, FormalKey] using hs

theorem goodMark_unique (pp : PublicParams P) (w : WorldOut P)
    {D D' : ExprT P} {ι ι' : Fq P}
    (h : GoodMark pp w D ι) (h' : GoodMark pp w D' ι') : D = D' ∧ ι = ι' := by
  obtain ⟨k, hk, hd, _⟩ := h
  obtain ⟨k', hk', hd', _⟩ := h'
  have : k = k' := Option.some.inj (hk.symm.trans hk')
  subst k'
  exact Prod.mk.inj (Option.some.inj (hd.symm.trans hd'))

theorem idealEvent_marked (cx : IdealCtx P) (st : IdealState P) (e : MonEvent P)
    (k : Mark P) (h : st.mark = some k) : idealEvent cx st e = st := by
  simp [idealEvent, h]

theorem ideal_fold_marked (cx : IdealCtx P) (es : List (MonEvent P))
    (st : IdealState P) (k : Mark P) (h : st.mark = some k) :
    es.foldl (idealEvent cx) st = st := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, idealEvent_marked cx st e k h, ih]

theorem monEvent_stopped (cx : MonCtx P) (st : MonState P) (e : MonEvent P)
    (D : ExprT P) (h : st.stop = .stack D) : monEvent cx st e = st := by
  simp [monEvent, h]

theorem mon_fold_stopped (cx : MonCtx P) (es : List (MonEvent P))
    (st : MonState P) (D : ExprT P) (h : st.stop = .stack D) :
    es.foldl (monEvent cx) st = st := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, monEvent_stopped cx st e D h, ih]

end Praxis.Proofs.Monitor
