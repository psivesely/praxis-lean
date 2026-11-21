import Praxis.Proofs.Basic
import Praxis.Extractor
import Praxis.Keys
import Praxis.Params
import Praxis.Reduction
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Monitor

variable {P : Params}

def SameTables (si : IdealState P) (sm : MonState P) : Prop :=
  si.d1 = sm.d1 ∧ si.d2 = sm.d2 ∧ si.dT = sm.dT ∧ si.named = sm.named

theorem recordT_sync (si : IdealState P) (sm : MonState P) (u v : Label P)
    (hs : SameTables si sm) :
    SameTables (recordT si u v) (monRecordT sm u v) := by
  rcases hs with ⟨h1, h2, hT, hn⟩
  simp [SameTables, recordT, monRecordT, h1, h2, hT, hn]

theorem new1_sync (ci : IdealCtx P) (cm : MonCtx P)
    (hval : ∀ E F, ci.eq1 E F → cm.priv1 E = cm.priv1 F)
    (si : IdealState P) (sm : MonState P) (l : Label P) (F : Expr1 P) (k : Mark P)
    (hs : SameTables si sm) (hr : sm.stop = .running)
    (hi : (ideal1 ci k si l F).mark = none) :
    (monNew1 cm sm l F).stop = .running ∧
      SameTables (ideal1 ci k si l F) (monNew1 cm sm l F) := by
  classical
  rcases hs with ⟨h1, h2, ht, hn⟩
  cases hd : si.d1 l with
  | none =>
    have hm : sm.d1 l = none := by rw [← h1, hd]
    simp [ideal1, monNew1, hd, hm, hr, SameTables, h1, h2, ht, hn]
  | some E =>
    have hm : sm.d1 l = some E := by rw [← h1, hd]
    by_cases he : ci.eq1 F E
    · have hv := hval F E he
      simp [ideal1, monNew1, hd, hm, he, hv, hr, SameTables, h1, h2, ht, hn]
    · simp [ideal1, hd, he] at hi

theorem new2_sync (ci : IdealCtx P) (cm : MonCtx P)
    (hval : ∀ E F, ci.eq2 E F → cm.priv2 E = cm.priv2 F)
    (si : IdealState P) (sm : MonState P) (l : Label P) (F : Expr2 P) (k : Mark P)
    (hs : SameTables si sm) (hr : sm.stop = .running)
    (hi : (ideal2 ci k si l F).mark = none) :
    (monNew2 cm sm l F).stop = .running ∧
      SameTables (ideal2 ci k si l F) (monNew2 cm sm l F) := by
  classical
  rcases hs with ⟨h1, h2, ht, hn⟩
  cases hd : si.d2 l with
  | none =>
    have hm : sm.d2 l = none := by rw [← h2, hd]
    simp [ideal2, monNew2, hd, hm, hr, SameTables, h1, h2, ht, hn]
  | some E =>
    have hm : sm.d2 l = some E := by rw [← h2, hd]
    by_cases he : ci.eq2 F E
    · have hv := hval F E he
      simp [ideal2, monNew2, hd, hm, he, hv, hr, SameTables, h1, h2, ht, hn]
    · simp [ideal2, hd, he] at hi

theorem newT_sync (ci : IdealCtx P) (cm : MonCtx P)
    (hval : ∀ E F, ci.eqT E F → cm.privT E = cm.privT F)
    (si : IdealState P) (sm : MonState P) (l : Label P) (F : ExprT P)
    (hs : SameTables si sm) (hr : sm.stop = .running)
    (hi : (idealT ci false si l F).mark = none) :
    (monNewT cm sm l F).stop = .running ∧
      SameTables (idealT ci false si l F) (monNewT cm sm l F) := by
  classical
  rcases hs with ⟨h1, h2, ht, hn⟩
  cases hd : si.dT l with
  | none =>
    have hm : sm.dT l = none := by rw [← ht, hd]
    simp [idealT, monNewT, hd, hm, hr, SameTables, h1, h2, ht, hn]
  | some E =>
    have hm : sm.dT l = some E := by rw [← ht, hd]
    by_cases he : ci.eqT F E
    · have hv := hval F E he
      simp [idealT, monNewT, hd, hm, he, hv, hr, SameTables, h1, h2, ht, hn]
    · simp [idealT, hd, he] at hi

theorem newT_stop (cm : MonCtx P) (si : IdealState P) (sm : MonState P)
    (l : Label P) (F E : ExprT P) (hs : SameTables si sm)
    (hd : si.dT l = some E) (hv : cm.privT F ≠ cm.privT E) :
    (monNewT cm sm l F).stop = .stack (F - E) := by
  have hm : sm.dT l = some E := by rw [← hs.2.2.1, hd]
  simp [monNewT, hm, hv]

theorem newT_mark_stop [Fact (Nat.Prime P.q)] (ci : IdealCtx P) (cm : MonCtx P)
    (hsub : ∀ E F, cm.privT (E - F) = cm.privT E - cm.privT F)
    (si : IdealState P) (sm : MonState P) (l : Label P) (F D : ExprT P)
    (hs : SameTables si sm) (hi : si.mark = none)
    (hm : (idealT ci false si l F).mark = some (.diff D)) (hv : cm.privT D ≠ 0) :
    (monNewT cm sm l F).stop = .stack D := by
  classical
  cases hd : si.dT l with
  | none => simp [idealT, hd, hi] at hm
  | some E =>
    by_cases he : ci.eqT F E
    · simp [idealT, hd, he, hi] at hm
    · have hD : F - E = D := by simpa [idealT, hd, he] using hm
      subst D
      have hne : cm.privT F ≠ cm.privT E := by
        intro hEq
        apply hv
        rw [hsub, hEq, sub_self]
      exact newT_stop cm si sm l F E hs hd hne

theorem op_sync (ci : IdealCtx P) (cm : MonCtx P)
    (h1 : ∀ E F, ci.eq1 E F → cm.priv1 E = cm.priv1 F)
    (h2 : ∀ E F, ci.eq2 E F → cm.priv2 E = cm.priv2 F)
    (hT : ∀ E F, ci.eqT E F → cm.privT E = cm.privT F)
    (si : IdealState P) (sm : MonState P) (op : TrOp P)
    (hs : SameTables si sm) (hr : sm.stop = .running)
    (hi : (idealOp ci si op).mark = none) :
    (monOp cm sm op).stop = .running ∧ SameTables (idealOp ci si op) (monOp cm sm op) := by
  classical
  cases op with
  | lin s a b u v res =>
    cases s with
    | g₁ =>
      simp only [idealOp] at hi
      simp only [idealOp, monOp, ← hs.1]
      exact new1_sync ci cm h1 si sm res _ .g1 hs hr hi
    | g₂ =>
      simp only [idealOp] at hi
      simp only [idealOp, monOp, ← hs.2.1]
      exact new2_sync ci cm h2 si sm res _ .g2 hs hr hi
    | gₜ =>
      simp only [idealOp] at hi
      simp only [idealOp, monOp, ← hs.2.2.1]
      exact newT_sync ci cm hT (recordT si u v) (monRecordT sm u v) res _
        (recordT_sync si sm u v hs) hr hi
  | pair u v res =>
    simp only [idealOp] at hi
    simp only [idealOp, monOp, ← hs.1, ← hs.2.1]
    exact newT_sync ci cm hT si sm res _ hs hr hi
  | name u res =>
    have hn : sm.named u = si.named u := by rw [← hs.2.2.2]
    simp only [idealOp] at hi
    simp only [idealOp, monOp, hn]
    split
    · exact ⟨hr, hs⟩
    · rename_i hflag
      simp only [if_neg hflag] at hi
      simp only [← hs.2.2.1]
      apply newT_sync ci cm hT
      · rcases hs with ⟨h1', h2', hT', hn'⟩
        exact ⟨h1', h2', rfl, by simp only [hn']⟩
      · exact hr
      · exact hi

end Praxis.Proofs.Monitor
