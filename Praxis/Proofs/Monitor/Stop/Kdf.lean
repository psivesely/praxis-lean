import Praxis.Proofs.Monitor.Stop.Sync
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open Classical

variable {P : Params} [Fact (Nat.Prime P.q)]

private def keyStep (cm : MonCtx P) (st : MonState P) (kl : Label P × Fq P) : MonState P :=
  match st.stop, st.dT kl.1 with
  | .running, some E =>
    if kl.2 * cm.privT E = cm.keyPriv then st else { st with stop := .stack (kl.2 • E) }
  | _, _ => st

private theorem keyStep_stopped (cm : MonCtx P) (st : MonState P) (kl : Label P × Fq P)
    (D : ExprT P) (h : st.stop = .stack D) : keyStep cm st kl = st := by
  simp [keyStep, h]

private theorem keyFold_stopped (cm : MonCtx P) (ls : List (Label P × Fq P))
    (st : MonState P) (D : ExprT P) (h : st.stop = .stack D) :
    ls.foldl (keyStep cm) st = st := by
  induction ls with
  | nil => rfl
  | cons kl ls ih => simp only [List.foldl_cons, keyStep_stopped cm st kl D h, ih]

private theorem keyFold_hit (ci : IdealCtx P) (cm : MonCtx P)
    (hformal : ∀ E, ci.isKey E → cm.privT E = cm.keyPriv)
    (hsmul : ∀ a E, cm.privT (a • E) = a * cm.privT E)
    (ls : List (Label P × Fq P)) (si : IdealState P) (sm : MonState P)
    (hs : si.dT = sm.dT) (hr : sm.stop = .running)
    (kl : Label P × Fq P)
    (hf : ls.find? (fun p => match si.dT p.1 with
      | some E => decide (¬ ci.isKey (p.2 • E))
      | none => false) = some kl)
    (D : ExprT P) (hD : kl.2 • (si.dT kl.1).getD 0 = D)
    (hne : cm.privT D ≠ cm.keyPriv) :
    (ls.foldl (keyStep cm) sm).stop = .stack D := by
  classical
  induction ls with
  | nil => simp at hf
  | cons a ls ih =>
    simp only [List.find?_cons] at hf
    cases hd : si.dT a.1 with
    | none =>
      have hd' : sm.dT a.1 = none := by rw [← hs, hd]
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hf
      simp only [List.foldl_cons, keyStep, hr, hd']
      exact ih hf
    | some E =>
      have hd' : sm.dT a.1 = some E := by rw [← hs, hd]
      by_cases he : ci.isKey (a.2 • E)
      · have hv : a.2 * cm.privT E = cm.keyPriv := by
          rw [← hsmul]
          exact hformal _ he
        have hp : decide (¬ ci.isKey (a.2 • E)) = false := by simp [he]
        simp only [hd, hp] at hf
        simp only [List.foldl_cons, keyStep, hr, hd', hv, ↓reduceIte]
        exact ih hf
      · have hp : decide (¬ ci.isKey (a.2 • E)) = true := by simp [he]
        simp only [hd, hp, Option.some.injEq] at hf
        subst kl
        simp only [hd, Option.getD_some] at hD
        have hv : a.2 * cm.privT E ≠ cm.keyPriv := by
          rw [← hsmul, hD]
          exact hne
        simp only [List.foldl_cons, keyStep, hr, hd', hv, ↓reduceIte]
        have hh : ({sm with stop := .stack (a.2 • E)} : MonState P).stop = .stack D := by
          simpa using congrArg MonStop.stack hD
        rw [keyFold_stopped cm ls _ D hh]
        exact hh

theorem kdf_sync (ci : IdealCtx P) (cm : MonCtx P)
    (htarget : ci.target = cm.target) (si : IdealState P) (sm : MonState P)
    (nm : ClassName P) (hs : SameTables si sm) (hr : sm.stop = .running)
    (hi : (idealKdf ci si nm).mark = none) :
    (monKdf cm sm nm).stop = .running ∧ SameTables (idealKdf ci si nm) (monKdf cm sm nm) := by
  classical
  by_cases hn : nm = ci.target
  · simp only [idealKdf, hn, ↓reduceIte] at hi
    split at hi
    · simp at hi
    · split at hi <;> simp at hi
  · have hn' : nm ≠ cm.target := by simpa [← htarget] using hn
    simpa [idealKdf, monKdf, hn, hn'] using And.intro hr hs

theorem kdf_mark_stop (ci : IdealCtx P) (cm : MonCtx P)
    (htarget : ci.target = cm.target) (hlabels : ci.keyLabels = cm.keyLabels)
    (hformal : ∀ E, ci.isKey E → cm.privT E = cm.keyPriv)
    (hsmul : ∀ a E, cm.privT (a • E) = a * cm.privT E)
    (si : IdealState P) (sm : MonState P) (nm : ClassName P) (D : ExprT P)
    (hs : SameTables si sm) (hi : si.mark = none) (hr : sm.stop = .running)
    (hm : (idealKdf ci si nm).mark = some (.key D))
    (hne : cm.privT D ≠ cm.keyPriv) : (monKdf cm sm nm).stop = .stack D := by
  classical
  by_cases hn : nm = ci.target
  · have hn' : nm = cm.target := hn.trans htarget
    simp only [idealKdf, hn, ↓reduceIte] at hm
    split at hm
    · rename_i kl hf
      simp only [Option.some.injEq, Mark.key.injEq] at hm
      simp only [monKdf, hn', ↓reduceIte, ← hlabels]
      exact keyFold_hit ci cm hformal hsmul _ si sm hs.2.2.1 hr kl hf D hm hne
    · split at hm <;> simp at hm
  · simp [idealKdf, hn, hi] at hm

theorem kdf_ne_diff (ci : IdealCtx P) (si : IdealState P) (nm : ClassName P)
    (D : ExprT P) (hi : si.mark = none) :
    (idealKdf ci si nm).mark ≠ some (.diff D) := by
  classical
  unfold idealKdf
  split
  · split
    · simp
    · split <;> simp
  · simp [hi]

end Praxis.Proofs.Monitor
