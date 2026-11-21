import Praxis.Proofs.Monitor.Stop.Sync
import Praxis.Extractor
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Reduction
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Monitor

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem op_diff_stop (ci : IdealCtx P) (cm : MonCtx P)
    (hsub : ∀ E F, cm.privT (E - F) = cm.privT E - cm.privT F)
    (si : IdealState P) (sm : MonState P) (op : TrOp P) (D : ExprT P)
    (hs : SameTables si sm) (hi : si.mark = none)
    (hm : (idealOp ci si op).mark = some (.diff D)) (hv : cm.privT D ≠ 0) :
    (monOp cm sm op).stop = .stack D := by
  classical
  cases op with
  | lin s a b u v res =>
    cases s with
    | g₁ =>
      simp only [idealOp, ideal1] at hm
      split at hm
      · simp [hi] at hm
      · split at hm <;> simp [hi] at hm
    | g₂ =>
      simp only [idealOp, ideal2] at hm
      split at hm
      · simp [hi] at hm
      · split at hm <;> simp [hi] at hm
    | gₜ =>
      simp only [idealOp] at hm
      simp only [monOp, ← hs.2.2.1]
      exact newT_mark_stop ci cm hsub (recordT si u v) (monRecordT sm u v) res _ D
        (recordT_sync si sm u v hs) hi hm hv
  | pair u v res =>
    simp only [idealOp] at hm
    simp only [monOp, ← hs.1, ← hs.2.1]
    exact newT_mark_stop ci cm hsub si sm res _ D hs hi hm hv
  | name u res =>
    have hn : sm.named u = si.named u := by rw [← hs.2.2.2]
    simp only [idealOp] at hm
    simp only [monOp, hn]
    split
    · rename_i hn'
      simp [hn', hi] at hm
    · rename_i hn'
      simp only [if_neg hn'] at hm
      simp only [← hs.2.2.1]
      apply newT_mark_stop ci cm hsub
        { si with named := Function.update si.named u true }
        { sm with dT := si.dT, named := Function.update sm.named u true } _ _ D
      · rcases hs with ⟨h1, h2, hT, hn⟩
        exact ⟨h1, h2, rfl, by simp only [hn]⟩
      · exact hi
      · exact hm
      · exact hv

theorem op_ne_key (ci : IdealCtx P) (si : IdealState P) (op : TrOp P) (D : ExprT P)
    (hi : si.mark = none) : (idealOp ci si op).mark ≠ some (.key D) := by
  classical
  cases op with
  | lin s a b u v res =>
    cases s with
    | g₁ =>
      simp only [idealOp, ideal1]
      split <;> simp_all
      split <;> simp_all
    | g₂ =>
      simp only [idealOp, ideal2]
      split <;> simp_all
      split <;> simp_all
    | gₜ =>
      simp only [idealOp, idealT, recordT]
      split <;> simp_all
      split <;> simp_all
  | pair u v res =>
    simp only [idealOp, idealT]
    split <;> simp_all
    split <;> simp_all
  | name u res =>
    simp only [idealOp]
    split
    · simp [hi]
    · simp only [idealT]
      split <;> simp_all
      split <;> simp_all

end Praxis.Proofs.Monitor
