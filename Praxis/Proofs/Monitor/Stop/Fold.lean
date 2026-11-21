import Praxis.Proofs.Monitor.Stop.Deterministic
import Praxis.Proofs.Monitor.Stop.Init
import Praxis.Proofs.Monitor.Stop.Op
import Praxis.Proofs.Monitor.Stop.Kdf
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Stop.Sync
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting

namespace Praxis.Proofs.Monitor

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem event_sync (ci : IdealCtx P) (cm : MonCtx P)
    (h1 : ∀ E F, ci.eq1 E F → cm.priv1 E = cm.priv1 F)
    (h2 : ∀ E F, ci.eq2 E F → cm.priv2 E = cm.priv2 F)
    (hT : ∀ E F, ci.eqT E F → cm.privT E = cm.privT F)
    (htarget : ci.target = cm.target)
    (si : IdealState P) (sm : MonState P) (e : MonEvent P)
    (hs : SameTables si sm) (hi : si.mark = none) (hr : sm.stop = .running)
    (hn : (idealEvent ci si e).mark = none) :
    (monEvent cm sm e).stop = .running ∧
      SameTables (idealEvent ci si e) (monEvent cm sm e) := by
  simp only [idealEvent, hi] at hn ⊢
  simp only [monEvent, hr]
  cases e with
  | op o => exact op_sync ci cm h1 h2 hT si sm o hs hr hn
  | kdf nm => exact kdf_sync ci cm htarget si sm nm hs hr hn

theorem event_payload_stop (ci : IdealCtx P) (cm : MonCtx P)
    (htarget : ci.target = cm.target) (hlabels : ci.keyLabels = cm.keyLabels)
    (hformal : ∀ E, ci.isKey E → cm.privT E = cm.keyPriv)
    (hsmul : ∀ a E, cm.privT (a • E) = a * cm.privT E)
    (hsub : ∀ E F, cm.privT (E - F) = cm.privT E - cm.privT F)
    (si : IdealState P) (sm : MonState P) (e : MonEvent P) (k : Mark P)
    (D : ExprT P) (ι : Fq P) (hs : SameTables si sm) (hi : si.mark = none)
    (hr : sm.stop = .running) (hm : (idealEvent ci si e).mark = some k)
    (hd : k.data = some (D, ι)) (hne : cm.privT D ≠ ι * cm.keyPriv) :
    (monEvent cm sm e).stop = .stack D := by
  classical
  simp only [idealEvent, hi] at hm
  simp only [monEvent, hr]
  cases k <;> simp [Mark.data] at hd
  · rename_i D'
    obtain ⟨rfl, rfl⟩ := hd
    have hv : cm.privT D' ≠ 0 := by simpa using hne
    cases e with
    | op o => exact op_diff_stop ci cm hsub si sm o D' hs hi hm hv
    | kdf nm => exact False.elim (kdf_ne_diff ci si nm D' hi hm)
  · rename_i D'
    obtain ⟨rfl, rfl⟩ := hd
    have hv : cm.privT D' ≠ cm.keyPriv := by simpa using hne
    cases e with
    | op o => exact False.elim (op_ne_key ci si o D' hi hm)
    | kdf nm => exact kdf_mark_stop ci cm htarget hlabels hformal hsmul si sm nm D' hs hi hr hm hv

theorem fold_payload_stop (ci : IdealCtx P) (cm : MonCtx P)
    (h1 : ∀ E F, ci.eq1 E F → cm.priv1 E = cm.priv1 F)
    (h2 : ∀ E F, ci.eq2 E F → cm.priv2 E = cm.priv2 F)
    (hT : ∀ E F, ci.eqT E F → cm.privT E = cm.privT F)
    (htarget : ci.target = cm.target) (hlabels : ci.keyLabels = cm.keyLabels)
    (hformal : ∀ E, ci.isKey E → cm.privT E = cm.keyPriv)
    (hsmul : ∀ a E, cm.privT (a • E) = a * cm.privT E)
    (hsub : ∀ E F, cm.privT (E - F) = cm.privT E - cm.privT F)
    (es : List (MonEvent P)) (si : IdealState P) (sm : MonState P) (k : Mark P)
    (D : ExprT P) (ι : Fq P) (hs : SameTables si sm) (hi : si.mark = none)
    (hr : sm.stop = .running) (hf : (es.foldl (idealEvent ci) si).mark = some k)
    (hd : k.data = some (D, ι)) (hne : cm.privT D ≠ ι * cm.keyPriv) :
    (es.foldl (monEvent cm) sm).stop = .stack D := by
  induction es generalizing si sm with
  | nil => simp [hi] at hf
  | cons e es ih =>
    simp only [List.foldl_cons] at hf ⊢
    cases hn : (idealEvent ci si e).mark with
    | none =>
      obtain ⟨hr', hs'⟩ := event_sync ci cm h1 h2 hT htarget si sm e hs hi hr hn
      exact ih _ _ hs' hn hr' hf
    | some k' =>
      have he := ideal_fold_marked ci es (idealEvent ci si e) k' hn
      rw [he, hn] at hf
      have hk : k' = k := Option.some.inj hf
      subst k'
      have ht := event_payload_stop ci cm htarget hlabels hformal hsmul hsub
        si sm e k D ι hs hi hr hn hd hne
      rw [mon_fold_stopped cm es (monEvent cm sm e) D ht]
      exact ht

theorem fixed_world_miss (pp : PublicParams P) (m : Msg P) (w : WorldOut P)
    (D : ExprT P) (ι : Fq P) (ω : Assign P) (hg : GoodMark pp w D ι)
    (hv : ValidCoins pp.qap ω.coins)
    (hm : monitor (monCtx (redViewOf pp m w) ω) w.out.pv w.st.tr w.st.kdfLog ≠
      .stack D) : valT pp (formsOfRun w) ω D = ι * kappa pp ω.coins := by
  classical
  by_contra hne
  obtain ⟨k, hk, hd, _⟩ := hg
  let ci := idealCtx pp w
  let cm := monCtx (redViewOf pp m w) ω
  have hf : ((monEvents w.st.tr w.st.kdfLog).foldl (idealEvent ci)
      (idealInit ci w.out.pv)).mark = some k := hk
  have hi : (idealInit ci w.out.pv).mark = none := by
    rcases init_mark_cases ci w.out.pv with h | h
    · exact h
    · have he := ideal_fold_marked ci (monEvents w.st.tr w.st.kdfLog)
        (idealInit ci w.out.pv) .init h
      rw [he, h] at hf
      have : k = .init := (Option.some.inj hf).symm
      subst k
      simp [Mark.data] at hd
  have hs : SameTables (idealInit ci w.out.pv) (monInit w.out.pv) :=
    init_sameTables ci w.out.pv hi
  have h1 : ∀ E F, ci.eq1 E F → cm.priv1 E = cm.priv1 F := by
    intro E F h
    exact h ω hv
  have h2 : ∀ E F, ci.eq2 E F → cm.priv2 E = cm.priv2 F := by
    intro E F h
    exact h ω hv
  have hT : ∀ E F, ci.eqT E F → cm.privT E = cm.privT F := by
    intro E F h
    exact h ω hv
  have ht : ci.target = cm.target := by rfl
  have hl : ci.keyLabels = cm.keyLabels := by rfl
  have hkey : ∀ E, ci.isKey E → cm.privT E = cm.keyPriv := by
    intro E h
    exact h ω hv
  have hsmul : ∀ a E, cm.privT (a • E) = a * cm.privT E := by
    intro a E
    exact valT_smul pp (formsOfRun w) ω a E
  have hsub : ∀ E F, cm.privT (E - F) = cm.privT E - cm.privT F := by
    intro E F
    exact valT_sub pp (formsOfRun w) ω E F
  have hp : cm.privT D ≠ ι * cm.keyPriv := hne
  have hstop := fold_payload_stop ci cm h1 h2 hT ht hl hkey hsmul hsub
    (monEvents w.st.tr w.st.kdfLog) (idealInit ci w.out.pv) (monInit w.out.pv)
    k D ι hs hi rfl hf hd hp
  exact hm hstop

end Praxis.Proofs.Monitor
