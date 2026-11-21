import Praxis.Proofs.NamesPhase
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.NamesMonitor
import Praxis.Proofs.NamesReservoir
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting

namespace Praxis.Proofs.Names

open OracleComp OracleSpec

variable {P : Params}

noncomputable def monitorState (cx : IdealCtx P) (pv : PubView P) (st : OracleState P) :
    IdealState P := (monEvents st.tr st.kdfLog).foldl (idealEvent cx) (idealInit cx pv)

def HasKey (l r : Label P) (im : IdealState P) : Prop :=
  im.dT l ≠ none ∨ im.dT r ≠ none

def PhaseGood (l r : Label P) (im : IdealState P) (p : Reservoir.Phase) : Prop :=
  (im.mark = some .guessName → p = .success) ∧
    (im.mark = none → p = .dead → HasKey l r im)

def IssuedGood (issued : Finset (Label P)) (im : IdealState P) : Prop :=
  im.mark = none → ∀ l ∈ issued, im.dT l ≠ none

theorem event_hasKey (cx : IdealCtx P) (im : IdealState P) (e : MonEvent P)
    (l r : Label P) (h : HasKey l r im) : HasKey l r (idealEvent cx im e) := by
  rcases h with h | h
  · exact Or.inl (fun hz => h (idealEvent_fold_dT_none_imp cx [e] im l hz))
  · exact Or.inr (fun hz => h (idealEvent_fold_dT_none_imp cx [e] im r hz))

theorem event_issued_op (cx : IdealCtx P) (im : IdealState P) (op : TrOp P)
    (issued : Finset (Label P)) (h : IssuedGood issued im) :
    IssuedGood (match op.issuedGT with | some l => insert l issued | none => issued)
      (idealEvent cx im (.op op)) := by
  classical
  intro hm l hl
  have h0 := idealEvent_prev_mark_none cx im (.op op) hm
  cases ho : op.issuedGT with
  | none =>
    apply fun hz => h h0 l (by simpa [ho] using hl)
      (idealEvent_fold_dT_none_imp cx [.op op] im l hz)
  | some k =>
    simp only [ho, Finset.mem_insert] at hl
    rcases hl with rfl | hl
    · simpa [idealEvent, h0] using idealOp_issuedGT cx im op l ho
    · exact fun hz => h h0 l hl (idealEvent_fold_dT_none_imp cx [.op op] im l hz)

theorem phaseGood_op (cx : IdealCtx P) (im : IdealState P) (op : TrOp P)
    (issued : Finset (Label P)) (l r : Label P) (p p' : Reservoir.Phase)
    (hi : IssuedGood issued im) (hp : PhaseGood l r im p)
    (hs : p = .success → p' = .success)
    (hd : p' = .dead → p = .dead ∨
      l ∈ (match op.issuedGT with | some k => insert k issued | none => issued) ∨
      r ∈ (match op.issuedGT with | some k => insert k issued | none => issued)) :
    PhaseGood l r (idealEvent cx im (.op op)) p' := by
  constructor
  · intro hm
    apply hs
    apply hp.1
    cases h0 : im.mark with
    | none =>
      exact False.elim (idealOp_not_guessName cx im (by simp [h0]) op
        (by simpa [idealEvent, h0] using hm))
    | some k => simpa [idealEvent, h0] using hm
  · intro hm hdead
    have h0 := idealEvent_prev_mark_none cx im (.op op) hm
    rcases hd hdead with hd | hl | hr
    · exact event_hasKey cx im (.op op) l r (hp.2 h0 hd)
    · exact Or.inl (event_issued_op cx im op issued hi hm l hl)
    · exact Or.inr (event_issued_op cx im op issued hi hm r hr)

theorem phaseGood_kdf (cx : IdealCtx P) (im : IdealState P) (nm : ClassName P)
    (l r : Label P) (hl : (l, (1 : Fq P)) ∈ cx.keyLabels)
    (hr : (r, (-1 : Fq P)) ∈ cx.keyLabels) (p p' : Reservoir.Phase)
    (hp : PhaseGood l r im p) (hs : p = .success → p' = .success)
    (hd : p' = .dead → p = .dead)
    (ht : nm = cx.target → p ≠ .dead → p' = .success) :
    PhaseGood l r (idealEvent cx im (.kdf nm)) p' := by
  constructor
  · intro hm
    cases h0 : im.mark with
    | some k => exact hs (hp.1 (by simpa [idealEvent, h0] using hm))
    | none =>
      obtain ⟨hn, hkeys⟩ := (idealKdf_guessName_iff cx im h0 nm).mp
        (by simpa [idealEvent, h0] using hm)
      apply ht hn
      intro hdead
      rcases hp.2 h0 hdead with h | h
      · exact h (hkeys _ hl)
      · exact h (hkeys _ hr)
  · intro hm hdead
    exact event_hasKey cx im (.kdf nm) l r
      (hp.2 (idealEvent_prev_mark_none cx im (.kdf nm) hm) (hd hdead))

theorem issuedGood_kdf (cx : IdealCtx P) (im : IdealState P) (nm : ClassName P)
    (issued : Finset (Label P)) (hi : IssuedGood issued im) :
    IssuedGood issued (idealEvent cx im (.kdf nm)) := by
  intro hm l hl hz
  exact hi (idealEvent_prev_mark_none cx im (.kdf nm) hm) l hl
    (idealEvent_fold_dT_none_imp cx [.kdf nm] im l hz)

end Praxis.Proofs.Names
