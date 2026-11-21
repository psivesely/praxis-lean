import Praxis.Proofs.Injectivity.Law
import Praxis.Proofs.Differences
import Praxis.Proofs.Injectivity.Sound
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Injectivity.Book
import Praxis.Proofs.Injectivity.Core
import Praxis.Proofs.Injectivity.Span
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Units

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec

open scoped ENNReal

lemma counted_failure_le_none {P : Params} [Fact (Nat.Prime P.q)] (S : Relation P)
    (pub : PubView P) (tr : List (TrOp P)) :
    Pr[ExtFails S | runUnits (extractorC (sparseOf S) pub tr)] ≤
      Pr[fun x => x = none | runUnits (extractorC (sparseOf S) pub tr)] := by
  apply probEvent_mono
  intro x hx hf
  cases x with
  | none => rfl
  | some y => exact (hf y rfl (jse_sound (P := P) S pub tr y hx)).elim

lemma extractorRef_map (S : Relation P0) (pub : PubView P0) (tr : List (TrOp P0)) :
    extractorRef S pub tr = extractWith S pub tr <$> sketchLaw := by
  simp only [extractorRef, sketchLaw, map_eq_bind_pure_comp, Function.comp_def]

lemma counted_none_eq_reference (S : Relation P0) (pub : PubView P0) (tr : List (TrOp P0)) :
    Pr[fun x => x = none | extF S pub tr] =
      Pr[fun sk => extractWith S pub tr sk = none | sketchLaw] := by
  calc
    _ = Pr[fun x => x = none | extractorRef S pub tr] := by
      simp only [extF, probEvent_def, jse_law]
    _ = _ := by
      rw [extractorRef_map, probEvent_map]
      rfl

lemma injective_reference_none (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (w : WorldOut P0) (hi : InjCase (ppOf ch S) w) :
    Pr[fun sk => extractWith S w.out.pv w.st.tr sk = none | sketchLaw] ≤
      ENNReal.ofReal (Constants.extractor_recovery_failure_per_sector : ℝ) := by
  classical
  obtain ⟨D, ι, hgood, hinj, hdim⟩ := hi
  have hpassing := Differences.good_mark_passing ch S hS w D ι hgood
  have hzero : markStack D ≠ 0 := by
    obtain ⟨k, _, _, hcmp⟩ := hgood
    exact hcmp.2.1
  have hmono :
      Pr[fun sk => extractWith S w.out.pv w.st.tr sk = none | sketchLaw] ≤
      Pr[fun sk : Sketches P0 =>
        Submodule.span (Fq P0) (Set.range fun l : Fin dimMax =>
          ∑ c, (markStack D c).mulVec (sk c l (markSector D))) ≠
          jointSpace (markStack D) | sketchLaw] := by
    apply probEvent_mono
    intro sk _ hn
    intro hspan
    have hs : Submodule.span (Fq P0)
        (Set.range fun l : Fin dimMax => sketchesOf D sk l (markSector D)) =
        jointSpace (markStack D) := hspan
    have htest := jse_expr w.out.forms S hS D hpassing.2.1 hzero hdim hinj sk hs
    exact htest (jse_book ch S hS w sk D ι hgood hn)
  apply hmono.trans
  have hb := jse_span (markStack D) hdim (markSector D)
  apply (ENNReal.toReal_le_toReal probEvent_ne_top ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal (by
    norm_num [Constants.extractor_recovery_failure_per_sector] :
      (0 : ℝ) ≤ (Constants.extractor_recovery_failure_per_sector : ℝ))] using hb

set_option maxRecDepth 4096 in

lemma injective_counted_failure (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (w : WorldOut P0) :
    Pr[fun x => InjCase (ppOf ch S) w ∧ ExtFails S x | extF S w.out.pv w.st.tr] ≤
      ENNReal.ofReal (Constants.extractor_recovery_failure_per_sector : ℝ) := by
  classical
  by_cases hi : InjCase (ppOf ch S) w
  · have hmono :
        Pr[fun x => InjCase (ppOf ch S) w ∧ ExtFails S x | extF S w.out.pv w.st.tr] ≤
        Pr[fun x => x = none | extF S w.out.pv w.st.tr] := by
      calc
        _ ≤ Pr[ExtFails S | extF S w.out.pv w.st.tr] :=
          probEvent_mono (fun x _ hx => hx.2)
        _ ≤ _ := by
          simpa only [extF] using counted_failure_le_none (P := P0) S w.out.pv w.st.tr
    rw [counted_none_eq_reference] at hmono
    exact hmono.trans (injective_reference_none ch S hS w hi)
  · simp [hi]

theorem jse_inj (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S) (Q QH : ℕ)
    (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => InjCase (ppOf ch S) f.w ∧ ExtFails S f.x |
      worldFull (ppOf ch S) m A extF]).toReal ≤
        (Constants.extractor_recovery_failure_per_sector : ℝ) := by
  have heps : (0 : ℝ) ≤ (Constants.extractor_recovery_failure_per_sector : ℝ) := by
    norm_num [Constants.extractor_recovery_failure_per_sector]
  have hbound :
      Pr[fun f => InjCase (ppOf ch S) f.w ∧ ExtFails S f.x |
        worldFull (ppOf ch S) m A extF] ≤
        ENNReal.ofReal (Constants.extractor_recovery_failure_per_sector : ℝ) := by
    unfold worldFull
    apply probEvent_bind_le_of_forall_le
    intro w _
    apply probEvent_bind_le_of_forall_le
    intro ωp _
    apply probEvent_bind_le_of_forall_le
    intro ω0 _
    apply probEvent_bind_le_of_forall_le
    intro ω1 _
    have hmap : (do
        let x ← extF (ppOf ch S).S w.out.pv w.st.tr
        pure (⟨w, ωp 0, ω0, ω1, x⟩ : FullOut P0)) =
        (fun x => (⟨w, ωp 0, ω0, ω1, x⟩ : FullOut P0)) <$>
          extF S w.out.pv w.st.tr := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, ppOf, setup]
    rw [hmap, probEvent_map]
    exact injective_counted_failure ch S hS w
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [ENNReal.toReal_ofReal heps] using hreal

end Praxis.Proofs.Injectivity
