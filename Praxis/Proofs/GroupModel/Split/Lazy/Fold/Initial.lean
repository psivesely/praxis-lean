import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Sync
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 800000

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0) (v : Fin P0.n → Vec k P0.N)

def constDict (st : IdealState P0) : Dict pp
  | .g₁ => fun l => (st.d1 l).map (fun E => MvPolynomial.C (Exposure.value1 pp E))
  | .g₂ => fun l => (st.d2 l).map (fun E => MvPolynomial.C (Exposure.value2 pp v E))
  | .gₜ => fun l => (st.dT l).map (fun E => MvPolynomial.C (Exposure.valueT pp v E))

def InitialRel (st : IdealState P0) (sh : State pp) : Prop :=
  (st.mark = none ∧ sh.first = none ∧ sh.dict = constDict pp v st) ∨
    (st.mark = some .init ∧ sh.first ≠ none)

lemma initial_g1 (cx : IdealCtx P0)
    (hcx : ∀ E F, cx.eq1 E F ↔ FormalEq1 pp E F)
    (st : IdealState P0) (sh : State pp) (h : InitialRel pp v st sh)
    (l : Label P0) (E : Expr1 P0) :
    InitialRel pp v (match st.mark with
      | some _ => st
      | none => ideal1 cx .init st l E)
      (insertResult pp sh .g₁ l (MvPolynomial.C (Exposure.value1 pp E))) := by
  classical
  rcases h with ⟨hm, hf, hd⟩ | ⟨hm, hf⟩
  · simp only [hm]
    have hd1 : sh.dict .g₁ l = (st.d1 l).map
        (fun E => MvPolynomial.C (Exposure.value1 pp E)) := by rw [hd]; rfl
    cases he : st.d1 l with
    | none =>
      have hs : sh.dict .g₁ l = none := by simp [he] at hd1; exact hd1
      left
      refine ⟨by simp [ideal1, he, hm], by simp [insertResult, hs, hf], ?_⟩
      simp only [insertResult, hs, ideal1, he]
      rw [hd]
      funext s t
      cases s <;> by_cases ht : t = l <;> simp [record, constDict, ht]
    | some F =>
      have hs : sh.dict .g₁ l = some (MvPolynomial.C (Exposure.value1 pp F)) := by
        simpa [he] using hd1
      rcases Classical.em (Exposure.value1 pp E = Exposure.value1 pp F) with hv | hv
      · have hc := (hcx E F).mpr ((Exposure.value1_eq_iff pp E F).mp hv)
        left
        simpa [ideal1, he, hc, insertResult, hs, hv] using And.intro hm (And.intro hf hd)
      · have hc : ¬ cx.eq1 E F := fun hc => hv
          ((Exposure.value1_eq_iff pp E F).mpr ((hcx E F).mp hc))
        have hC : MvPolynomial.C (Exposure.value1 pp E) ≠
            (MvPolynomial.C (Exposure.value1 pp F) : Poly pp) :=
          fun hh => hv (by simpa only [MvPolynomial.constantCoeff_C] using congrArg MvPolynomial.constantCoeff hh)
        right
        simp [ideal1, he, hc, insertResult, hs, hC, hf]
  · simp only [hm]
    right
    exact ⟨hm, fun hnone => hf ((insert_first_none pp sh .g₁ l _).mp hnone).1⟩

lemma initial_g2 (cx : IdealCtx P0)
    (hcx : ∀ E F, cx.eq2 E F ↔ FormalEq2 pp v E F)
    (st : IdealState P0) (sh : State pp) (h : InitialRel pp v st sh)
    (l : Label P0) (E : Expr2 P0) :
    InitialRel pp v (match st.mark with
      | some _ => st
      | none => ideal2 cx .init st l E)
      (insertResult pp sh .g₂ l (MvPolynomial.C (Exposure.value2 pp v E))) := by
  classical
  rcases h with ⟨hm, hf, hd⟩ | ⟨hm, hf⟩
  · simp only [hm]
    have hd2 : sh.dict .g₂ l = (st.d2 l).map
        (fun E => MvPolynomial.C (Exposure.value2 pp v E)) := by rw [hd]; rfl
    cases he : st.d2 l with
    | none =>
      have hs : sh.dict .g₂ l = none := by simpa [he] using hd2
      left
      refine ⟨by simp [ideal2, he, hm], by simp [insertResult, hs, hf], ?_⟩
      simp only [insertResult, hs, ideal2, he]
      rw [hd]
      funext s t
      cases s <;> by_cases ht : t = l <;> simp [record, constDict, ht]
    | some F =>
      have hs : sh.dict .g₂ l = some (MvPolynomial.C (Exposure.value2 pp v F)) := by
        simpa [he] using hd2
      rcases Classical.em (Exposure.value2 pp v E = Exposure.value2 pp v F) with hv | hv
      · have hc := (hcx E F).mpr ((Exposure.value2_eq_iff pp v E F).mp hv)
        left
        simpa [ideal2, he, hc, insertResult, hs, hv] using And.intro hm (And.intro hf hd)
      · have hc : ¬ cx.eq2 E F := fun hc => hv
          ((Exposure.value2_eq_iff pp v E F).mpr ((hcx E F).mp hc))
        have hC : MvPolynomial.C (Exposure.value2 pp v E) ≠
            (MvPolynomial.C (Exposure.value2 pp v F) : Poly pp) :=
          fun hh => hv (by simpa only [MvPolynomial.constantCoeff_C] using congrArg MvPolynomial.constantCoeff hh)
        right
        simp [ideal2, he, hc, insertResult, hs, hC, hf]
  · simp only [hm]
    right
    exact ⟨hm, fun hnone => hf ((insert_first_none pp sh .g₂ l _).mp hnone).1⟩

lemma initial_gt (cx : IdealCtx P0)
    (hcx : ∀ E F, cx.eqT E F ↔ FormalEqT pp v E F)
    (st : IdealState P0) (sh : State pp) (h : InitialRel pp v st sh)
    (l : Label P0) (E : ExprT P0) :
    InitialRel pp v (match st.mark with
      | some _ => st
      | none => idealT cx true st l E)
      (insertResult pp sh .gₜ l (MvPolynomial.C (Exposure.valueT pp v E))) := by
  classical
  rcases h with ⟨hm, hf, hd⟩ | ⟨hm, hf⟩
  · simp only [hm]
    have hdT : sh.dict .gₜ l = (st.dT l).map
        (fun E => MvPolynomial.C (Exposure.valueT pp v E)) := by rw [hd]; rfl
    cases he : st.dT l with
    | none =>
      have hs : sh.dict .gₜ l = none := by simpa [he] using hdT
      left
      refine ⟨by simp [idealT, he, hm], by simp [insertResult, hs, hf], ?_⟩
      simp only [insertResult, hs, idealT, he]
      rw [hd]
      funext s t
      cases s <;> by_cases ht : t = l <;> simp [record, constDict, ht]
    | some F =>
      have hs : sh.dict .gₜ l = some (MvPolynomial.C (Exposure.valueT pp v F)) := by
        simpa [he] using hdT
      rcases Classical.em (Exposure.valueT pp v E = Exposure.valueT pp v F) with hv | hv
      · have hc := (hcx E F).mpr ((Exposure.valueT_eq_iff pp v E F).mp hv)
        left
        simpa [idealT, he, hc, insertResult, hs, hv] using And.intro hm (And.intro hf hd)
      · have hc : ¬ cx.eqT E F := fun hc => hv
          ((Exposure.valueT_eq_iff pp v E F).mpr ((hcx E F).mp hc))
        have hC : MvPolynomial.C (Exposure.valueT pp v E) ≠
            (MvPolynomial.C (Exposure.valueT pp v F) : Poly pp) :=
          fun hh => hv (by simpa only [MvPolynomial.constantCoeff_C] using congrArg MvPolynomial.constantCoeff hh)
        right
        simp [idealT, he, hc, insertResult, hs, hC, hf]
  · simp only [hm]
    right
    exact ⟨hm, fun hnone => hf ((insert_first_none pp sh .gₜ l _).mp hnone).1⟩

lemma fold_rel {α β γ : Type} (R : α → β → Prop) (f : α → γ → α) (g : β → γ → β)
    (hstep : ∀ a b, R a b → ∀ x, R (f a x) (g b x))
    (xs : List γ) (a : α) (b : β) (h : R a b) : R (xs.foldl f a) (xs.foldl g b) := by
  classical
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih _ _ (hstep _ _ h x)

lemma initial_rel (z : WorldOut P0) :
    InitialRel pp (formVec z.out.forms) (idealInit (idealCtx pp z) z.out.pv)
      (initialise pp z.out.forms z.out.pv) := by
  let st : IdealState P0 := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => false, none⟩
  have h0 : InitialRel pp (formVec z.out.forms) st (empty pp) := by
    left
    exact ⟨rfl, rfl, by funext s t; cases s <;> rfl⟩
  have h1 := fold_rel (InitialRel pp (formVec z.out.forms))
    (fun st (e : Option (G1Idx P0) × Label P0) => match st.mark with
      | some _ => st | none => ideal1 (idealCtx pp z) .init st e.2 (Pi.single e.1 1))
    (fun sh e => insertResult pp sh .g₁ e.2 (base1 pp (Pi.single e.1 1)))
    (fun st sh h e => initial_g1 pp (formVec z.out.forms) (idealCtx pp z)
      (fun _ _ => Iff.rfl) st sh h e.2 (Pi.single e.1 1)) z.out.pv.g1 st (empty pp) h0
  have h2 := fold_rel (InitialRel pp (formVec z.out.forms))
    (fun st (e : Option (G2Idx P0) × Label P0) => match st.mark with
      | some _ => st | none => ideal2 (idealCtx pp z) .init st e.2 (Pi.single e.1 1))
    (fun sh e => insertResult pp sh .g₂ e.2 (base2 pp z.out.forms (Pi.single e.1 1)))
    (fun st sh h e => initial_g2 pp (formVec z.out.forms) (idealCtx pp z)
      (fun _ _ => Iff.rfl) st sh h e.2 (Pi.single e.1 1)) z.out.pv.g2 _ _ h1
  have h3 := fold_rel (InitialRel pp (formVec z.out.forms))
    (fun st (e : Option Unit × Label P0) => match st.mark with
      | some _ => st | none => idealT (idealCtx pp z) true st e.2 (gtInit e.1))
    (fun sh e => insertResult pp sh .gₜ e.2 (baseT pp z.out.forms (gtInit e.1)))
    (fun st sh h e => initial_gt pp (formVec z.out.forms) (idealCtx pp z)
      (fun _ _ => Iff.rfl) st sh h e.2 (gtInit e.1)) z.out.pv.gT _ _ h2
  convert h3 using 1 <;>
    simp only [idealInit, initialise, initialEntries, List.foldl_append, List.foldl_map, st]
  all_goals
    repeat' first
      | rfl
      | (funext s e; cases s.mark <;> rfl)
      | congr 1

lemma constants_projects {E : Type} [AddCommMonoid E] [Module k E]
    (value : E →ₗ[k] Coeff pp) (d : Label P0 → Option E) :
    Exposure.Projects value d (fun l => (d l).map (fun E => MvPolynomial.C (value E))) := by
  classical
  constructor
  · intro l
    cases hd : d l <;> simp [hd]
  · intro l E he
    exact ⟨MvPolynomial.C (value E), by simp [he]⟩

lemma const_projects (st : IdealState P0) (sh : State pp) (h : sh.dict = constDict pp v st) :
    Projects pp v st sh := by
  classical
  constructor
  all_goals rw [h]
  · exact constants_projects pp _ _
  · exact constants_projects pp _ _
  · exact constants_projects pp _ _

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync
