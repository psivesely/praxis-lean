import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Catalog

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

local instance : Fintype GroupModel.Sorted.PSort :=
  ⟨{.g₁,.g₂,.gₜ}, by intro s; cases s <;> simp⟩

variable (pp : PublicParams P0)

def operands : GQuery P0 → List GuessVar
  | .lin s _ _ u v => [(s,u), (s,v)]
  | .pair u v => [(.g₁,u), (.g₂,v)]
  | .name _ => []

def resultLabels : (q : GQuery P0) → q.Result → List GuessVar
  | .lin s _ _ _ _, some l => [(s,l)]
  | .pair _ _, some l => [(.gₜ,l)]
  | .name u, some nm => [(.gₜ,otherLabel u nm)]
  | _, _ => []

def groupLabels (q : GQuery P0) (a : q.Result) : List GuessVar :=
  operands q ++ resultLabels q a

def groupCount (xs : List (Step pp)) : ℕ :=
  (xs.map fun s => callCost s.entry.1 .group).sum

def keys (sh : State pp) : Finset GuessVar :=
  Finset.univ.filter fun v => (sh.dict v.1 v.2).isSome

def addedLabels (sh sh' : State pp) : List GuessVar :=
  (keys pp sh' \ keys pp sh).toList

def laterLabels (sh : State pp) : List (Step pp) → List GuessVar
  | [] => []
  | s :: xs => addedLabels pp sh s.shadow ++ laterLabels s.shadow xs

def labels (r : Record pp) : List GuessVar :=
  (keys pp (initialise pp r.forms r.pv)).toList ++
    laterLabels pp (initialise pp r.forms r.pv) r.steps

def oldPoly (sh : State pp) (v : GuessVar) : Poly pp :=
  (sh.dict v.1 v.2).getD (MvPolynomial.X v)

def newPoly (sh : State pp) : GQuery P0 → GroupModel.Sorted.PSort × Poly pp
  | .lin s a b u v => (s, scalar pp a * oldPoly pp sh (s,u) +
      scalar pp b * oldPoly pp sh (s,v))
  | .pair u v => (.gₜ, oldPoly pp sh (.g₁,u) * oldPoly pp sh (.g₂,v))
  | .name u => (.gₜ, -((sh.dict .gₜ u).getD 0))

lemma resolve_old (σ : LabelEncoding P0) (sh : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) (h : (resolve pp σ sh s l).1 = some P) :
    P = oldPoly pp sh (s,l) := by
  unfold resolve at h
  split at h
  · cases Option.some.inj h
    simp [oldPoly, ‹sh.dict s l = _›]
  · split at h
    · cases h
    · cases Option.some.inj h
      simp [oldPoly, ‹sh.dict s l = none›]

lemma resolve_dict (σ : LabelEncoding P0) (sh : State pp) (s t : GroupModel.Sorted.PSort)
    (l u : Label P0) :
    oldPoly pp (resolve pp σ sh s l).2 (t,u) = oldPoly pp sh (t,u) := by
  unfold resolve
  split
  · rfl
  · split
    · rfl
    · rename_i x hx
      by_cases ht : t = s
      · subst t
        by_cases hu : u = l
        · subst u
          simp [oldPoly, record, ‹sh.dict s l = none›]
        · simp [oldPoly, record, hu]
      · simp [oldPoly, record, ht]

lemma resolve_mono (σ : LabelEncoding P0) (sh : State pp) (s t : GroupModel.Sorted.PSort)
    (l u : Label P0) (P : Poly pp) (h : sh.dict t u = some P) :
    (resolve pp σ sh s l).2.dict t u = some P := by
  unfold resolve
  split
  · exact h
  · split
    · exact h
    · by_cases ht : t = s
      · subst t
        by_cases hu : u = l
        · subst u
          simp_all
        · simpa [record, hu] using h
      · simpa [record, ht] using h

lemma insert_mono (sh : State pp) (s t : GroupModel.Sorted.PSort)
    (l u : Label P0) (P R : Poly pp) (h : sh.dict t u = some P) :
    (insertResult pp sh s l R).dict t u = some P := by
  unfold insertResult
  split
  · by_cases ht : t = s
    · subst t
      by_cases hu : u = l
      · subst u; simp_all
      · simpa [record, hu] using h
    · simpa [record, ht] using h
  · split <;> exact h

lemma resolve_origin (σ : LabelEncoding P0) (sh : State pp)
    (s t : GroupModel.Sorted.PSort) (l u : Label P0) (P : Poly pp)
    (h : (resolve pp σ sh s l).2.dict t u = some P) :
    (sh.dict t u).isSome ∨ (t,u) = (s,l) := by
  unfold resolve at h
  split at h
  · exact Or.inl (by simpa only [← h] using (show (some P).isSome = true from rfl))
  · split at h
    · exact Or.inl (by simpa only [← h] using (show (some P).isSome = true from rfl))
    · by_cases ht : t = s
      · subst t
        by_cases hu : u = l
        · exact Or.inr (by simp [hu])
        · exact Or.inl (by simpa [record, hu] using Option.isSome_iff_exists.mpr ⟨P,h⟩)
      · exact Or.inl (by simpa [record, ht] using Option.isSome_iff_exists.mpr ⟨P,h⟩)

lemma insert_origin (sh : State pp) (s t : GroupModel.Sorted.PSort)
    (l u : Label P0) (P R : Poly pp)
    (h : (insertResult pp sh s l R).dict t u = some P) :
    (sh.dict t u).isSome ∨ (t,u) = (s,l) := by
  unfold insertResult at h
  split at h
  · by_cases ht : t = s
    · subst t
      by_cases hu : u = l
      · exact Or.inr (by simp [hu])
      · exact Or.inl (by simpa [record, hu] using Option.isSome_iff_exists.mpr ⟨P,h⟩)
    · exact Or.inl (by simpa [record, ht] using Option.isSome_iff_exists.mpr ⟨P,h⟩)
  · split at h <;> exact Or.inl (by simpa only [← h] using (show (some P).isSome = true from rfl))

lemma observe_mono (σ : LabelEncoding P0) (sh : State pp) (q : GQuery P0)
    (a : q.Result) (t : GroupModel.Sorted.PSort) (u : Label P0) (P : Poly pp)
    (h : sh.dict t u = some P) :
    (observeGroup pp σ sh q a).dict t u = some P := by
  cases q with
  | lin s a b v w =>
    have hx := resolve_mono pp σ sh s t v u P h
    have hy := resolve_mono pp σ (resolve pp σ sh s v).2 s t w u P hx
    simp only [observeGroup]
    split
    · exact insert_mono pp _ _ _ _ _ _ _ hy
    · exact hy
  | pair v w =>
    have hx := resolve_mono pp σ sh .g₁ t v u P h
    have hy := resolve_mono pp σ (resolve pp σ sh .g₁ v).2 .g₂ t w u P hx
    simp only [observeGroup]
    split
    · exact insert_mono pp _ _ _ _ _ _ _ hy
    · exact hy
  | name v =>
    cases a with
    | none => exact h
    | some nm => exact insert_mono pp _ _ _ _ _ _ _ h

lemma observe_origin (σ : LabelEncoding P0) (sh : State pp) (q : GQuery P0)
    (a : q.Result) (t : GroupModel.Sorted.PSort) (u : Label P0) (P : Poly pp)
    (h : (observeGroup pp σ sh q a).dict t u = some P) :
    (sh.dict t u).isSome ∨ (t,u) ∈ groupLabels q a := by
  cases q with
  | lin s a b v w =>
    have resolve_two (R : Poly pp)
        (hR : (resolve pp σ (resolve pp σ sh s v).2 s w).2.dict t u = some R) :
        (sh.dict t u).isSome ∨ (t,u) = (s,v) ∨ (t,u) = (s,w) := by
      rcases resolve_origin pp σ _ s t w u R hR with h | h
      · obtain ⟨R', hR'⟩ := Option.isSome_iff_exists.mp h
        exact (resolve_origin pp σ sh s t v u R' hR').imp_right Or.inl
      · exact Or.inr (Or.inr h)
    simp only [observeGroup] at h
    split at h
    · rcases insert_origin pp _ _ _ _ _ _ _ h with h | h
      · obtain ⟨R,hR⟩ := Option.isSome_iff_exists.mp h
        rcases resolve_two R hR with h | h | h
        · exact Or.inl h
        · exact Or.inr (by simp [groupLabels, operands, h])
        · exact Or.inr (by simp [groupLabels, operands, h])
      · exact Or.inr (by simp_all [groupLabels, resultLabels])
    · rcases resolve_two P h with h | h | h
      · exact Or.inl h
      · exact Or.inr (by simp [groupLabels, operands, h])
      · exact Or.inr (by simp [groupLabels, operands, h])
  | pair v w =>
    have resolve_two (R : Poly pp)
        (hR : (resolve pp σ (resolve pp σ sh .g₁ v).2 .g₂ w).2.dict t u = some R) :
        (sh.dict t u).isSome ∨ (t,u) = (.g₁,v) ∨ (t,u) = (.g₂,w) := by
      rcases resolve_origin pp σ _ .g₂ t w u R hR with h | h
      · obtain ⟨R', hR'⟩ := Option.isSome_iff_exists.mp h
        exact (resolve_origin pp σ sh .g₁ t v u R' hR').imp_right Or.inl
      · exact Or.inr (Or.inr h)
    simp only [observeGroup] at h
    split at h
    · rcases insert_origin pp _ _ _ _ _ _ _ h with h | h
      · obtain ⟨R,hR⟩ := Option.isSome_iff_exists.mp h
        rcases resolve_two R hR with h | h | h
        · exact Or.inl h
        · exact Or.inr (by simp [groupLabels, operands, h])
        · exact Or.inr (by simp [groupLabels, operands, h])
      · exact Or.inr (by simp_all [groupLabels, resultLabels])
    · rcases resolve_two P h with h | h | h
      · exact Or.inl h
      · exact Or.inr (by simp [groupLabels, operands, h])
      · exact Or.inr (by simp [groupLabels, operands, h])
  | name v =>
    cases a with
    | none => exact Or.inl (by simp_all [observeGroup])
    | some nm =>
      rcases insert_origin pp _ _ _ _ _ _ _ h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [groupLabels, operands, resultLabels, h])

lemma insert_collision (sh : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) (e : Collision pp)
    (hf : sh.first = none) (he : (insertResult pp sh s l P).first = some e) :
    e.sort = s ∧ e.new = P ∧ sh.dict s e.label = some e.old := by
  unfold insertResult at he
  split at he
  · simp [hf] at he
  · split at he
    · simp [hf] at he
    · simp only [hf, Option.orElse_none, Option.some.injEq] at he
      cases he
      exact ⟨rfl,rfl,‹sh.dict s l = _›⟩

lemma observe_collision (σ : LabelEncoding P0) (sh : State pp) (q : GQuery P0)
    (a : q.Result) (e : Collision pp) (hf : sh.first = none)
    (he : (observeGroup pp σ sh q a).first = some e) :
    e.sort = (newPoly pp sh q).1 ∧ e.new = (newPoly pp sh q).2 ∧
      e.old = oldPoly pp sh (e.sort,e.label) ∧
      ((sh.dict e.sort e.label).isSome ∨ (e.sort,e.label) ∈ operands q) := by
  cases q with
  | lin s a b u v =>
    have hx := resolve_first pp σ sh s u
    have hy := resolve_first pp σ (resolve pp σ sh s u).2 s v
    simp only [observeGroup] at he
    split at he
    · rename_i x y answer P Q l hP hQ
      obtain ⟨hs,hn,ho⟩ := insert_collision pp _ _ _ _ _ (hy.trans (hx.trans hf)) he
      have hp := resolve_old pp σ sh s u P hP
      have hq := (resolve_old pp σ _ s v Q hQ).trans (resolve_dict pp σ sh s s u v)
      have hold : e.old = oldPoly pp sh (s,e.label) := by
        calc e.old = oldPoly pp (resolve pp σ (resolve pp σ sh s u).2 s v).2
              (s,e.label) := by simp [oldPoly, ho]
             _ = oldPoly pp sh (s,e.label) := by rw [resolve_dict, resolve_dict]
      refine ⟨hs, ?_, ?_, ?_⟩
      · simpa [newPoly, hp, hq] using hn
      · simpa [hs] using hold
      · rw [hs]
        rcases resolve_origin pp σ _ s s v e.label e.old ho with h | h
        · obtain ⟨R,hR⟩ := Option.isSome_iff_exists.mp h
          rcases resolve_origin pp σ sh s s u e.label R hR with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [operands,h])
        · exact Or.inr (by simp [operands,h])
    · rw [hy,hx,hf] at he
      cases he
  | pair u v =>
    have hx := resolve_first pp σ sh .g₁ u
    have hy := resolve_first pp σ (resolve pp σ sh .g₁ u).2 .g₂ v
    simp only [observeGroup] at he
    split at he
    · rename_i x y answer P Q l hP hQ
      obtain ⟨hs,hn,ho⟩ := insert_collision pp _ _ _ _ _ (hy.trans (hx.trans hf)) he
      have hp := resolve_old pp σ sh .g₁ u P hP
      have hq := (resolve_old pp σ _ .g₂ v Q hQ).trans (resolve_dict pp σ sh .g₁ .g₂ u v)
      have hold : e.old = oldPoly pp sh (.gₜ,e.label) := by
        calc e.old = oldPoly pp (resolve pp σ (resolve pp σ sh .g₁ u).2 .g₂ v).2
              (.gₜ,e.label) := by simp [oldPoly,ho]
             _ = oldPoly pp sh (.gₜ,e.label) := by rw [resolve_dict,resolve_dict]
      refine ⟨hs, ?_, ?_, ?_⟩
      · simpa [newPoly,hp,hq] using hn
      · simpa [hs] using hold
      · rw [hs]
        rcases resolve_origin pp σ _ .g₂ .gₜ v e.label e.old ho with h | h
        · obtain ⟨R,hR⟩ := Option.isSome_iff_exists.mp h
          rcases resolve_origin pp σ sh .g₁ .gₜ u e.label R hR with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [operands,h])
        · exact Or.inr (by simp [operands,h])
    · rw [hy,hx,hf] at he
      cases he
  | name u =>
    cases a with
    | none => simp [observeGroup,hf] at he
    | some nm =>
      obtain ⟨hs,hn,ho⟩ := insert_collision pp _ _ _ _ _ hf he
      refine ⟨hs,hn,?_,Or.inl ?_⟩
      · simp [oldPoly,hs,ho]
      · simpa [hs] using Option.isSome_iff_exists.mpr ⟨e.old,ho⟩

def StepRel (σ : LabelEncoding P0) (sh : State pp) (s : Step pp) : Prop :=
  match s.entry.1 with
  | .inl (.inl (.inr q)) => ∃ a : q.Result, s.shadow = observeGroup pp σ sh q a
  | _ => s.shadow = sh

def lastShadow (init : State pp) (xs : List (Step pp)) : State pp :=
  ((xs.getLast?).map Step.shadow).getD init

inductive History (σ : LabelEncoding P0) (init : State pp) :
    List (Step pp) → State pp → Prop
  | nil : History σ init [] init
  | snoc {xs sh} (h : History σ init xs sh) (s : Step pp)
      (hs : StepRel pp σ sh s) :
      History σ init (xs ++ [s]) s.shadow

lemma history_last {σ : LabelEncoding P0} {init sh : State pp} {xs : List (Step pp)}
    (h : History pp σ init xs sh) : lastShadow pp init xs = sh := by
  cases h with
  | nil => rfl
  | snoc h s hs => simp [lastShadow]

lemma history_take {σ : LabelEncoding P0} {init sh : State pp} {xs : List (Step pp)}
    (h : History pp σ init xs sh) (n : ℕ) :
    History pp σ init (xs.take n) (lastShadow pp init (xs.take n)) := by
  induction h with
  | nil => simpa [lastShadow] using (History.nil (pp := pp) (σ := σ) (init := init))
  | @snoc xs sh h s hs ih =>
    by_cases hn : n ≤ xs.length
    · rw [List.take_append_of_le_length hn]
      exact ih
    · have hn : xs.length + 1 ≤ n := by omega
      rw [List.take_of_length_le (by simpa using hn), history_last pp (History.snoc h s hs)]
      exact History.snoc h s hs

lemma history_next {σ : LabelEncoding P0} {init sh : State pp} {xs : List (Step pp)}
    (h : History pp σ init xs sh) {n : ℕ} {s : Step pp} (hs : xs[n]? = some s) :
    StepRel pp σ (lastShadow pp init (xs.take n)) s := by
  induction h with
  | nil => simp at hs
  | @snoc xs sh h t ht ih =>
    by_cases hn : n < xs.length
    · rw [List.getElem?_append_left hn] at hs
      rw [List.take_append_of_le_length hn.le]
      exact ih hs
    · have hn' : n = xs.length := by
        have : n < (xs ++ [t]).length := List.getElem?_eq_some_iff.mp hs |>.1
        simp only [List.length_append,List.length_singleton] at this
        omega
      subst n
      simp only [List.getElem?_append_right (by omega : xs.length ≤ xs.length),
        Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at hs
      subst t
      simpa [List.take_append_of_le_length,history_last pp h] using ht

lemma step_mono (σ : LabelEncoding P0) (sh : State pp) (s : Step pp)
    (hs : StepRel pp σ sh s) (t : GroupModel.Sorted.PSort) (u : Label P0) (P : Poly pp)
    (h : sh.dict t u = some P) : s.shadow.dict t u = some P := by
  rcases hq : s.entry.1 with ((n | q) | i) | k
  · have he : s.shadow = sh := by simpa [StepRel,hq] using hs
    simpa [he] using h
  · obtain ⟨a,ha⟩ := (show ∃ a, s.shadow = observeGroup pp σ sh q a from by simpa [StepRel,hq] using hs)
    rw [ha]
    exact observe_mono pp σ sh q a t u P h
  · have he : s.shadow = sh := by simpa [StepRel,hq] using hs
    simpa [he] using h
  · have he : s.shadow = sh := by simpa [StepRel,hq] using hs
    simpa [he] using h

lemma history_mono {σ : LabelEncoding P0} {init sh : State pp} {xs : List (Step pp)}
    (h : History pp σ init xs sh) (n : ℕ) (t : GroupModel.Sorted.PSort)
    (u : Label P0) (P : Poly pp)
    (hp : (lastShadow pp init (xs.take n)).dict t u = some P) :
    sh.dict t u = some P := by
  induction h with
  | nil => simpa [lastShadow] using hp
  | @snoc xs sh h s hs ih =>
    by_cases hn : n ≤ xs.length
    · rw [List.take_append_of_le_length hn] at hp
      exact step_mono pp σ sh s hs t u P (ih hp)
    · rw [List.take_of_length_le (by simp; omega),history_last pp (History.snoc h s hs)] at hp
      exact hp

lemma mem_keys (sh : State pp) (v : GuessVar) :
    v ∈ keys pp sh ↔ (sh.dict v.1 v.2).isSome := by simp [keys]

lemma added_length (σ : LabelEncoding P0) (sh : State pp) (q : GQuery P0)
    (a : q.Result) : (addedLabels pp sh (observeGroup pp σ sh q a)).length ≤ 3 := by
  have hsub : keys pp (observeGroup pp σ sh q a) \ keys pp sh ⊆
      (groupLabels q a).toFinset := by
    intro v hv
    obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨P,hP⟩ := Option.isSome_iff_exists.mp ((mem_keys pp _ _).mp hv)
    exact List.mem_toFinset.mpr ((observe_origin pp σ sh q a v.1 v.2 P hP).resolve_left
      (by simpa [mem_keys] using hn))
  have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  have hl : (groupLabels q a).length ≤ 3 := by
    cases q <;> cases a <;> simp [groupLabels,operands,resultLabels]
  have hc' : (addedLabels pp sh (observeGroup pp σ sh q a)).length ≤ (groupLabels q a).length := by
    simpa [addedLabels] using hc
  exact hc'.trans hl

lemma step_added_length (σ : LabelEncoding P0) (sh : State pp) (s : Step pp)
    (hs : StepRel pp σ sh s) :
    (addedLabels pp sh s.shadow).length ≤ 3 * callCost s.entry.1 .group := by
  rcases hq : s.entry.1 with ((n | q) | i) | k
  · have he : s.shadow = sh := by simpa [StepRel,hq] using hs
    simp [he,addedLabels,hq,callCost,isGroupQuery]
  · obtain ⟨a,ha⟩ := (show ∃ a, s.shadow = observeGroup pp σ sh q a from by simpa [StepRel,hq] using hs)
    simpa [ha,hq,callCost,isGroupQuery] using added_length pp σ sh q a
  · have he : s.shadow = sh := by simpa [StepRel,hq] using hs
    simp [he,addedLabels,hq,callCost,isGroupQuery]
  · have he : s.shadow = sh := by simpa [StepRel,hq] using hs
    simp [he,addedLabels,hq,callCost,isGroupQuery]

lemma later_append (sh : State pp) (xs ys : List (Step pp)) :
    laterLabels pp sh (xs ++ ys) = laterLabels pp sh xs ++
      laterLabels pp (lastShadow pp sh xs) ys := by
  induction xs generalizing sh with
  | nil => simp [laterLabels,lastShadow]
  | cons x xs ih =>
    rw [List.cons_append,laterLabels,ih]
    simp [laterLabels,lastShadow,List.getLast?_cons,List.append_assoc]

lemma history_labels_length {σ : LabelEncoding P0} {init sh : State pp} {xs : List (Step pp)}
    (h : History pp σ init xs sh) :
    (laterLabels pp init xs).length ≤ 3 * groupCount pp xs := by
  induction h with
  | nil => simp [laterLabels,groupCount]
  | @snoc xs sh h s hs ih =>
    rw [later_append,history_last pp h]
    have hb := step_added_length pp σ sh s hs
    simp only [List.length_append,laterLabels,List.length_nil,Nat.add_zero,
      groupCount,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    simp only [groupCount] at ih
    omega

lemma history_labels_mem {σ : LabelEncoding P0} {init sh : State pp} {xs : List (Step pp)}
    (h : History pp σ init xs sh) (v : GuessVar) (hv : v ∈ keys pp sh) :
    v ∈ (keys pp init).toList ++ laterLabels pp init xs := by
  induction h with
  | nil => simpa [laterLabels] using hv
  | @snoc xs sh h s hs ih =>
    by_cases hm : v ∈ keys pp sh
    · have := ih hm
      rw [later_append,history_last pp h]
      simpa only [laterLabels,List.append_nil,List.append_assoc] using
        (List.mem_append_left (addedLabels pp sh s.shadow) this)
    · rw [later_append,history_last pp h]
      simp [laterLabels,addedLabels,hv,hm]

lemma initial_keys (forms : FormMatrix P0) (pv : PubView P0) :
    (keys pp (initialise pp forms pv)).card ≤ (initialEntries pp forms pv).length := by
  have aux (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (sh : State pp) :
      (keys pp (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) sh)).card ≤
        (keys pp sh).card + es.length := by
    induction es generalizing sh with
    | nil => simp
    | cons e es ih =>
      have hsub : keys pp (insertResult pp sh e.1 e.2.1 e.2.2) ⊆
          insert (e.1,e.2.1) (keys pp sh) := by
        intro v hv
        obtain ⟨P,hP⟩ := Option.isSome_iff_exists.mp ((mem_keys pp _ _).mp hv)
        rcases insert_origin pp sh e.1 v.1 e.2.1 v.2 P e.2.2 hP with h | h
        · exact Finset.mem_insert_of_mem ((mem_keys pp _ _).mpr h)
        · have hv : v = (e.1,e.2.1) := h
          rw [hv]
          exact Finset.mem_insert_self _ _
      have hb := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      have hi := ih (insertResult pp sh e.1 e.2.1 e.2.2)
      simpa only [List.foldl_cons,List.length_cons] using (by omega :
        (keys pp (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2)
          (insertResult pp sh e.1 e.2.1 e.2.2))).card ≤ (keys pp sh).card + (es.length+1))
  have := aux (initialEntries pp forms pv) (empty pp)
  have he : keys pp (empty pp) = ∅ := by ext v; simp [keys,empty]
  simpa only [initialise,he,Finset.card_empty,Nat.zero_add] using this

def StopCorrect (st : ObsState pp) : Prop :=
  (∀ b, st.stop = some b → b < st.steps.length) ∧
  ∀ n s, st.steps[n]? = some s → s.shadow.first.isSome →
    ∃ b, st.stop = some b ∧ b ≤ n

lemma obs_invariant (σ : LabelEncoding P0) (c : Coins P0) (init : State pp)
    {α : Type} (oa : OracleComp (AdvModel P0) α) (st : ObsState pp)
    (hh : History pp σ init st.steps st.shadow) (hb : StopCorrect pp st) :
    ∀ z ∈ support ((simulateQ (obsHandler pp σ c) oa).run st),
      History pp σ init z.2.steps z.2.shadow ∧ StopCorrect pp z.2 := by
  apply simulateQ_run_preserves_inv_of_query (obsHandler pp σ c)
    (fun st => History pp σ init st.steps st.shadow ∧ StopCorrect pp st) ?_ oa st ⟨hh,hb⟩
  intro q st hst z hz
  simp only [obsHandler,StateT.run_mk,support_map,Set.mem_image] at hz
  obtain ⟨y,hy,rfl⟩ := hz
  let sh := match q with
    | .inl (.inl (.inr gq)) => observeGroup pp σ st.shadow gq (groupAnswer σ st.oracle.issuedT gq)
    | _ => st.shadow
  let ord := match q with
    | .inl (.inl (.inr gq)) => st.order ++ newGuesses pp st.shadow sh gq
    | _ => st.order
  let ss : Step pp := ⟨⟨q,y.1⟩,sh,ord⟩
  have hs : StepRel pp σ st.shadow ss := by
    rcases q with ((n | q) | i) | k
    · rfl
    · exact ⟨groupAnswer σ st.oracle.issuedT q,rfl⟩
    · rfl
    · rfl
  refine ⟨History.snoc hst.1 ss hs, ?_⟩
  constructor
  · intro b hb
    change st.stop.orElse _ = some b at hb
    change b < (st.steps ++ [ss]).length
    cases hold : st.stop with
    | none =>
      simp only [hold,Option.orElse_none] at hb
      split_ifs at hb with hbad
      · cases Option.some.inj hb
        simp
    | some b' =>
      simp only [hold,Option.orElse_some,Option.some.injEq] at hb
      subst b'
      have := hst.2.1 b hold
      simp only [List.length_append,List.length_singleton]
      omega
  intro n s hn hfirst
  change (st.steps ++ [ss])[n]? = some s at hn
  by_cases hn' : n < st.steps.length
  · rw [List.getElem?_append_left hn'] at hn
    obtain ⟨b,hb,hbn⟩ := hst.2.2 n s hn hfirst
    refine ⟨b,?_,hbn⟩
    change st.stop.orElse _ = some b
    simp [hb]
  · have hlen := (List.getElem?_eq_some_iff.mp hn).1
    have he : n = st.steps.length := by simp only [List.length_append,List.length_singleton] at hlen; omega
    subst n
    simp only [List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero,
      Option.some.injEq] at hn
    subst s
    cases hb : st.stop with
    | none =>
      refine ⟨st.steps.length,?_,le_rfl⟩
      dsimp only
      simp only [Option.orElse_none]
      exact if_pos (Or.inl hfirst)
    | some b =>
      have hbound : b ≤ st.steps.length := (hst.2.1 b hb).le
      exact ⟨b,by simp [hb],hbound⟩

lemma observed_history [Nonempty {c : Coins P0 // ValidCoins pp.qap c}]
    (m : Msg P0) (A : Adversary P0) (ω : World pp)
    (hω : ω ∈ support (observedRun pp m A)) :
    History pp ω.1.enc (initialise pp ω.1.out.forms ω.1.out.pv) ω.2.steps ω.2.shadow ∧
      StopCorrect pp ω.2 := by
  unfold observedRun at hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨σ,hσ,hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨e,he,hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨z,hz,hω⟩ := hω
  simp only [support_pure,Set.mem_singleton_iff] at hω
  cases hω
  exact obs_invariant pp σ e.1.coins (initialise pp e.1.forms e.1.pv)
    (A.run e.1.pv e.1.header) _ History.nil (by constructor <;> simp) z hz

lemma counted_support (σ : LabelEncoding P0) (c : Coins P0) {α : Type}
    (oa : OracleComp (AdvModel P0) α) (st : ObsState pp)
    (z : α × ObsState pp) (hz : z ∈ support ((simulateQ (obsHandler pp σ c) oa).run st)) :
    ∃ z' ∈ support (((simulateQ ((gameImpl σ).withCost callCost) oa).run).run st.oracle),
      z'.1.1 = z.1 ∧ z'.2 = z.2.oracle ∧
        groupCount pp z.2.steps = groupCount pp st.steps + z'.1.2 .group := by
  induction oa using OracleComp.inductionOn generalizing st z with
  | pure a =>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at hz
    subst z
    refine ⟨((a,0),st.oracle),?_,rfl,rfl,?_⟩
    · simp
    · simp
  | query_bind q cont ih =>
    simp only [simulateQ_bind,simulateQ_query,OracleQuery.input_query,
      OracleQuery.cont_query,id_map,StateT.run_bind] at hz
    obtain ⟨y,hy,hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    simp only [obsHandler,StateT.run_mk,support_map,Set.mem_image] at hy
    obtain ⟨w,hw,hy⟩ := hy
    subst y
    obtain ⟨v,hv,ha,ho,hc⟩ := ih w.1 _ z hz
    have step : (((simulateQ ((gameImpl σ).withCost callCost)
        ((liftM (OracleSpec.query q) : OracleComp (AdvModel P0) _) >>= cont)).run).run st.oracle) =
        ((gameImpl σ q).run st.oracle >>= fun us =>
          (fun v => ((v.1.1,callCost q + v.1.2),v.2)) <$>
            (((simulateQ ((gameImpl σ).withCost callCost) (cont us.1)).run).run us.2)) := by
      simp [simulateQ_bind,QueryImpl.withCost_apply,WriterT.run_bind,StateT.run_bind,monad_norm]
    rw [step]
    refine ⟨((v.1.1,callCost q + v.1.2),v.2),?_,ha,ho,?_⟩
    · exact (mem_support_bind_iff _ _ _).mpr ⟨w,hw,by rw [support_map]; exact ⟨v,hv,rfl⟩⟩
    · simp only [groupCount,List.map_append,List.sum_append,List.map_singleton,
        List.sum_singleton] at hc ⊢
      change _ = _ + (callCost q .group + v.1.2 .group)
      change _ = _ + callCost q .group + v.1.2 .group at hc
      omega

lemma observed_count [Nonempty {c : Coins P0 // ValidCoins pp.qap c}]
    (m : Msg P0) (A : Adversary P0) (Q : ℕ) (hA : MaxCalls A .group Q)
    (ω : World pp) (hω : ω ∈ support (observedRun pp m A)) : groupCount pp ω.2.steps ≤ Q := by
  unfold observedRun at hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨σ,hσ,hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨e,he,hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨z,hz,hω⟩ := hω
  simp only [support_pure,Set.mem_singleton_iff] at hω
  cases hω
  obtain ⟨v,hv,ha,ho,hc⟩ := counted_support pp σ e.1.coins (A.run e.1.pv e.1.header) _ z hz
  have hcv : ((e.1,v.1),v.2) ∈ support (countedRun σ A pp m) := by
    unfold countedRun
    simp only [StateT.run_bind,mem_support_bind_iff]
    exact ⟨e,he,v,hv,by simp⟩
  have hb := hA σ pp m _ hcv
  change groupCount pp z.2.steps ≤ Q
  rw [hc]
  simpa only [groupCount,List.map_nil,List.sum_nil,Nat.zero_add] using hb

lemma groupCount_take_le (xs : List (Step pp)) (n : ℕ) :
    groupCount pp (xs.take n) ≤ groupCount pp xs := by
  have h : groupCount pp xs = groupCount pp (xs.take n) + groupCount pp (xs.drop n) := by
    conv_lhs => rw [← List.take_append_drop n xs]
    simp [groupCount]
  omega

lemma groupCount_before_lt (xs : List (Step pp)) (b : ℕ) (s : Step pp)
    (hs : xs[b]? = some s) (q : GQuery P0) (hq : s.entry.1 = .inl (.inl (.inr q))) :
    groupCount pp (xs.take b) < groupCount pp xs := by
  have he : xs.take (b+1) = xs.take b ++ [s] := by
    simpa [hs] using (List.take_add_one (l := xs) (i := b))
  have hle := groupCount_take_le pp xs (b+1)
  rw [he] at hle
  have hg : groupCount pp (xs.take b ++ [s]) = groupCount pp (xs.take b) + 1 := by
    simp [groupCount,hq,callCost,isGroupQuery]
  rw [hg] at hle
  omega

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Catalog
