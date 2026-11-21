import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.View.NoKey
import Praxis.Reduction
import Praxis.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.BadNe

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0) (forms : FormMatrix P0)

def valueSpace : GroupModel.Sorted.PSort → Submodule k (Exposure.Coeff pp)
  | .g₁ => LinearMap.range (Exposure.value1 pp)
  | .g₂ => LinearMap.range (Exposure.value2 pp (formVec forms))
  | .gₜ => LinearMap.range (Exposure.valueT pp (formVec forms))

def Typed (s : GroupModel.Sorted.PSort) (p : Poly pp) : Prop :=
  MvPolynomial.constantCoeff p ∈ valueSpace pp forms s

def Inv (st : State pp) : Prop :=
  (∀ s l p, st.dict s l = some p → Typed pp forms s p) ∧
    ∀ e, st.first = some e → e.new ≠ e.old

lemma typed_zero (s : GroupModel.Sorted.PSort) : Typed pp forms s 0 := by
  unfold Typed
  rw [map_zero]
  exact (valueSpace pp forms s).zero_mem

lemma typed_X (s : GroupModel.Sorted.PSort) (v : GuessVar) :
    Typed pp forms s (MvPolynomial.X v) := by
  simp only [Typed, MvPolynomial.constantCoeff_X]
  exact (valueSpace pp forms s).zero_mem

lemma typed_add (s : GroupModel.Sorted.PSort) {p q : Poly pp}
    (hp : Typed pp forms s p) (hq : Typed pp forms s q) :
    Typed pp forms s (p + q) := by
  unfold Typed
  rw [map_add]
  exact (valueSpace pp forms s).add_mem hp hq

lemma typed_neg (s : GroupModel.Sorted.PSort) {p : Poly pp}
    (hp : Typed pp forms s p) : Typed pp forms s (-p) := by
  unfold Typed
  rw [map_neg]
  exact (valueSpace pp forms s).neg_mem hp

lemma typed_scalar (s : GroupModel.Sorted.PSort) (a : k) {p : Poly pp}
    (hp : Typed pp forms s p) : Typed pp forms s (scalar pp a * p) := by
  unfold Typed scalar
  rw [map_mul, MvPolynomial.constantCoeff_C]
  exact (valueSpace pp forms s).smul_mem a hp

lemma typed_pair {p q : Poly pp} (hp : Typed pp forms .g₁ p)
    (hq : Typed pp forms .g₂ q) : Typed pp forms .gₜ (p * q) := by
  obtain ⟨E, hE⟩ := hp
  obtain ⟨F, hF⟩ := hq
  refine ⟨pairExpr E F, ?_⟩
  rw [Exposure.value_pair, map_mul, hE, hF]

lemma record_inv (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (p : Poly pp) (hi : Inv pp forms st) (hp : Typed pp forms s p) :
    Inv pp forms {st with dict := record pp st.dict s l p} := by
  refine ⟨?_, hi.2⟩
  intro s' l' q hq
  by_cases hs : s' = s
  · subst s'
    by_cases hl : l' = l
    · subst l'
      have he : p = q := Option.some.inj (by simpa [record] using hq)
      exact he ▸ hp
    · exact hi.1 s l' q (by simpa [record, hl] using hq)
  · exact hi.1 s' l' q (by simpa [record, hs] using hq)

lemma resolve_inv (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (hi : Inv pp forms st) :
    Inv pp forms (resolve pp σ st s l).2 ∧
      ∀ p, (resolve pp σ st s l).1 = some p → Typed pp forms s p := by
  unfold resolve
  split
  · rename_i p hp
    exact ⟨hi, fun q hq => (Option.some.inj hq) ▸ hi.1 s l p hp⟩
  · split
    · exact ⟨hi, by simp⟩
    · refine ⟨?_, ?_⟩
      · exact ⟨(record_inv pp forms st s l _ hi (typed_X pp forms s _)).1, hi.2⟩
      · intro p hp
        cases Option.some.inj hp
        exact typed_X pp forms s _

lemma insertResult_inv (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (p : Poly pp) (hi : Inv pp forms st) (hp : Typed pp forms s p) :
    Inv pp forms (insertResult pp st s l p) := by
  unfold insertResult
  split
  · exact record_inv pp forms st s l p hi hp
  · split
    · exact hi
    · rename_i q hq hne
      refine ⟨hi.1, ?_⟩
      intro e he
      cases hf : st.first with
      | none =>
        simp only [hf, Option.orElse_none, Option.some.injEq] at he
        cases he
        exact hne
      | some e' =>
        simp only [hf, Option.orElse_some, Option.some.injEq] at he
        exact he ▸ hi.2 e' hf

lemma observeGroup_inv (σ : LabelEncoding P0) (st : State pp) (q : GQuery P0)
    (answer : q.Result) (hi : Inv pp forms st) :
    Inv pp forms (observeGroup pp σ st q answer) := by
  cases q with
  | lin s a b u v =>
    let x := resolve pp σ st s u
    let y := resolve pp σ x.2 s v
    have hx := resolve_inv pp forms σ st s u hi
    have hy := resolve_inv pp forms σ x.2 s v hx.1
    change Inv pp forms (match x.1, y.1, answer with
      | some p, some q, some l => insertResult pp y.2 s l (scalar pp a * p + scalar pp b * q)
      | _, _, _ => y.2)
    cases hp : x.1 with
    | none => simpa only [hp] using hy.1
    | some p =>
      cases hq : y.1 with
      | none => simpa only [hp, hq] using hy.1
      | some q =>
        cases ha : answer with
        | none => simpa only [hp, hq, ha] using hy.1
        | some l =>
          exact insertResult_inv pp forms y.2 s l _ hy.1
            (typed_add pp forms s (typed_scalar pp forms s a (hx.2 p hp))
              (typed_scalar pp forms s b (hy.2 q hq)))
  | pair u v =>
    let x := resolve pp σ st .g₁ u
    let y := resolve pp σ x.2 .g₂ v
    have hx := resolve_inv pp forms σ st .g₁ u hi
    have hy := resolve_inv pp forms σ x.2 .g₂ v hx.1
    change Inv pp forms (match x.1, y.1, answer with
      | some p, some q, some l => insertResult pp y.2 .gₜ l (p * q)
      | _, _, _ => y.2)
    cases hp : x.1 with
    | none => simpa only [hp] using hy.1
    | some p =>
      cases hq : y.1 with
      | none => simpa only [hp, hq] using hy.1
      | some q =>
        cases ha : answer with
        | none => simpa only [hp, hq, ha] using hy.1
        | some l =>
          exact insertResult_inv pp forms y.2 .gₜ l _ hy.1
            (typed_pair pp forms (hx.2 p hp) (hy.2 q hq))
  | name u =>
    cases answer with
    | none => exact hi
    | some nm =>
      apply insertResult_inv pp forms st .gₜ _ _ hi
      apply typed_neg
      cases hd : st.dict .gₜ u with
      | none => exact typed_zero pp forms .gₜ
      | some p => exact hi.1 .gₜ u p hd

lemma initialise_inv (pv : PubView P0) : Inv pp forms (initialise pp forms pv) := by
  have hfold (entries : List (GroupModel.Sorted.PSort × Label P0 × Poly pp))
      (st : State pp) (hi : Inv pp forms st)
      (ht : ∀ e ∈ entries, Typed pp forms e.1 e.2.2) :
      Inv pp forms (entries.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st) := by
    induction entries generalizing st with
    | nil => exact hi
    | cons e es ih =>
      exact ih _ (insertResult_inv pp forms st _ _ _ hi (ht e (by simp)))
        (fun f hf => ht f (List.mem_cons_of_mem e hf))
  apply hfold
  · exact ⟨by simp [empty], by simp [empty]⟩
  · intro e he
    simp only [initialEntries, List.mem_append, List.mem_map] at he
    rcases he with (⟨e', _, rfl⟩ | ⟨e', _, rfl⟩) | ⟨e', _, rfl⟩
    · simp only [Typed, base1, MvPolynomial.constantCoeff_C, valueSpace]
      exact ⟨Pi.single e'.1 1, rfl⟩
    · simp only [Typed, base2, MvPolynomial.constantCoeff_C, valueSpace]
      exact ⟨Pi.single e'.1 1, rfl⟩
    · simp only [Typed, baseT, MvPolynomial.constantCoeff_C, valueSpace]
      exact ⟨gtInit e'.1, rfl⟩

def ObsInv (st : ObsState pp) : Prop :=
  Inv pp forms st.shadow ∧ ∀ step ∈ st.steps, Inv pp forms step.shadow

lemma obsHandler_inv (σ : LabelEncoding P0) (c : Coins P0)
    (q : (AdvModel P0).Domain) (st : ObsState pp) (hi : ObsInv pp forms st) :
    ∀ y ∈ support ((obsHandler pp σ c q).run st), ObsInv pp forms y.2 := by
  have hsh : Inv pp forms (match q with
      | .inl (.inl (.inr gq)) =>
        observeGroup pp σ st.shadow gq (groupAnswer σ st.oracle.issuedT gq)
      | _ => st.shadow) := by
    rcases q with ((n | gq) | i) | kq
    · exact hi.1
    · exact observeGroup_inv pp forms σ st.shadow gq _ hi.1
    · exact hi.1
    · exact hi.1
  intro y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨z, _, rfl⟩ := hy
  refine ⟨hsh, ?_⟩
  intro step hstep
  rcases List.mem_append.mp hstep with hold | hnew
  · exact hi.2 step hold
  · have heq := List.mem_singleton.mp hnew
    subst step
    exact hsh

lemma observed_inv [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0)
    (ω : World pp) (hω : ω ∈ support (observedRun pp m A)) :
    ObsInv pp ω.1.out.forms ω.2 := by
  unfold observedRun at hω
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hω
  obtain ⟨σ, _, e, _, z, hz, rfl⟩ := hω
  have hi : ObsInv pp e.1.forms
      (⟨e.2, initialise pp e.1.forms e.1.pv, [], [], none⟩ : ObsState pp) :=
    ⟨initialise_inv pp e.1.forms e.1.pv, by simp⟩
  exact simulateQ_run_preserves_inv_of_query (obsHandler pp σ e.1.coins)
    (ObsInv pp e.1.forms) (obsHandler_inv pp e.1.forms σ e.1.coins)
    (A.run e.1.pv e.1.header) _ hi z hz

lemma keyCmp_ne (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (z : WorldOut P0) (st : State (ppOf ch S)) (hi : Inv (ppOf ch S) z.out.forms st)
    (e : Collision (ppOf ch S)) (he : keyCmp (ppOf ch S) z st = some e) :
    e.new ≠ e.old := by
  unfold keyCmp at he
  split at he
  · rename_i p hp
    cases Option.some.inj he
    intro heq
    change p = key (ppOf ch S) at heq
    obtain ⟨D, hD⟩ := hi.1 .gₜ _ p hp
    apply View.view_no_formal_key ch S hS z.out.forms D
    apply (Exposure.valueKey_eq_iff (ppOf ch S) _ D).mp
    rw [hD, heq]
    simp only [key, MvPolynomial.constantCoeff_C]
    rfl
  · split at he
    · rename_i p hp
      cases Option.some.inj he
      intro heq
      change scalar (ppOf ch S) (-1) * p = key (ppOf ch S) at heq
      obtain ⟨D, hD⟩ := hi.1 .gₜ _ p hp
      apply View.view_no_formal_key ch S hS z.out.forms ((-1 : k) • D)
      apply (Exposure.valueKey_eq_iff (ppOf ch S) _ _).mp
      rw [map_smul, hD]
      have hc := congrArg MvPolynomial.constantCoeff heq
      simp only [map_mul, scalar, MvPolynomial.constantCoeff_C, key] at hc
      funext a
      simpa only [Pi.smul_apply, smul_eq_mul, Exposure.valueKey, Pi.mul_apply] using congrFun hc a
    · simp at he

lemma bad_ne (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)
    (hS : InShape P0 S) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A))
    (e : Collision (ppOf ch S)) (he : BadAt ω e) : e.new ≠ e.old := by
  have hi := observed_inv (ppOf ch S) m A
  generalize observedRun (ppOf ch S) m A = obs at hi hω ⊢
  have hsteps := (hi ω hω).2
  obtain ⟨b, hb, _, he⟩ := he
  unfold badCmp at he
  simp only [hb] at he
  cases hstep : ω.2.steps[b]? with
  | none => simp [hstep] at he
  | some step =>
    simp only [hstep] at he
    have hs := hsteps step (List.mem_of_getElem? hstep)
    rcases hq : step.entry.1 with ((n | gq) | i) | kq
    · simp [hq] at he
    · exact hs.2 e (by simpa only [hq] using he)
    · simp [hq] at he
    · exact keyCmp_ne ch S hS ω.1 step.shadow hs e (by simpa only [hq] using he)

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.BadNe
