import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
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
import Praxis.Reduction
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.BadTyped

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0) (forms : FormMatrix P0)

def space : GroupModel.Sorted.PSort → Submodule k (Coeff pp)
  | .g₁ => LinearMap.range (Exposure.value1 pp)
  | .g₂ => LinearMap.range (Exposure.value2 pp (formVec forms))
  | .gₜ => LinearMap.range (Exposure.valueT pp (formVec forms))

def Typed (st : State pp) : Prop :=
  (∀ s l P, st.dict s l = some P → MvPolynomial.constantCoeff P ∈ space pp forms s) ∧
  (∀ e, st.first = some e →
    MvPolynomial.constantCoeff e.new ∈ space pp forms e.sort ∧
    MvPolynomial.constantCoeff e.old ∈ space pp forms e.sort)

lemma record_typed (st : State pp) (hs : Typed pp forms st)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hp : MvPolynomial.constantCoeff P ∈ space pp forms s) :
    Typed pp forms {st with dict := record pp st.dict s l P} := by
  refine ⟨?_, hs.2⟩
  intro t u Q hQ
  by_cases ht : t = s
  · subst t
    by_cases hu : u = l
    · subst u
      have he : P = Q := Option.some.inj (by simpa [record] using hQ)
      simpa [← he] using hp
    · exact hs.1 s u Q (by simpa [record, hu] using hQ)
  · exact hs.1 t u Q (by simpa [record, ht] using hQ)

lemma resolve_typed (σ : LabelEncoding P0) (st : State pp) (hs : Typed pp forms st)
    (s : GroupModel.Sorted.PSort) (l : Label P0) :
    Typed pp forms (resolve pp σ st s l).2 ∧
      ∀ P, (resolve pp σ st s l).1 = some P →
        MvPolynomial.constantCoeff P ∈ space pp forms s := by
  unfold resolve
  split
  · rename_i P hP
    refine ⟨hs, ?_⟩
    intro Q hQ
    cases Option.some.inj hQ
    exact hs.1 s l P hP
  · split
    · exact ⟨hs, by simp⟩
    · constructor
      · apply record_typed pp forms st hs
        simp
      · intro P hP
        cases Option.some.inj hP
        simp

lemma insert_typed (st : State pp) (hs : Typed pp forms st)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hp : MvPolynomial.constantCoeff P ∈ space pp forms s) :
    Typed pp forms (insertResult pp st s l P) := by
  unfold insertResult
  split
  · exact record_typed pp forms st hs s l P hp
  · rename_i Q hQ
    split
    · exact hs
    · refine ⟨hs.1, ?_⟩
      intro e he
      cases hf : st.first with
      | none =>
        simp only [hf, Option.orElse_none, Option.some.injEq] at he
        cases he
        exact ⟨hp, hs.1 s l Q hQ⟩
      | some e' =>
        simp only [hf, Option.orElse_some, Option.some.injEq] at he
        exact he ▸ hs.2 e' hf

lemma linear_mem (s : GroupModel.Sorted.PSort) (a b : k) (P Q : Poly pp)
    (hp : MvPolynomial.constantCoeff P ∈ space pp forms s)
    (hq : MvPolynomial.constantCoeff Q ∈ space pp forms s) :
    MvPolynomial.constantCoeff (scalar pp a * P + scalar pp b * Q) ∈ space pp forms s := by
  simp only [map_add, map_mul, scalar, MvPolynomial.constantCoeff_C]
  exact (space pp forms s).add_mem ((space pp forms s).smul_mem a hp)
    ((space pp forms s).smul_mem b hq)

lemma pair_mem (P Q : Poly pp)
    (hp : MvPolynomial.constantCoeff P ∈ space pp forms .g₁)
    (hq : MvPolynomial.constantCoeff Q ∈ space pp forms .g₂) :
    MvPolynomial.constantCoeff (P * Q) ∈ space pp forms .gₜ := by
  obtain ⟨E, hE⟩ := hp
  obtain ⟨F, hF⟩ := hq
  exact ⟨pairExpr E F, by rw [Exposure.value_pair, hE, hF, map_mul]⟩

lemma observe_typed (σ : LabelEncoding P0) (st : State pp) (hs : Typed pp forms st)
    (q : GQuery P0) (answer : q.Result) :
    Typed pp forms (observeGroup pp σ st q answer) := by
  cases q with
  | lin s a b u v =>
    let x := resolve pp σ st s u
    let y := resolve pp σ x.2 s v
    have hx := resolve_typed pp forms σ st hs s u
    have hy := resolve_typed pp forms σ x.2 hx.1 s v
    change Typed pp forms (match x.1, y.1, answer with
      | some P, some Q, some l => insertResult pp y.2 s l (scalar pp a * P + scalar pp b * Q)
      | _, _, _ => y.2)
    cases hp : x.1 with
    | none => simpa [hp] using hy.1
    | some P =>
      cases hq : y.1 with
      | none => simpa [hp, hq] using hy.1
      | some Q =>
        cases answer with
        | none => simpa [hp, hq] using hy.1
        | some l =>
          exact insert_typed pp forms _ hy.1 s l _
            (linear_mem pp forms s a b P Q (hx.2 P hp) (hy.2 Q hq))
  | pair u v =>
    let x := resolve pp σ st .g₁ u
    let y := resolve pp σ x.2 .g₂ v
    have hx := resolve_typed pp forms σ st hs .g₁ u
    have hy := resolve_typed pp forms σ x.2 hx.1 .g₂ v
    change Typed pp forms (match x.1, y.1, answer with
      | some P, some Q, some l => insertResult pp y.2 .gₜ l (P * Q)
      | _, _, _ => y.2)
    cases hp : x.1 with
    | none => simpa [hp] using hy.1
    | some P =>
      cases hq : y.1 with
      | none => simpa [hp, hq] using hy.1
      | some Q =>
        cases answer with
        | none => simpa [hp, hq] using hy.1
        | some l =>
          exact insert_typed pp forms _ hy.1 .gₜ l _
            (pair_mem pp forms P Q (hx.2 P hp) (hy.2 Q hq))
  | name u =>
    cases answer with
    | none => exact hs
    | some nm =>
      apply insert_typed pp forms st hs
      rw [map_neg]
      apply (space pp forms .gₜ).neg_mem
      cases hu : st.dict .gₜ u with
      | none => simp
      | some P => exact hs.1 .gₜ u P hu

lemma initial_typed (pv : PubView P0) : Typed pp forms (initialise pp forms pv) := by
  have hentry : ∀ e ∈ initialEntries pp forms pv,
      MvPolynomial.constantCoeff e.2.2 ∈ space pp forms e.1 := by
    intro e he
    simp only [initialEntries, List.mem_append, List.mem_map] at he
    rcases he with (⟨e', _, rfl⟩ | ⟨e', _, rfl⟩) | ⟨e', _, rfl⟩
    · exact ⟨Pi.single e'.1 1, by simp [base1]; rfl⟩
    · exact ⟨Pi.single e'.1 1, by simp [base2]; rfl⟩
    · exact ⟨gtInit e'.1, by simp [baseT]; rfl⟩
  have hfold (entries : List (GroupModel.Sorted.PSort × Label P0 × Poly pp))
      (st : State pp) (hs : Typed pp forms st)
      (hv : ∀ e ∈ entries, MvPolynomial.constantCoeff e.2.2 ∈ space pp forms e.1) :
      Typed pp forms (entries.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st) := by
    induction entries generalizing st with
    | nil => exact hs
    | cons e es ih =>
      apply ih _ (insert_typed pp forms st hs _ _ _ (hv e (by simp)))
      exact fun e' he' => hv e' (List.mem_cons_of_mem e he')
  apply hfold _ _ ?_ hentry
  constructor
  · intro s l P h; simp [empty] at h
  · intro e h; simp [empty] at h

def ObsTyped (st : ObsState pp) : Prop :=
  Typed pp forms st.shadow ∧ ∀ s ∈ st.steps, Typed pp forms s.shadow

lemma handler_typed (σ : LabelEncoding P0) (c : Coins P0)
    (q : (AdvModel P0).Domain) (st : ObsState pp) (hs : ObsTyped pp forms st) :
    ∀ y ∈ support ((obsHandler pp σ c q).run st), ObsTyped pp forms y.2 := by
  have ht : Typed pp forms (match q with
      | .inl (.inl (.inr gq)) =>
        observeGroup pp σ st.shadow gq (groupAnswer σ st.oracle.issuedT gq)
      | _ => st.shadow) := by
    rcases q with ((n | gq) | i) | kq
    · exact hs.1
    · exact observe_typed pp forms σ st.shadow hs.1 gq _
    · exact hs.1
    · exact hs.1
  intro y hy
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨z, _, rfl⟩ := hy
  refine ⟨ht, ?_⟩
  intro s hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · exact hs.2 s hmem
  · exact ht

lemma observed_typed [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0)
    (ω : World pp) (hω : ω ∈ support (observedRun pp m A)) :
    ObsTyped pp ω.1.out.forms ω.2 := by
  simp only [observedRun, support_bind, Set.mem_iUnion, support_pure,
    Set.mem_singleton_iff] at hω
  obtain ⟨σ, _, e, _, z, hz, rfl⟩ := hω
  exact simulateQ_run_preserves_inv_of_query (obsHandler pp σ e.1.coins)
    (ObsTyped pp e.1.forms) (handler_typed pp e.1.forms σ e.1.coins)
    (A.run e.1.pv e.1.header) _ ⟨initial_typed pp e.1.forms e.1.pv, by simp⟩ z hz

def Conclusion (e : Collision pp) : Prop :=
  (e.sort = .g₁ → ∃ E : Expr1 P0, e.value = Exposure.value1 pp E) ∧
  (e.sort = .g₂ → ∃ E : Expr2 P0,
    e.value = Exposure.value2 pp (formVec forms) E) ∧
  (e.sort = .gₜ → ∃ (D : ExprT P0) (ι : k),
    e.value = Exposure.valueT pp (formVec forms) D - ι • Exposure.valueKey pp)

lemma conclusion_of_mem (e : Collision pp) (h : e.value ∈ space pp forms e.sort) :
    Conclusion pp forms e := by
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    rw [hs] at h
    obtain ⟨E, hE⟩ := h
    exact ⟨E, hE.symm⟩
  · intro hs
    rw [hs] at h
    obtain ⟨E, hE⟩ := h
    exact ⟨E, hE.symm⟩
  · intro hs
    rw [hs] at h
    obtain ⟨E, hE⟩ := h
    exact ⟨E, 0, by simp [hE]⟩

lemma keyCmp_typed (z : WorldOut P0) (st : State pp) (hs : Typed pp forms st)
    (e : Collision pp) (he : keyCmp pp z st = some e) : Conclusion pp forms e := by
  unfold keyCmp at he
  split at he
  · rename_i P hP
    cases Option.some.inj he
    obtain ⟨D, hD⟩ := hs.1 .gₜ _ P hP
    refine ⟨by simp, by simp, ?_⟩
    intro _
    exact ⟨D, 1, by simp [Collision.value, Collision.diff, key, ← hD]; rfl⟩
  · split at he
    · rename_i P hP
      cases Option.some.inj he
      obtain ⟨D, hD⟩ := hs.1 .gₜ _ P hP
      refine ⟨by simp, by simp, ?_⟩
      intro _
      refine ⟨(-1 : k) • D, 1, ?_⟩
      simp only [Collision.value, Collision.diff, map_sub, map_mul, scalar,
        MvPolynomial.constantCoeff_C, key, map_smul, ← hD, one_smul]
      rfl
    · simp at he

lemma bad_typed [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0)
    (ω : World pp) (hω : ω ∈ support (observedRun pp m A))
    (e : Collision pp) (he : BadAt ω e) :
    (e.sort = .g₁ → ∃ E : Expr1 P0, e.value = Exposure.value1 pp E) ∧
    (e.sort = .g₂ → ∃ E : Expr2 P0,
      e.value = Exposure.value2 pp (formVec ω.1.out.forms) E) ∧
    (e.sort = .gₜ → ∃ (D : ExprT P0) (ι : k),
      e.value = Exposure.valueT pp (formVec ω.1.out.forms) D -
        ι • Exposure.valueKey pp) := by
  have h := observed_typed pp m A
  generalize observedRun pp m A = obs at h hω ⊢
  have hs := h ω hω
  obtain ⟨b, hb, _, hcmp⟩ := he
  unfold badCmp at hcmp
  simp only [hb] at hcmp
  cases hstep : ω.2.steps[b]? with
  | none => simp [hstep] at hcmp
  | some st =>
    simp only [hstep] at hcmp
    have ht := hs.2 st (List.mem_of_getElem? hstep)
    rcases hq : st.entry.1 with ((n | gq) | i) | kq
    · simp [hq] at hcmp
    · simp only [hq] at hcmp
      obtain ⟨hn, ho⟩ := ht.2 e hcmp
      apply conclusion_of_mem pp ω.1.out.forms e
      exact (space pp ω.1.out.forms e.sort).sub_mem hn ho
    · simp [hq] at hcmp
    · simp only [hq] at hcmp
      exact keyCmp_typed pp ω.1.out.forms ω.1 st.shadow ht e hcmp

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.BadTyped
