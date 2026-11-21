import Praxis.Proofs.GroupModel.Split.Lazy.Fold.GuessBuild
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
import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Reduction
import Praxis.Relation
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

def scalarValue (pp : PublicParams P0) : k →ₗ[k] Exposure.Coeff pp where
  toFun a := fun _ => a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def targetValue (pp : PublicParams P0) (forms : FormMatrix P0) :
    (ExprT P0 × k) →ₗ[k] Exposure.Coeff pp where
  toFun x := Exposure.valueT pp (formVec forms) x.1 - x.2 • Exposure.valueKey pp
  map_add' x y := by
    change Exposure.valueT pp (formVec forms) (x.1 + y.1) -
      (x.2 + y.2) • Exposure.valueKey pp = _
    rw [map_add, add_smul]
    abel
  map_smul' a x := by
    change Exposure.valueT pp (formVec forms) (a • x.1) -
      (a * x.2) • Exposure.valueKey pp = _
    rw [map_smul, smul_sub, smul_smul]
    rfl

def monDegree (m : GuessVar →₀ ℕ) : ℕ := m.sum fun _ n => n

def sortDegree (s : GroupModel.Sorted.PSort) (m : GuessVar →₀ ℕ) : ℕ :=
  m.sum fun v n => if v.1 = s then n else 0

@[simp] lemma monDegree_zero : monDegree 0 = 0 := rfl

@[simp] lemma monDegree_single (v : GuessVar) : monDegree (Finsupp.single v 1) = 1 := by
  simp [monDegree]

@[simp] lemma monDegree_add (a b : GuessVar →₀ ℕ) :
    monDegree (a + b) = monDegree a + monDegree b := by
  simp [monDegree, Finsupp.sum_add_index']

@[simp] lemma sortDegree_single (s : GroupModel.Sorted.PSort) (v : GuessVar) :
    sortDegree s (Finsupp.single v 1) = if v.1 = s then 1 else 0 := by
  simp [sortDegree]

lemma monDegree_pos (m : GuessVar →₀ ℕ) (hm : m ≠ 0) : 0 < monDegree m := by
  apply Finsupp.sum_pos _ hm
  intro v hv
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)

def coefficientSpace (pp : PublicParams P0) (forms : FormMatrix P0)
    (s : GroupModel.Sorted.PSort) (m : GuessVar →₀ ℕ) : Submodule k (Exposure.Coeff pp) :=
  match s with
  | .g₁ => if m = 0 then (Exposure.value1 pp).range else (scalarValue pp).range
  | .g₂ => if m = 0 then (Exposure.value2 pp (formVec forms)).range else (scalarValue pp).range
  | .gₜ => if m = 0 then (targetValue pp forms).range
      else if monDegree m = 1 ∧ sortDegree .g₁ m = 1 then
        (Exposure.value2 pp (formVec forms)).range
      else if monDegree m = 1 ∧ sortDegree .g₂ m = 1 then
        (Exposure.value1 pp).range else (scalarValue pp).range

def sortBound (s : GroupModel.Sorted.PSort) : ℕ := if s = .gₜ then 2 else 1

structure Typed (pp : PublicParams P0) (forms : FormMatrix P0)
    (s : GroupModel.Sorted.PSort) (p : Poly pp) : Prop where
  degree : p.totalDegree ≤ sortBound s
  vars : s ≠ .gₜ → ∀ v ∈ p.vars, v.1 = s
  coeff : ∀ m, p.coeff m ∈ coefficientSpace pp forms s m

variable {pp : PublicParams P0} {forms : FormMatrix P0} {s : GroupModel.Sorted.PSort}

lemma Typed.zero : Typed pp forms s 0 := by
  refine ⟨by simp, ?_, ?_⟩
  · intro hs v hv
    simpa using hv
  · intro m
    simpa using (coefficientSpace pp forms s m).zero_mem

lemma Typed.add {p q : Poly pp} (hp : Typed pp forms s p) (hq : Typed pp forms s q) :
    Typed pp forms s (p + q) := by
  refine ⟨(MvPolynomial.totalDegree_add _ _).trans (max_le hp.degree hq.degree), ?_, ?_⟩
  · intro hs v hv
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset p q hv) with hv | hv
    · exact hp.vars hs v hv
    · exact hq.vars hs v hv
  · intro m
    rw [MvPolynomial.coeff_add]
    exact Submodule.add_mem _ (hp.coeff m) (hq.coeff m)

lemma Typed.sub {p q : Poly pp} (hp : Typed pp forms s p) (hq : Typed pp forms s q) :
    Typed pp forms s (p - q) := by
  refine ⟨(MvPolynomial.totalDegree_sub _ _).trans (max_le hp.degree hq.degree), ?_, ?_⟩
  · intro hs v hv
    rw [sub_eq_add_neg] at hv
    have hv' := MvPolynomial.vars_add_subset p (-q) hv
    rw [MvPolynomial.vars_neg] at hv'
    rcases Finset.mem_union.mp hv' with hv | hv
    · exact hp.vars hs v hv
    · exact hq.vars hs v hv
  · intro m
    rw [MvPolynomial.coeff_sub]
    exact Submodule.sub_mem _ (hp.coeff m) (hq.coeff m)

lemma Typed.neg {p : Poly pp} (hp : Typed pp forms s p) : Typed pp forms s (-p) := by
  simpa only [zero_sub] using Typed.zero.sub hp

lemma Typed.scale {p : Poly pp} (a : k) (hp : Typed pp forms s p) :
    Typed pp forms s (scalar pp a * p) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := MvPolynomial.totalDegree_mul (scalar pp a) p
    simp only [scalar, MvPolynomial.totalDegree_C, zero_add] at h
    exact h.trans hp.degree
  · intro hs v hv
    have hv' : v ∈ p.vars := by
      have h := MvPolynomial.vars_mul (scalar pp a) p hv
      simpa [scalar] using h
    exact hp.vars hs v hv'
  · intro m
    simp only [scalar, MvPolynomial.coeff_C_mul]
    exact (coefficientSpace pp forms s m).smul_mem a (hp.coeff m)

lemma Typed.linear {p q : Poly pp} (a b : k)
    (hp : Typed pp forms s p) (hq : Typed pp forms s q) :
    Typed pp forms s (scalar pp a * p + scalar pp b * q) :=
  (hp.scale a).add (hq.scale b)

lemma Typed.constant (f : Exposure.Coeff pp)
    (hf : f ∈ coefficientSpace pp forms s 0) : Typed pp forms s (MvPolynomial.C f) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro hs v hv
    simpa using hv
  · intro m
    by_cases hm : m = 0
    · subst m
      simpa only [MvPolynomial.coeff_C, ite_true] using hf
    · simpa only [MvPolynomial.coeff_C, if_neg (Ne.symm hm)] using
        (coefficientSpace pp forms s m).zero_mem

lemma Typed.base1 (E : Expr1 P0) : Typed pp forms .g₁ (base1 pp E) := by
  apply Typed.constant
  exact ⟨E, rfl⟩

lemma Typed.base2 (E : Expr2 P0) : Typed pp forms .g₂ (base2 pp forms E) := by
  apply Typed.constant
  exact ⟨E, rfl⟩

lemma Typed.baseT (E : ExprT P0) : Typed pp forms .gₜ (baseT pp forms E) := by
  apply Typed.constant
  exact ⟨(E, 0), by simp [targetValue]; rfl⟩

lemma Typed.key : Typed pp forms .gₜ (key pp) := by
  change Typed pp forms .gₜ (MvPolynomial.C (Exposure.valueKey pp))
  apply Typed.constant
  refine ⟨(0, -1), ?_⟩
  simp [targetValue]

lemma Typed.guess (v : GuessVar) : Typed pp forms v.1 (MvPolynomial.X v) := by
  refine ⟨?_, ?_, ?_⟩
  · change (MvPolynomial.monomial (Finsupp.single v 1) (1 : Coeff pp)).totalDegree ≤ _
    apply (MvPolynomial.totalDegree_monomial_le _ _).trans
    simp [sortBound]
    split_ifs <;> decide
  · intro hs w hw
    obtain ⟨m, hm, hwm⟩ := (MvPolynomial.mem_vars_iff_mem_support w).mp hw
    have hm' : m = Finsupp.single v 1 :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    rw [hm'] at hwm
    have hw' : w = v := Finset.mem_singleton.mp (Finsupp.support_single_subset hwm)
    exact congrArg Prod.fst hw'
  · intro m
    by_cases hm : Finsupp.single v 1 = m
    · subst m
      rw [MvPolynomial.coeff_X, if_pos rfl]
      have hv : (Finsupp.single v 1 : GuessVar →₀ ℕ) ≠ 0 := by simp
      cases hs : v.1 <;> simp only [coefficientSpace, if_neg hv]
      · exact ⟨1, rfl⟩
      · exact ⟨1, rfl⟩
      · simp only [monDegree_single, sortDegree_single, hs, reduceCtorEq, if_false,
          Nat.zero_ne_one, and_false]
        exact ⟨1, rfl⟩
    · rw [MvPolynomial.coeff_X, if_neg hm]
      exact (coefficientSpace pp forms v.1 m).zero_mem

lemma source_coefficient_scalar {p : Poly pp} (hp : Typed pp forms s p) (hs : s ≠ .gₜ)
    (m : GuessVar →₀ ℕ) (hm : m ≠ 0) :
    ∃ a : k, (fun _ => a) = p.coeff m := by
  have h := hp.coeff m
  cases s <;> simp only [coefficientSpace, if_neg hm] at h
  · exact h
  · exact h
  · exact (hs rfl).elim

lemma source_sortDegree {p : Poly pp} (hp : Typed pp forms s p) (hs : s ≠ .gₜ)
    (m : GuessVar →₀ ℕ) (hm : m ∈ p.support) (t : GroupModel.Sorted.PSort) :
    sortDegree t m = if s = t then monDegree m else 0 := by
  unfold sortDegree monDegree
  split_ifs with hst
  · subst t
    apply Finsupp.sum_congr
    intro v hv
    have hvs : v.1 = s := hp.vars hs v ((MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨m, hm, hv⟩)
    simp only [hvs, ite_true]
  · unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro v hv
    have hvs : v.1 = s := hp.vars hs v ((MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨m, hm, hv⟩)
    simp only [hvs, if_neg hst]

lemma source_monDegree {p : Poly pp} (hp : Typed pp forms s p) (hs : s ≠ .gₜ)
    (m : GuessVar →₀ ℕ) (hm : m ∈ p.support) (hm0 : m ≠ 0) : monDegree m = 1 := by
  have h₁ := MvPolynomial.le_totalDegree hm
  have h₂ := hp.degree
  have h₃ := monDegree_pos m hm0
  simp only [sortBound, if_neg hs] at h₂
  change monDegree m ≤ p.totalDegree at h₁
  omega

lemma pair_coefficient {p q : Poly pp} (hp : Typed pp forms .g₁ p)
    (hq : Typed pp forms .g₂ q) (a b : GuessVar →₀ ℕ) :
    p.coeff a * q.coeff b ∈ coefficientSpace pp forms .gₜ (a + b) := by
  by_cases hpa : p.coeff a = 0
  · rw [hpa, zero_mul]
    exact Submodule.zero_mem _
  by_cases hqb : q.coeff b = 0
  · rw [hqb, mul_zero]
    exact Submodule.zero_mem _
  have ha := MvPolynomial.mem_support_iff.mpr hpa
  have hb := MvPolynomial.mem_support_iff.mpr hqb
  by_cases ha0 : a = 0
  · subst a
    obtain ⟨E, hE⟩ := hp.coeff 0
    by_cases hb0 : b = 0
    · subst b
      obtain ⟨F, hF⟩ := hq.coeff 0
      change _ ∈ (targetValue pp forms).range
      refine ⟨(pairExpr E F, 0), ?_⟩
      simp only [targetValue, LinearMap.coe_mk, AddHom.coe_mk, zero_smul, sub_zero,
        Exposure.value_pair, hE, hF]
    · obtain ⟨u, hu⟩ := source_coefficient_scalar hq (by decide) b hb0
      have hd := source_monDegree hq (by decide) b hb hb0
      have h1 := source_sortDegree hq (by decide) b hb .g₁
      have h2 := source_sortDegree hq (by decide) b hb .g₂
      simp only [reduceCtorEq, if_false, if_pos rfl, hd] at h1 h2
      simp only [zero_add, coefficientSpace, if_neg hb0, hd, h1, h2, true_and,
        Nat.zero_ne_one, if_false, if_pos rfl]
      refine ⟨u • E, ?_⟩
      rw [map_smul, hE, ← hu]
      funext ω
      simp [smul_eq_mul, mul_comm]
  · obtain ⟨u, hu⟩ := source_coefficient_scalar hp (by decide) a ha0
    have hd := source_monDegree hp (by decide) a ha ha0
    by_cases hb0 : b = 0
    · subst b
      obtain ⟨F, hF⟩ := hq.coeff 0
      have h1 := source_sortDegree hp (by decide) a ha .g₁
      simp only [if_pos rfl, hd] at h1
      simp only [add_zero, coefficientSpace, if_neg ha0, hd, h1, and_self, if_pos rfl]
      refine ⟨u • F, ?_⟩
      rw [map_smul, hF, ← hu]
      rfl
    · obtain ⟨v, hv⟩ := source_coefficient_scalar hq (by decide) b hb0
      have hd' := source_monDegree hq (by decide) b hb hb0
      have hab : a + b ≠ 0 := by
        intro hab
        have h := congrArg monDegree hab
        simp only [monDegree_add, hd, hd', monDegree_zero] at h
        contradiction
      simp only [coefficientSpace, if_neg hab, monDegree_add, hd, hd',
        Nat.reduceAdd, OfNat.ofNat_ne_one, false_and, if_false]
      refine ⟨u * v, ?_⟩
      rw [← hu, ← hv]
      rfl

lemma Typed.pair {p q : Poly pp} (hp : Typed pp forms .g₁ p)
    (hq : Typed pp forms .g₂ q) : Typed pp forms .gₜ (p * q) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := MvPolynomial.totalDegree_mul p q
    have h1 := hp.degree
    have h2 := hq.degree
    simp only [sortBound, reduceCtorEq, ite_false, ite_true] at h1 h2 ⊢
    omega
  · intro hs
    exact (hs rfl).elim
  · intro m
    rw [MvPolynomial.coeff_mul]
    apply Submodule.sum_mem
    intro ab hab
    have he := Finset.mem_antidiagonal.mp hab
    rw [← he]
    exact pair_coefficient hp hq ab.1 ab.2

lemma Typed.coinCoefficient {p : Poly pp} (hp : Typed pp forms s p) (m : GuessVar →₀ ℕ) :
    CoinCoefficient pp forms (p.coeff m) := by
  have h := hp.coeff m
  cases s with
  | g₁ =>
    by_cases hm : m = 0
    · simp only [coefficientSpace, if_pos hm] at h
      obtain ⟨E, hE⟩ := h
      exact Or.inl (Or.inr (Or.inl ⟨E, hE.symm⟩))
    · simp only [coefficientSpace, if_neg hm] at h
      obtain ⟨a, ha⟩ := h
      exact Or.inl (Or.inl ⟨a, ha.symm⟩)
  | g₂ =>
    by_cases hm : m = 0
    · simp only [coefficientSpace, if_pos hm] at h
      obtain ⟨E, hE⟩ := h
      exact Or.inl (Or.inr (Or.inr ⟨E, hE.symm⟩))
    · simp only [coefficientSpace, if_neg hm] at h
      obtain ⟨a, ha⟩ := h
      exact Or.inl (Or.inl ⟨a, ha.symm⟩)
  | gₜ =>
    by_cases hm : m = 0
    · simp only [coefficientSpace, if_pos hm] at h
      obtain ⟨⟨D, ι⟩, hD⟩ := h
      exact Or.inr ⟨D, ι, hD.symm⟩
    · simp only [coefficientSpace, if_neg hm] at h
      split_ifs at h with h1 h2
      · obtain ⟨E, hE⟩ := h
        exact Or.inl (Or.inr (Or.inr ⟨E, hE.symm⟩))
      · obtain ⟨E, hE⟩ := h
        exact Or.inl (Or.inr (Or.inl ⟨E, hE.symm⟩))
      · obtain ⟨a, ha⟩ := h
        exact Or.inl (Or.inl ⟨a, ha.symm⟩)

lemma Typed.sourceCoefficient {p : Poly pp} (hp : Typed pp forms s p)
    (m : GuessVar →₀ ℕ) (hm : m ≠ 0) : SourceCoefficient pp forms (p.coeff m) := by
  have h := hp.coeff m
  cases s with
  | g₁ | g₂ =>
    simp only [coefficientSpace, if_neg hm] at h
    obtain ⟨a, ha⟩ := h
    exact Or.inl ⟨a, ha.symm⟩
  | gₜ =>
    simp only [coefficientSpace, if_neg hm] at h
    split_ifs at h with h1 h2
    · obtain ⟨E, hE⟩ := h
      exact Or.inr (Or.inr ⟨E, hE.symm⟩)
    · obtain ⟨E, hE⟩ := h
      exact Or.inr (Or.inl ⟨E, hE.symm⟩)
    · obtain ⟨a, ha⟩ := h
      exact Or.inl ⟨a, ha.symm⟩

structure TypedState (pp : PublicParams P0) (forms : FormMatrix P0) (st : State pp) : Prop where
  dict : ∀ s l p, st.dict s l = some p → Typed pp forms s p
  first : ∀ e, st.first = some e → Typed pp forms e.sort e.new ∧ Typed pp forms e.sort e.old

lemma typed_record (st : State pp) (ht : TypedState pp forms st)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (p : Poly pp) (hp : Typed pp forms s p) :
    ∀ s' l' q, record pp st.dict s l p s' l' = some q → Typed pp forms s' q := by
  intro s' l' q hq
  by_cases hs : s' = s
  · subst s'
    by_cases hl : l' = l
    · subst l'
      have hqp : p = q := by simpa only [record_same, Option.some.injEq] using hq
      exact hqp ▸ hp
    · apply ht.dict s l' q
      simpa [record, hl] using hq
  · apply ht.dict s' l' q
    simpa [record, hs] using hq

lemma TypedState.insert (st : State pp) (ht : TypedState pp forms st)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (p : Poly pp) (hp : Typed pp forms s p) :
    TypedState pp forms (insertResult pp st s l p) := by
  unfold insertResult
  cases hd : st.dict s l with
  | none => exact ⟨typed_record st ht s l p hp, ht.first⟩
  | some q =>
    dsimp only
    split_ifs
    · exact ht
    · refine ⟨ht.dict, ?_⟩
      intro e he
      cases hf : st.first with
      | some f =>
        have hfe : f = e := by simpa [hf] using he
        exact hfe ▸ ht.first f hf
      | none =>
        have hfe : (⟨s, l, p, q⟩ : Collision pp) = e := by simpa [hf] using he
        subst e
        exact ⟨hp, ht.dict s l q hd⟩

lemma TypedState.resolve_typed (st : State pp) (ht : TypedState pp forms st)
    (σ : LabelEncoding P0) (s : GroupModel.Sorted.PSort) (l : Label P0) :
    TypedState pp forms (resolve pp σ st s l).2 ∧
      ∀ p, (resolve pp σ st s l).1 = some p → Typed pp forms s p := by
  unfold resolve
  cases hd : st.dict s l with
  | some p =>
    refine ⟨ht, ?_⟩
    intro q hq
    cases hq
    exact ht.dict s l p hd
  | none =>
    cases hc : Algebra.decodeLabel (σ s) l with
    | none =>
      refine ⟨⟨ht.dict, ht.first⟩, ?_⟩
      intro p hp
      cases hp
    | some a =>
      refine ⟨⟨typed_record st ht s l _ (Typed.guess (s, l)), ht.first⟩, ?_⟩
      intro p hp
      cases hp
      exact Typed.guess (s, l)

lemma TypedState.observe (st : State pp) (ht : TypedState pp forms st)
    (σ : LabelEncoding P0) (gq : GQuery P0) (R : gq.Result) :
    TypedState pp forms (observeGroup pp σ st gq R) := by
  cases gq with
  | lin s a b u v =>
    obtain ⟨hx, hP⟩ := ht.resolve_typed st σ s u
    obtain ⟨hy, hQ⟩ := hx.resolve_typed _ σ s v
    simp only [observeGroup]
    cases h1 : (resolve pp σ st s u).1 with
    | none => exact hy
    | some p =>
      cases h2 : (resolve pp σ (resolve pp σ st s u).2 s v).1 with
      | none => exact hy
      | some q =>
        cases R with
        | none => exact hy
        | some l => exact hy.insert _ s l _ ((hP p h1).linear a b (hQ q h2))
  | pair u v =>
    obtain ⟨hx, hP⟩ := ht.resolve_typed st σ .g₁ u
    obtain ⟨hy, hQ⟩ := hx.resolve_typed _ σ .g₂ v
    simp only [observeGroup]
    cases h1 : (resolve pp σ st .g₁ u).1 with
    | none => exact hy
    | some p =>
      cases h2 : (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).1 with
      | none => exact hy
      | some q =>
        cases R with
        | none => exact hy
        | some l => exact hy.insert _ .gₜ l _ ((hP p h1).pair (hQ q h2))
  | name u =>
    cases R with
    | none => exact ht
    | some nm =>
      apply ht.insert _ .gₜ _ _
      apply Typed.neg
      cases hd : st.dict .gₜ u with
      | none => exact Typed.zero
      | some p => exact ht.dict .gₜ u p hd

lemma TypedState.empty : TypedState pp forms (empty pp) := by
  constructor
  · intro s l p hp
    cases hp
  · intro e he
    cases he

lemma initialEntries_typed (pv : PubView P0) (e : GroupModel.Sorted.PSort × Label P0 × Poly pp)
    (he : e ∈ initialEntries pp forms pv) : Typed pp forms e.1 e.2.2 := by
  simp only [initialEntries, List.mem_append, List.mem_map] at he
  rcases he with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
  · exact Typed.base1 _
  · exact Typed.base2 _
  · exact Typed.baseT _

lemma TypedState.initialise_typed (pv : PubView P0) : TypedState pp forms (initialise pp forms pv) := by
  unfold initialise
  have h : ∀ (l : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)),
      (∀ e ∈ l, Typed pp forms e.1 e.2.2) → ∀ st : State pp, TypedState pp forms st →
      TypedState pp forms (l.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st) := by
    intro l hl
    induction l with
    | nil => exact fun st ht => ht
    | cons e es ih =>
      intro st ht
      apply ih (fun f hf => hl f (List.mem_cons_of_mem e hf))
      exact ht.insert st e.1 e.2.1 e.2.2 (hl e (by simp))
  exact h _ (initialEntries_typed pv) _ TypedState.empty

def TypedObserved (pp : PublicParams P0) (forms : FormMatrix P0) (st : ObsState pp) : Prop :=
  TypedState pp forms st.shadow ∧ ∀ step ∈ st.steps, TypedState pp forms step.shadow

lemma typed_obsHandler (σ : LabelEncoding P0) (c : Coins P0)
    (st : ObsState pp) (ht : TypedObserved pp forms st) (q : (AdvModel P0).Domain) :
    ∀ z ∈ support ((obsHandler pp σ c q).run st), TypedObserved pp forms z.2 := by
  have hsh : TypedState pp forms (match q with
      | .inl (.inl (.inr gq)) => observeGroup pp σ st.shadow gq (groupAnswer σ st.oracle.issuedT gq)
      | _ => st.shadow) := by
    rcases q with ((n | gq) | hf) | kq
    · exact ht.1
    · exact ht.1.observe st.shadow σ gq _
    · exact ht.1
    · exact ht.1
  intro z hz
  simp only [obsHandler, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  refine ⟨hsh, ?_⟩
  intro step hstep
  rcases List.mem_append.mp hstep with hstep | hstep
  · exact ht.2 step hstep
  · have hstep' := List.mem_singleton.mp hstep
    subst step
    exact hsh

lemma typed_observedRun (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0)
    (A : Adversary P0) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A)) :
    TypedObserved (ppOf ch S) ω.1.out.forms ω.2 := by
  unfold observedRun at hω
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hω
  obtain ⟨σ, hσ, e, he, z, hz, rfl⟩ := hω
  apply simulateQ_run_preserves_inv_of_query (obsHandler (ppOf ch S) σ e.1.coins)
    (TypedObserved (ppOf ch S) e.1.forms)
    (fun q st ht => typed_obsHandler σ e.1.coins st ht q)
    (A.run e.1.pv e.1.header)
    (⟨e.2, initialise (ppOf ch S) e.1.forms e.1.pv, [], [], none⟩ : ObsState (ppOf ch S))
    ⟨TypedState.initialise_typed e.1.pv, by simp⟩ z hz

lemma keyCmp_typed (z : WorldOut P0) (st : State pp) (ht : TypedState pp z.out.forms st)
    (e : Collision pp) (he : keyCmp pp z st = some e) :
    Typed pp z.out.forms e.sort e.new ∧ Typed pp z.out.forms e.sort e.old := by
  unfold keyCmp at he
  cases hpos : st.dict .gₜ (z.enc .gₜ (kappa pp z.out.coins)) with
  | some p =>
    have hep : (⟨.gₜ, z.enc .gₜ (kappa pp z.out.coins), p, key pp⟩ : Collision pp) = e := by
      simpa [hpos] using he
    subst e
    exact ⟨ht.dict _ _ _ hpos, Typed.key⟩
  | none =>
    cases hneg : st.dict .gₜ (z.enc .gₜ (-kappa pp z.out.coins)) with
    | none => simp [hpos, hneg] at he
    | some p =>
      have hep : (⟨.gₜ, z.enc .gₜ (-kappa pp z.out.coins), scalar pp (-1) * p,
          key pp⟩ : Collision pp) = e := by simpa [hpos, hneg] using he
      subst e
      exact ⟨(ht.dict _ _ _ hneg).scale (-1), Typed.key⟩

lemma badAt_typed (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0)
    (A : Adversary P0) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A)) (e : Collision (ppOf ch S))
    (he : BadAt ω e) : Typed (ppOf ch S) ω.1.out.forms e.sort e.diff := by
  have ht := typed_observedRun ch S m A
  generalize observedRun (ppOf ch S) m A = obs at ht hω
  have htyped := ht ω hω
  obtain ⟨b, hb, hclean, he⟩ := he
  unfold badCmp at he
  rw [hb] at he
  cases hstep : ω.2.steps[b]? with
  | none => simp [hstep] at he
  | some step =>
    have htstep := htyped.2 step (List.mem_of_getElem? hstep)
    simp only [hstep] at he
    rcases hq : step.entry.1 with ((n | gq) | hf) | kq
    · simp [hq] at he
    · simp only [hq] at he
      obtain ⟨hp, hq⟩ := htstep.first e he
      exact hp.sub hq
    · simp [hq] at he
    · simp only [hq] at he
      obtain ⟨hp, hq⟩ := keyCmp_typed ω.1 step.shadow htstep e he
      exact hp.sub hq

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild
