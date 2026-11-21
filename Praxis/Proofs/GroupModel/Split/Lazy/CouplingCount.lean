import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0)

def swapEnc (s : GroupModel.Sorted.PSort) (l₁ l₂ : Label P0) (σ : LabelEncoding P0) :
    LabelEncoding P0 :=
  Function.update σ s ((σ s).trans (Equiv.swap l₁ l₂).toEmbedding)

lemma swapEnc_same (s : GroupModel.Sorted.PSort) (l₁ l₂ : Label P0) (σ : LabelEncoding P0)
    (v : k) : swapEnc s l₁ l₂ σ s v = Equiv.swap l₁ l₂ (σ s v) := by
  simp [swapEnc]

lemma swapEnc_other (s s' : GroupModel.Sorted.PSort) (h : s' ≠ s) (l₁ l₂ : Label P0)
    (σ : LabelEncoding P0) : swapEnc s l₁ l₂ σ s' = σ s' := by
  simp [swapEnc, Function.update_of_ne h]

lemma swapEnc_swapEnc (s : GroupModel.Sorted.PSort) (l₁ l₂ : Label P0) (σ : LabelEncoding P0) :
    swapEnc s l₁ l₂ (swapEnc s l₁ l₂ σ) = σ := by
  funext s'
  by_cases h : s' = s
  · subst h
    apply Function.Embedding.ext
    intro v
    rw [swapEnc_same, swapEnc_same, Equiv.swap_apply_self]
  · rw [swapEnc_other s s' h, swapEnc_other s s' h]

lemma mem_cons_iff (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (σ : LabelEncoding P0) :
    σ ∈ cons pp sh ord c x ↔
      (∀ s l P, sh.dict s l = some P → σ s (valueAt pp ord c x P) = l) ∧
        ∀ s l, l ∈ sh.excluded s → ∀ v, σ s v ≠ l := by
  unfold cons
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma not_mem_assigned (sh : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h : l ∈ available pp sh s) : sh.dict s l = none := by
  simp only [available, assigned, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_filter, not_or] at h
  simpa using h.1

lemma not_mem_excluded (sh : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h : l ∈ available pp sh s) : l ∉ sh.excluded s := by
  simp only [available, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    not_or] at h
  exact h.2

lemma mem_available (sh : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h1 : sh.dict s l = none) (h2 : l ∉ sh.excluded s) : l ∈ available pp sh s := by
  simp only [available, assigned, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_filter, not_or, h1, Option.isSome_none,
    Bool.false_eq_true, not_false_eq_true, h2, and_self]

lemma swapEnc_mem_cons (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l₁ l₂ : Label P0)
    (h₁ : l₁ ∈ available pp sh s) (h₂ : l₂ ∈ available pp sh s)
    (σ : LabelEncoding P0) (hσ : σ ∈ cons pp sh ord c x) :
    swapEnc s l₁ l₂ σ ∈ cons pp sh ord c x := by
  rw [mem_cons_iff] at hσ ⊢
  obtain ⟨hd, he⟩ := hσ
  refine ⟨?_, ?_⟩
  · intro s' l P hP
    by_cases hs : s' = s
    · subst hs
      rw [swapEnc_same, hd s' l P hP]
      have hl1 : l ≠ l₁ := by
        intro h; subst h; rw [not_mem_assigned pp sh s' l h₁] at hP; cases hP
      have hl2 : l ≠ l₂ := by
        intro h; subst h; rw [not_mem_assigned pp sh s' l h₂] at hP; cases hP
      exact Equiv.swap_apply_of_ne_of_ne hl1 hl2
    · rw [swapEnc_other s s' hs]
      exact hd s' l P hP
  · intro s' l hl v hv
    by_cases hs : s' = s
    · subst hs
      rw [swapEnc_same] at hv
      have hl1 : l ≠ l₁ := by
        intro h; subst h; exact not_mem_excluded pp sh s' l h₁ hl
      have hl2 : l ≠ l₂ := by
        intro h; subst h; exact not_mem_excluded pp sh s' l h₂ hl
      apply he s' l hl v
      have := congrArg (Equiv.swap l₁ l₂) hv
      rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne hl1 hl2] at this
      exact this
    · rw [swapEnc_other s s' hs] at hv
      exact he s' l hl v hv

lemma card_fiber_eq (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (v : k) (l₁ l₂ : Label P0)
    (h₁ : l₁ ∈ available pp sh s) (h₂ : l₂ ∈ available pp sh s) :
    ((cons pp sh ord c x).filter fun σ => σ s v = l₁).card =
      ((cons pp sh ord c x).filter fun σ => σ s v = l₂).card := by
  apply Finset.card_bij' (fun σ _ => swapEnc s l₁ l₂ σ) (fun σ _ => swapEnc s l₁ l₂ σ)
  · intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨swapEnc_mem_cons pp sh ord c x s l₁ l₂ h₁ h₂ σ hσ.1, ?_⟩
    rw [swapEnc_same, hσ.2, Equiv.swap_apply_left]
  · intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨swapEnc_mem_cons pp sh ord c x s l₁ l₂ h₁ h₂ σ hσ.1, ?_⟩
    rw [swapEnc_same, hσ.2, Equiv.swap_apply_right]
  · intro σ _
    exact swapEnc_swapEnc s l₁ l₂ σ
  · intro σ _
    exact swapEnc_swapEnc s l₁ l₂ σ

def valuesOf (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) : Finset k :=
  Finset.univ.filter fun v => ∃ l P, sh.dict s l = some P ∧ valueAt pp ord c x P = v

lemma label_available (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (v : k) (hv : v ∉ valuesOf pp sh ord c x s)
    (σ : LabelEncoding P0) (hσ : σ ∈ cons pp sh ord c x) :
    σ s v ∈ available pp sh s := by
  rw [mem_cons_iff] at hσ
  apply mem_available
  · cases h : sh.dict s (σ s v) with
    | none => rfl
    | some P =>
      exfalso
      apply hv
      simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨σ s v, P, h, ?_⟩
      exact (σ s).injective (hσ.1 s (σ s v) P h)
  · intro hl
    exact hσ.2 s (σ s v) hl v rfl

lemma card_cons_eq (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (v : k) (hv : v ∉ valuesOf pp sh ord c x s)
    (l : Label P0) (hl : l ∈ available pp sh s) :
    (cons pp sh ord c x).card =
      (available pp sh s).card * ((cons pp sh ord c x).filter fun σ => σ s v = l).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ => σ s v) (t := available pp sh s)
    (fun σ hσ => label_available pp sh ord c x s v hv σ hσ)]
  rw [Finset.sum_congr rfl (fun l' hl' => card_fiber_eq pp sh ord c x s v l' l hl' hl)]
  rw [Finset.sum_const, smul_eq_mul]

section Consistent

variable (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
  (s : GroupModel.Sorted.PSort) (σ : LabelEncoding P0) (hσ : σ ∈ cons pp sh ord c x)

include hσ

lemma assigned_excluded_disjoint : Disjoint (assigned pp sh s) (sh.excluded s) := by
  rw [mem_cons_iff] at hσ
  rw [Finset.disjoint_left]
  intro l hl he
  simp only [assigned, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hl
  exact hσ.2 s l he _ (hσ.1 s l P hP)

lemma card_available :
    (available pp sh s).card = 2 ^ P0.labelBits - (assigned pp sh s).card - (sh.excluded s).card := by
  unfold available
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_union_of_disjoint (assigned_excluded_disjoint pp sh ord c x s σ hσ),
    Fintype.card_bitVec]
  omega

lemma card_values : (valuesOf pp sh ord c x s).card = (assigned pp sh s).card := by
  rw [mem_cons_iff] at hσ
  apply Finset.card_bij (fun v _ => σ s v)
  · intro v hv
    simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨l, P, hP, rfl⟩ := hv
    simp only [assigned, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hσ.1 s l P hP, hP]
    rfl
  · intro v₁ _ v₂ _ h
    exact (σ s).injective h
  · intro l hl
    simp only [assigned, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hl
    refine ⟨valueAt pp ord c x P, ?_, hσ.1 s l P hP⟩
    simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, P, hP, rfl⟩

lemma unassigned_le_available :
    Fintype.card k - (valuesOf pp sh ord c x s).card ≤ (available pp sh s).card := by
  have hsub : (Finset.univ \ valuesOf pp sh ord c x s).image (σ s) ⊆ available pp sh s := by
    intro l hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
    exact label_available pp sh ord c x s v (Finset.mem_sdiff.mp hv).2 σ hσ
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (σ s).injective,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at h1
  exact h1

end Consistent

lemma card_exclude (sh : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (hl : l ∈ available pp sh s)
    (σ₀ : LabelEncoding P0) (hσ₀ : σ₀ ∈ cons pp sh ord c x) :
    ((cons pp sh ord c x).filter fun σ => ∀ v, σ s v ≠ l).card * (available pp sh s).card =
      (cons pp sh ord c x).card *
        ((available pp sh s).card - (Fintype.card k - (valuesOf pp sh ord c x s).card)) := by
  set C := cons pp sh ord c x
  set U := Finset.univ \ valuesOf pp sh ord c x s
  set F := (C.filter fun σ => σ s (Classical.arbitrary k) = l).card

  have hfib : ∀ v ∈ U, C.card = (available pp sh s).card * (C.filter fun σ => σ s v = l).card :=
    fun v hv => card_cons_eq pp sh ord c x s v (Finset.mem_sdiff.mp hv).2 l hl

  have hin : (C.filter fun σ => ¬ ∀ v, σ s v ≠ l).card =
      ∑ v ∈ U, (C.filter fun σ => σ s v = l).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ => Function.invFun (σ s) l) (t := U)]
    · apply Finset.sum_congr rfl
      intro v hv
      congr 1
      ext σ
      simp only [Finset.mem_filter, not_forall, not_not]
      constructor
      · rintro ⟨⟨hσ, w, hw⟩, hinv⟩
        refine ⟨hσ, ?_⟩
        rw [← hinv]
        exact Function.invFun_eq ⟨w, hw⟩
      · rintro ⟨hσ, hv'⟩
        refine ⟨⟨hσ, v, hv'⟩, ?_⟩
        rw [← hv']
        exact Function.leftInverse_invFun (σ s).injective v
    · intro σ hσ
      rw [Finset.mem_coe, Finset.mem_filter] at hσ
      simp only [not_forall, not_not] at hσ
      obtain ⟨hσC, w, hw⟩ := hσ
      have hw' : Function.invFun (σ s) l = w := by
        rw [← hw]; exact Function.leftInverse_invFun (σ s).injective w
      rw [Finset.mem_coe]
      change Function.invFun (σ s) l ∈ U
      rw [hw']
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hwv
      simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hwv
      obtain ⟨l', P, hP, hPv⟩ := hwv
      rw [mem_cons_iff] at hσC
      have h1 := hσC.1 s l' P hP
      rw [hPv, hw] at h1
      subst h1
      rw [not_mem_assigned pp sh s _ hl] at hP
      cases hP
  have hsplit := Finset.card_filter_add_card_filter_not (s := C)
    (fun σ => ∀ v, σ s v ≠ l)
  have hsum : (∑ v ∈ U, (C.filter fun σ => σ s v = l).card) * (available pp sh s).card =
      U.card * C.card := by
    rw [Finset.sum_mul, ← smul_eq_mul (U.card), ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hfib v hv, mul_comm]
  have hU : U.card = Fintype.card k - (valuesOf pp sh ord c x s).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rw [hU] at hsum
  rw [← hin] at hsum
  rw [Nat.mul_sub]
  have h1 := congrArg (· * (available pp sh s).card) hsplit
  simp only [Nat.add_mul] at h1
  rw [hsum, mul_comm (Fintype.card k - (valuesOf pp sh ord c x s).card) C.card] at h1
  exact Nat.eq_sub_of_add_eq h1

lemma cons_record (st : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp) (G : Finset GuessVar)
    (h : st.dict s l = none) :
    cons pp {st with dict := record pp st.dict s l P, guesses := G} ord c x =
      (cons pp st ord c x).filter fun σ => σ s (valueAt pp ord c x P) = l := by
  ext σ
  rw [Finset.mem_filter, mem_cons_iff, mem_cons_iff]
  constructor
  · rintro ⟨hd, he⟩
    refine ⟨⟨fun s' l' P' hP' => hd s' l' P' ?_, he⟩, hd s l P ?_⟩
    · simp only [record]
      by_cases hs : s' = s
      · subst hs
        rw [Function.update_self]
        by_cases hl : l' = l
        · subst hl; rw [h] at hP'; cases hP'
        · rw [Function.update_of_ne hl]; exact hP'
      · rw [Function.update_of_ne hs]; exact hP'
    · simp [record]
  · rintro ⟨⟨hd, he⟩, hnew⟩
    refine ⟨fun s' l' P' hP' => ?_, he⟩
    simp only [record] at hP'
    by_cases hs : s' = s
    · subst hs
      rw [Function.update_self] at hP'
      by_cases hl : l' = l
      · subst hl
        rw [Function.update_self] at hP'
        cases hP'
        exact hnew
      · rw [Function.update_of_ne hl] at hP'
        exact hd s' l' P' hP'
    · rw [Function.update_of_ne hs] at hP'
      exact hd s' l' P' hP'

lemma cons_exclude (st : State pp) (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l : Label P0) :
    cons pp {st with excluded := Function.update st.excluded s (insert l (st.excluded s))}
        ord c x =
      (cons pp st ord c x).filter fun σ => ∀ v, σ s v ≠ l := by
  ext σ
  rw [Finset.mem_filter, mem_cons_iff, mem_cons_iff]
  dsimp only
  constructor
  · rintro ⟨hd, he⟩
    refine ⟨⟨hd, fun s' l' hl' => he s' l' ?_⟩, he s l (by simp)⟩
    by_cases hs : s' = s
    · subst hs; rw [Function.update_self]; exact Finset.mem_insert_of_mem hl'
    · rw [Function.update_of_ne hs]; exact hl'
  · rintro ⟨⟨hd, he⟩, hnew⟩
    refine ⟨hd, fun s' l' hl' => ?_⟩
    by_cases hs : s' = s
    · subst hs
      rw [Function.update_self, Finset.mem_insert] at hl'
      rcases hl' with rfl | hl'
      · exact hnew
      · exact he s' l' hl'
    · rw [Function.update_of_ne hs] at hl'
      exact he s' l' hl'

lemma refResolve_known (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) (h : st.dict s l = some P) :
    (referenceResolve pp s l).run st = pure (some P, st) := by
  simp [referenceResolve, h, StateT.run_bind, StateT.run_get]

lemma refResolve_excluded (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h1 : st.dict s l = none) (h2 : l ∈ st.excluded s) :
    (referenceResolve pp s l).run st = pure (none, st) := by
  simp [referenceResolve, h1, h2, StateT.run_bind, StateT.run_get]

lemma refResolve_fresh (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h1 : st.dict s l = none) (h2 : l ∉ st.excluded s) :
    (referenceResolve pp s l).run st =
      (fun u : Fin (2 ^ P0.labelBits - (assigned pp st s).card - (st.excluded s).card - 1 + 1) =>
        genericResolve pp st s l (decide (u.val < P0.q - (assigned pp st s).card))) <$>
        $[0..(2 ^ P0.labelBits - (assigned pp st s).card - (st.excluded s).card - 1)] := by
  simp [referenceResolve, h1, h2, StateT.run_bind, StateT.run_get, StateT.run_lift,
    StateT.run_set, map_eq_bind_pure_comp]

lemma decode_none_iff (τ : k ↪ Label P0) (l : Label P0) :
    Algebra.decodeLabel τ l = none ↔ ∀ v, τ v ≠ l := by
  rw [Option.eq_none_iff_forall_ne_some]
  exact forall_congr' fun v => not_congr (decodeLabel_eq_some_iff τ l v)

lemma resolve_props (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) :
    (resolve pp σ st s l).2.first = st.first ∧
    (∀ v ∈ (resolve pp σ st s l).2.guesses, v ∈ st.guesses ∨
      (v = (s, l) ∧ (resolve pp σ st s l).2.dict s l = some (MvPolynomial.X (s, l)))) ∧
    (∀ v ∈ st.guesses, v ∈ (resolve pp σ st s l).2.guesses) ∧
    (∀ s' l' P, st.dict s' l' = some P → (resolve pp σ st s l).2.dict s' l' = some P) ∧
    (∀ s' l' P, (resolve pp σ st s l).2.dict s' l' = some P →
      st.dict s' l' = some P ∨ ((s', l') = (s, l) ∧ P = MvPolynomial.X (s, l) ∧
        (s, l) ∈ (resolve pp σ st s l).2.guesses)) ∧
    (∀ s' l', l' ∈ (resolve pp σ st s l).2.excluded s' →
      l' ∈ st.excluded s' ∨ (s' = s ∧ l' = l ∧ ∀ v, σ s v ≠ l)) ∧
    (∀ P, (resolve pp σ st s l).1 = some P →
      st.dict s l = some P ∨ (P = MvPolynomial.X (s, l) ∧
        (resolve pp σ st s l).2.dict s l = some P ∧ (s, l) ∈ (resolve pp σ st s l).2.guesses)) := by
  unfold resolve
  cases hd : st.dict s l with
  | some P =>
    simp only [hd]
    refine ⟨trivial, fun v hv => Or.inl hv, fun v hv => hv, fun _ _ _ h => h,
      fun _ _ _ h => Or.inl h, fun _ _ h => Or.inl h, ?_⟩
    intro P' hP'
    cases hP'
    exact Or.inl rfl
  | none =>
    simp only [hd]
    cases hdec : Algebra.decodeLabel (σ s) l with
    | none =>
      simp only
      refine ⟨trivial, fun v hv => Or.inl hv, fun v hv => hv, fun _ _ _ h => h,
        fun _ _ _ h => Or.inl h, ?_, fun _ h => by cases h⟩
      intro s' l' hl'
      by_cases hs : s' = s
      · subst hs
        rw [Function.update_self, Finset.mem_insert] at hl'
        rcases hl' with rfl | hl'
        · exact Or.inr ⟨rfl, rfl, (decode_none_iff _ _).mp hdec⟩
        · exact Or.inl hl'
      · rw [Function.update_of_ne hs] at hl'
        exact Or.inl hl'
    | some w =>
      simp only
      refine ⟨trivial, ?_, fun v hv => Finset.mem_insert_of_mem hv, ?_, ?_, fun _ _ h => Or.inl h,
        ?_⟩
      · intro v hv
        rw [Finset.mem_insert] at hv
        rcases hv with rfl | hv
        · exact Or.inr ⟨rfl, by simp [record]⟩
        · exact Or.inl hv
      · intro s' l' P hP
        simp only [record]
        by_cases hs : s' = s
        · subst hs
          rw [Function.update_self]
          by_cases hl : l' = l
          · subst hl; rw [hd] at hP; cases hP
          · rw [Function.update_of_ne hl]; exact hP
        · rw [Function.update_of_ne hs]; exact hP
      · intro s' l' P hP
        simp only [record] at hP
        by_cases hs : s' = s
        · subst hs
          rw [Function.update_self] at hP
          by_cases hl : l' = l
          · subst hl
            rw [Function.update_self] at hP
            cases hP
            exact Or.inr ⟨rfl, rfl, Finset.mem_insert_self _ _⟩
          · rw [Function.update_of_ne hl] at hP
            exact Or.inl hP
        · rw [Function.update_of_ne hs] at hP
          exact Or.inl hP
      · intro P hP
        cases hP
        refine Or.inr ⟨rfl, ?_, Finset.mem_insert_self _ _⟩
        simp [record]

lemma insertResult_props (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) :
    (insertResult pp st s l P).guesses = st.guesses ∧
    (insertResult pp st s l P).excluded = st.excluded ∧
    (∀ s' l' Q, st.dict s' l' = some Q → (insertResult pp st s l P).dict s' l' = some Q) ∧
    (∀ s' l' Q, (insertResult pp st s l P).dict s' l' = some Q →
      st.dict s' l' = some Q ∨ ((s', l') = (s, l) ∧ Q = P)) ∧
    ((insertResult pp st s l P).first = none → st.first = none) := by
  unfold insertResult
  cases hd : st.dict s l with
  | none =>
    simp only
    refine ⟨trivial, trivial, ?_, ?_, fun h => h⟩
    · intro s' l' Q hQ
      simp only [record]
      by_cases hs : s' = s
      · subst hs
        rw [Function.update_self]
        by_cases hl : l' = l
        · subst hl; rw [hd] at hQ; cases hQ
        · rw [Function.update_of_ne hl]; exact hQ
      · rw [Function.update_of_ne hs]; exact hQ
    · intro s' l' Q hQ
      simp only [record] at hQ
      by_cases hs : s' = s
      · subst hs
        rw [Function.update_self] at hQ
        by_cases hl : l' = l
        · subst hl
          rw [Function.update_self] at hQ
          cases hQ
          exact Or.inr ⟨rfl, rfl⟩
        · rw [Function.update_of_ne hl] at hQ
          exact Or.inl hQ
      · rw [Function.update_of_ne hs] at hQ
        exact Or.inl hQ
  | some Q =>
    simp only
    split_ifs with hPQ
    · exact ⟨rfl, rfl, fun _ _ _ h => h, fun _ _ _ h => Or.inl h, fun h => h⟩
    · refine ⟨rfl, rfl, fun _ _ _ h => h, fun _ _ _ h => Or.inl h, ?_⟩
      intro h
      simp only at h
      cases hf : st.first with
      | none => rfl
      | some e => rw [hf] at h; simp at h

lemma mem_vars_X {R : Type} [CommSemiring R] {n v : GuessVar}
    (h : v ∈ (MvPolynomial.X n : MvPolynomial GuessVar R).vars) : v = n := by
  rw [MvPolynomial.mem_vars_iff_mem_support] at h
  obtain ⟨d, hd, hv⟩ := h
  have hd' := MvPolynomial.support_monomial_subset hd
  rw [Finset.mem_singleton] at hd'
  subst hd'
  exact Finset.mem_singleton.mp (Finsupp.support_single_subset hv)

def ShInv (σ : LabelEncoding P0) (st : State pp) : Prop :=
  (∀ s l P, st.dict s l = some P → ∀ v ∈ P.vars, v ∈ st.guesses) ∧
  (∀ v ∈ st.guesses, st.dict v.1 v.2 = some (MvPolynomial.X v)) ∧
  (∀ s l, l ∈ st.excluded s → ∀ w, σ s w ≠ l)

lemma resolve_shInv (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (h : ShInv pp σ st) :
    ShInv pp σ (resolve pp σ st s l).2 ∧
      ∀ P, (resolve pp σ st s l).1 = some P → ∀ v ∈ P.vars, v ∈ (resolve pp σ st s l).2.guesses := by
  obtain ⟨_, hg, hg', hd, hd', he, hP⟩ := resolve_props pp σ st s l
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro s' l' P hP' v hv
    rcases hd' s' l' P hP' with h1 | ⟨_, rfl, hm⟩
    · exact hg' v (h.1 s' l' P h1 v hv)
    · rw [mem_vars_X hv]
      exact hm
  · intro v hv
    rcases hg v hv with h1 | ⟨rfl, h3⟩
    · exact hd _ _ _ (h.2.1 v h1)
    · exact h3
  · intro s' l' hl' w
    rcases he s' l' hl' with h1 | ⟨rfl, rfl, h2⟩
    · exact h.2.2 s' l' h1 w
    · exact h2 w
  · intro P hP' v hv
    rcases hP P hP' with h1 | ⟨rfl, _, hm⟩
    · exact hg' v (h.1 s l P h1 v hv)
    · rw [mem_vars_X hv]
      exact hm

lemma insertResult_shInv (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) (h : ShInv pp σ st) (hP : ∀ v ∈ P.vars, v ∈ st.guesses) :
    ShInv pp σ (insertResult pp st s l P) := by
  obtain ⟨hg, he, hd, hd', _⟩ := insertResult_props pp st s l P
  refine ⟨?_, ?_, ?_⟩
  · intro s' l' Q hQ v hv
    rw [hg]
    rcases hd' s' l' Q hQ with h1 | ⟨_, rfl⟩
    · exact h.1 s' l' Q h1 v hv
    · exact hP v hv
  · intro v hv
    rw [hg] at hv
    exact hd _ _ _ (h.2.1 v hv)
  · intro s' l' hl' w
    rw [he] at hl'
    exact h.2.2 s' l' hl' w

lemma insertResult_guesses (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) : (insertResult pp st s l P).guesses = st.guesses :=
  (insertResult_props pp st s l P).1

lemma observeGroup_shInv (σ : LabelEncoding P0) (st : State pp) (gq : GQuery P0)
    (R : gq.Result) (h : ShInv pp σ st) :
    ShInv pp σ (observeGroup pp σ st gq R) ∧
      (∀ v ∈ st.guesses, v ∈ (observeGroup pp σ st gq R).guesses) ∧
      ∀ v ∈ (observeGroup pp σ st gq R).guesses, v ∈ st.guesses ∨
        v ∈ newGuesses pp st (observeGroup pp σ st gq R) gq := by
  have hvars_sum : ∀ (a b : k) (P Q : Poly pp) (G : Finset GuessVar),
      (∀ v ∈ P.vars, v ∈ G) → (∀ v ∈ Q.vars, v ∈ G) →
      ∀ v ∈ (scalar pp a * P + scalar pp b * Q).vars, v ∈ G := by
    intro a b P Q G hP hQ v hv
    have h1 := MvPolynomial.vars_add_subset (scalar pp a * P) (scalar pp b * Q) hv
    rcases Finset.mem_union.mp h1 with h2 | h2
    · have h3 := MvPolynomial.vars_mul (scalar pp a) P h2
      rcases Finset.mem_union.mp h3 with h4 | h4
      · simp [scalar] at h4
      · exact hP v h4
    · have h3 := MvPolynomial.vars_mul (scalar pp b) Q h2
      rcases Finset.mem_union.mp h3 with h4 | h4
      · simp [scalar] at h4
      · exact hQ v h4
  cases gq with
  | lin s a b u v =>
    obtain ⟨hx, hxv⟩ := resolve_shInv pp σ st s u h
    obtain ⟨hy, hyv⟩ := resolve_shInv pp σ (resolve pp σ st s u).2 s v hx
    obtain ⟨_, hxg, hxg', _⟩ := resolve_props pp σ st s u
    obtain ⟨_, hyg, hyg', _⟩ := resolve_props pp σ (resolve pp σ st s u).2 s v
    have key : ShInv pp σ (observeGroup pp σ st (.lin s a b u v) R) ∧
        (observeGroup pp σ st (.lin s a b u v) R).guesses =
          (resolve pp σ (resolve pp σ st s u).2 s v).2.guesses := by
      simp only [observeGroup]
      cases hP : (resolve pp σ st s u).1 with
      | none => exact ⟨hy, rfl⟩
      | some P =>
        cases hQ : (resolve pp σ (resolve pp σ st s u).2 s v).1 with
        | none => exact ⟨hy, rfl⟩
        | some Q =>
          cases R with
          | none => exact ⟨hy, rfl⟩
          | some l =>
            refine ⟨insertResult_shInv pp σ _ s l _ hy ?_, insertResult_guesses pp _ s l _⟩
            exact hvars_sum a b P Q _ (fun w hw => hyg' w (hxv P hP w hw)) (hyv Q hQ)
    refine ⟨key.1, fun w hw => ?_, fun w hw => ?_⟩
    · rw [key.2]; exact hyg' w (hxg' w hw)
    · rw [key.2] at hw
      by_cases hw0 : w ∈ st.guesses
      · exact Or.inl hw0
      · right
        simp only [newGuesses]
        rw [List.mem_dedup, List.mem_filter]
        refine ⟨?_, ?_⟩
        · rcases hyg w hw with h1 | ⟨rfl, _⟩
          · rcases hxg w h1 with h2 | ⟨rfl, _⟩
            · exact absurd h2 hw0
            · simp
          · simp
        · rw [key.2]
          simp [hw, hw0]
  | pair u v =>
    obtain ⟨hx, hxv⟩ := resolve_shInv pp σ st .g₁ u h
    obtain ⟨hy, hyv⟩ := resolve_shInv pp σ (resolve pp σ st .g₁ u).2 .g₂ v hx
    obtain ⟨_, hxg, hxg', _⟩ := resolve_props pp σ st .g₁ u
    obtain ⟨_, hyg, hyg', _⟩ := resolve_props pp σ (resolve pp σ st .g₁ u).2 .g₂ v
    have key : ShInv pp σ (observeGroup pp σ st (.pair u v) R) ∧
        (observeGroup pp σ st (.pair u v) R).guesses =
          (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).2.guesses := by
      simp only [observeGroup]
      cases hP : (resolve pp σ st .g₁ u).1 with
      | none => exact ⟨hy, rfl⟩
      | some P =>
        cases hQ : (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).1 with
        | none => exact ⟨hy, rfl⟩
        | some Q =>
          cases R with
          | none => exact ⟨hy, rfl⟩
          | some l =>
            refine ⟨insertResult_shInv pp σ _ .gₜ l _ hy ?_, insertResult_guesses pp _ .gₜ l _⟩
            intro w hw
            rcases Finset.mem_union.mp (MvPolynomial.vars_mul P Q hw) with h1 | h1
            · exact hyg' w (hxv P hP w h1)
            · exact hyv Q hQ w h1
    refine ⟨key.1, fun w hw => ?_, fun w hw => ?_⟩
    · rw [key.2]; exact hyg' w (hxg' w hw)
    · rw [key.2] at hw
      by_cases hw0 : w ∈ st.guesses
      · exact Or.inl hw0
      · right
        simp only [newGuesses]
        rw [List.mem_filter]
        refine ⟨?_, ?_⟩
        · rcases hyg w hw with h1 | ⟨rfl, _⟩
          · rcases hxg w h1 with h2 | ⟨rfl, _⟩
            · exact absurd h2 hw0
            · simp
          · simp
        · rw [key.2]
          simp [hw, hw0]
  | name u =>
    have key : ShInv pp σ (observeGroup pp σ st (.name u) R) ∧
        (observeGroup pp σ st (.name u) R).guesses = st.guesses := by
      simp only [observeGroup]
      split
      · exact ⟨h, rfl⟩
      · rename_i nm _
        refine ⟨insertResult_shInv pp σ _ .gₜ _ _ h ?_, insertResult_guesses pp _ .gₜ _ _⟩
        intro w hw
        rw [MvPolynomial.vars_neg] at hw
        cases hu : st.dict .gₜ u with
        | none => rw [hu] at hw; simp at hw
        | some P => rw [hu] at hw; exact h.1 .gₜ u P hu w hw
    refine ⟨key.1, fun w hw => by rw [key.2]; exact hw, fun w hw => ?_⟩
    rw [key.2] at hw
    exact Or.inl hw

lemma valueAt_eq_evaluate (ord : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (σ : LabelEncoding P0) (P : Poly pp)
    (h : ∀ v ∈ P.vars, x (ord.idxOf v) = (Algebra.decodeLabel (σ v.1) v.2).getD 0) :
    valueAt pp ord c x P = evaluate pp σ c P := by
  unfold valueAt evaluate
  simp only [MvPolynomial.coe_eval₂Hom]
  apply MvPolynomial.eval₂_congr
  intro i d hi hd
  apply h
  rw [MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨d, MvPolynomial.mem_support_iff.mpr hd, hi⟩

theorem cons_step_proof (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) :
    ConsStep pp r c x := by
  intro g gq σ hI hσ hgv hcl hpre
  obtain ⟨hfirst, _, hcov, hvars, _, hiff, hgd⟩ := hI
  rw [mem_cons_iff] at hσ
  have hsh : ShInv pp σ g.shadow :=
    ⟨fun s l P hP v hv => (hiff v).mp (hvars s l P hP v hv), hgd, hσ.2⟩
  obtain ⟨hsh', _, hgnew⟩ := observeGroup_shInv pp σ g.shadow gq (realResult pp σ g gq) hsh
  have hdec : ∀ v ∈ g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq,
      x ((g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq).idxOf v) =
        (Algebra.decodeLabel (σ v.1) v.2).getD 0 := by
    intro v hv
    set o := g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq
    have hlt : o.idxOf v < o.length := List.idxOf_lt_length_of_mem hv
    obtain ⟨t, ht⟩ := hpre
    have hget : r.order[o.idxOf v]? = some v := by
      rw [← ht, List.getElem?_append_left hlt]
      exact List.getElem?_idxOf hv
    rw [← hgv]
    simp only [guessValuesσ, hget]
  have hF : Faithful pp σ c g.shadow := by
    intro s l P hP
    have he : evaluate pp σ c P = valueAt pp g.order c x P := by
      symm
      apply valueAt_eq_evaluate
      intro v hv
      have hvo : v ∈ g.order := hvars s l P hP v hv
      have h1 := hdec v (List.mem_append_left _ hvo)
      rwa [List.idxOf_append_of_mem hvo] at h1
    rw [he]
    exact hσ.1 s l P hP
  have hS : Sound pp σ c g.shadow := ⟨hF, fun e he => by rw [hfirst] at he; cases he⟩
  have hcov' : ∀ l ∈ g.oracle.issuedT, ∃ P, g.shadow.dict .gₜ l = some P :=
    fun l hl => Option.isSome_iff_exists.mp (hcov l hl)
  have hS' := observeGroup_sound pp σ c g.shadow g.oracle.issuedT gq hS hcov'
  rw [mem_cons_iff]
  refine ⟨fun s l P hP => ?_, hsh'.2.2⟩
  have he : valueAt pp (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq) c x P =
      evaluate pp σ c P := by
    apply valueAt_eq_evaluate
    intro v hv
    apply hdec
    rcases hgnew v (hsh'.1 s l P hP v hv) with h1 | h1
    · exact List.mem_append_left _ ((hiff v).mpr h1)
    · exact List.mem_append_right _ h1
  rw [he]
  exact hS'.1 s l P hP

lemma handOut_issuedT (qr : GQuery P0) (R : qr.Result) (st : OracleState P0) :
    ∀ w ∈ support ((handOut qr R).run st), w.2.issuedT = st.issuedT := by
  intro w hw
  cases qr with
  | lin s a b u v => simp [handOut] at hw; rw [hw]
  | pair u v => simp [handOut] at hw; rw [hw]
  | name v =>
    cases R with
    | none => simp [handOut] at hw; rw [hw]
    | some nm =>
      simp only [handOut, nameRef, StateT.run_map, StateT.run_bind, StateT.run_get,
        pure_bind] at hw
      cases hn : st.names.findIdx? (· == nm) <;>
        simp [hn, StateT.run_set, StateT.run_pure] at hw <;> rw [hw]

lemma finishGroup_issued (gq : GQuery P0) (R : gq.Result) (st : OracleState P0) :
    ∀ w ∈ support ((finishGroup gq R).run st), ∀ l ∈ w.2.issuedT,
      l ∈ st.issuedT ∨ ∃ e, trEntry gq R = some e ∧ e.issuedGT = some l := by
  intro w hw l hl
  unfold finishGroup at hw
  cases ht : trEntry gq R with
  | none =>
    simp only [ht, StateT.run_bind, StateT.run_pure, pure_bind] at hw
    rw [handOut_issuedT gq R st w hw] at hl
    exact Or.inl hl
  | some e =>
    simp only [ht, StateT.run_bind, StateT.run_modify, pure_bind] at hw
    rw [handOut_issuedT gq R _ w hw] at hl
    cases hi : e.issuedGT with
    | none => simp only [hi] at hl; exact Or.inl hl
    | some l' =>
      simp only [hi, Finset.mem_insert] at hl
      rcases hl with rfl | hl
      · exact Or.inr ⟨e, rfl, hi⟩
      · exact Or.inl hl

lemma resolve_some_of_decode (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (w : k) (h : Algebra.decodeLabel (σ s) l = some w) :
    ∃ P, (resolve pp σ st s l).1 = some P := by
  unfold resolve
  cases hd : st.dict s l with
  | some P => exact ⟨P, by simp⟩
  | none => simp [h]

lemma insertResult_isSome (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) : ((insertResult pp st s l P).dict s l).isSome := by
  unfold insertResult
  cases hd : st.dict s l with
  | none => simp [record]
  | some Q =>
    simp only
    split_ifs <;> simp [hd]

lemma observeGroup_result (σ : LabelEncoding P0) (st : State pp) (issued : Finset (Label P0))
    (gq : GQuery P0) (l : Label P0) (e : TrOp P0)
    (he : trEntry gq (groupAnswer σ issued gq) = some e) (hl : e.issuedGT = some l) :
    ((observeGroup pp σ st gq (groupAnswer σ issued gq)).dict .gₜ l).isSome := by
  cases gq with
  | lin s a b u v =>
    cases hR : groupAnswer σ issued (.lin s a b u v) with
    | none => simp [trEntry, hR] at he
    | some l' =>
      simp only [trEntry, hR, Option.map_some] at he
      cases he
      cases s <;> simp only [TrOp.issuedGT, reduceCtorEq, Option.some.injEq] at hl
      subst hl
      have hdec : ∃ xu xv, Algebra.decodeLabel (σ .gₜ) u = some xu ∧
          Algebra.decodeLabel (σ .gₜ) v = some xv := by
        simp only [groupAnswer] at hR
        cases hu : Algebra.decodeLabel (σ .gₜ) u <;> cases hv : Algebra.decodeLabel (σ .gₜ) v <;>
          simp [hu, hv] at hR
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨xu, xv, hu, hv⟩ := hdec
      obtain ⟨P, hP⟩ := resolve_some_of_decode pp σ st .gₜ u xu hu
      obtain ⟨Q, hQ⟩ := resolve_some_of_decode pp σ (resolve pp σ st .gₜ u).2 .gₜ v xv hv
      simp only [observeGroup, hP, hQ]
      exact insertResult_isSome pp _ .gₜ _ _
  | pair u v =>
    cases hR : groupAnswer σ issued (.pair u v) with
    | none => simp [trEntry, hR] at he
    | some l' =>
      simp only [trEntry, hR, Option.map_some] at he
      cases he
      simp only [TrOp.issuedGT, Option.some.injEq] at hl
      subst hl
      have hdec : ∃ xu xv, Algebra.decodeLabel (σ .g₁) u = some xu ∧
          Algebra.decodeLabel (σ .g₂) v = some xv := by
        simp only [groupAnswer] at hR
        cases hu : Algebra.decodeLabel (σ .g₁) u <;> cases hv : Algebra.decodeLabel (σ .g₂) v <;>
          simp [hu, hv] at hR
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨xu, xv, hu, hv⟩ := hdec
      obtain ⟨P, hP⟩ := resolve_some_of_decode pp σ st .g₁ u xu hu
      obtain ⟨Q, hQ⟩ := resolve_some_of_decode pp σ (resolve pp σ st .g₁ u).2 .g₂ v xv hv
      simp only [observeGroup, hP, hQ]
      exact insertResult_isSome pp _ .gₜ _ _
  | name u =>
    cases hR : groupAnswer σ issued (.name u) with
    | none => simp [trEntry, hR] at he
    | some nm =>
      simp only [trEntry, hR, Option.map_some] at he
      cases he
      simp [TrOp.issuedGT] at hl

lemma observeGroup_mono (σ : LabelEncoding P0) (st : State pp) (gq : GQuery P0)
    (R : gq.Result) :
    ∀ s l P, st.dict s l = some P → (observeGroup pp σ st gq R).dict s l = some P := by
  intro s' l' P hP
  cases gq with
  | lin s a b u v =>
    have h1 := (resolve_props pp σ st s u).2.2.2.1 s' l' P hP
    have h2 := (resolve_props pp σ (resolve pp σ st s u).2 s v).2.2.2.1 s' l' P h1
    simp only [observeGroup]
    cases (resolve pp σ st s u).1 with
    | none => exact h2
    | some P1 =>
      cases (resolve pp σ (resolve pp σ st s u).2 s v).1 with
      | none => exact h2
      | some Q1 =>
        cases R with
        | none => exact h2
        | some l => exact (insertResult_props pp _ s l _).2.2.1 s' l' P h2
  | pair u v =>
    have h1 := (resolve_props pp σ st .g₁ u).2.2.2.1 s' l' P hP
    have h2 := (resolve_props pp σ (resolve pp σ st .g₁ u).2 .g₂ v).2.2.2.1 s' l' P h1
    simp only [observeGroup]
    cases (resolve pp σ st .g₁ u).1 with
    | none => exact h2
    | some P1 =>
      cases (resolve pp σ (resolve pp σ st .g₁ u).2 .g₂ v).1 with
      | none => exact h2
      | some Q1 =>
        cases R with
        | none => exact h2
        | some l => exact (insertResult_props pp _ .gₜ l _).2.2.1 s' l' P h2
  | name u =>
    simp only [observeGroup]
    cases R with
    | none => exact hP
    | some nm => exact (insertResult_props pp _ .gₜ _ _).2.2.1 s' l' P hP

lemma newGuesses_mem (before after : State pp) (gq : GQuery P0) (v : GuessVar)
    (h : v ∈ newGuesses pp before after gq) : v ∈ after.guesses ∧ v ∉ before.guesses := by
  cases gq with
  | lin s a b u w =>
    simp only [newGuesses, List.mem_dedup, List.mem_filter, decide_eq_true_eq] at h
    exact h.2
  | pair u w =>
    simp only [newGuesses, List.mem_filter, decide_eq_true_eq] at h
    exact h.2
  | name u => simp [newGuesses] at h

lemma newGuesses_nodup (before after : State pp) (gq : GQuery P0) :
    (newGuesses pp before after gq).Nodup := by
  cases gq with
  | lin s a b u w => exact List.nodup_dedup _
  | pair u w =>
    apply List.Nodup.filter
    simp
  | name u => simp [newGuesses]

theorem cover_step_proof (c : CoinDomain pp) (x : ℕ → k) : CoverStep pp c x := by
  intro g gq σ w hI hσ hw _
  obtain ⟨_, _, hcov, hvars, hnodup, hiff, hgd⟩ := hI
  rw [mem_cons_iff] at hσ
  have hsh : ShInv pp σ g.shadow :=
    ⟨fun s l P hP v hv => (hiff v).mp (hvars s l P hP v hv), hgd, hσ.2⟩
  obtain ⟨hsh', hgold, hgnew⟩ := observeGroup_shInv pp σ g.shadow gq (realResult pp σ g gq) hsh
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    change ((realShadow pp σ g gq).dict .gₜ l).isSome
    rcases finishGroup_issued gq (realResult pp σ g gq) g.oracle w hw l hl with h1 | ⟨e, he, hel⟩
    · obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (hcov l h1)
      simp only [realShadow]
      rw [observeGroup_mono pp σ g.shadow gq _ .gₜ l P hP]
      rfl
    · exact observeGroup_result pp σ g.shadow g.oracle.issuedT gq l e he hel
  · intro s l P hP v hv
    rcases hgnew v (hsh'.1 s l P hP v hv) with h1 | h1
    · exact List.mem_append_left _ ((hiff v).mpr h1)
    · exact List.mem_append_right _ h1
  · change (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq).Nodup
    rw [List.nodup_append]
    refine ⟨hnodup, newGuesses_nodup pp _ _ gq, ?_⟩
    intro a ha b hb hab
    subst hab
    exact (newGuesses_mem pp _ _ gq a hb).2 ((hiff a).mp ha)
  · intro v
    change v ∈ g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq ↔
      v ∈ (realShadow pp σ g gq).guesses
    constructor
    · intro hv
      rcases List.mem_append.mp hv with h1 | h1
      · exact hgold v ((hiff v).mp h1)
      · exact (newGuesses_mem pp _ _ gq v h1).1
    · intro hv
      rcases hgnew v hv with h1 | h1
      · exact List.mem_append_left _ ((hiff v).mpr h1)
      · exact List.mem_append_right _ h1
  · exact hsh'.2.1

lemma uniformFin_lt_prob (M K : ℕ) (hK : K ≤ M + 1) :
    Pr[fun u : Fin (M + 1) => u.val < K | $[0..M]] = (K : ℝ≥0∞) / (M + 1 : ℕ) := by
  have hcard : (Finset.univ.filter (fun i : Fin (M + 1) => i.val < K)).card = K := by
    rw [Fin.card_filter_val_lt]
    exact min_eq_right hK
  change Pr[fun i : Fin (M + 1) => i.val < K | $ᵗ (Fin (M + 1))] = _
  rw [probEvent_uniformSample, hcard, Fintype.card_fin]

lemma uniformFin_ge_prob (M K : ℕ) (hK : K ≤ M + 1) :
    Pr[fun u : Fin (M + 1) => ¬ u.val < K | $[0..M]] = ((M + 1 - K : ℕ) : ℝ≥0∞) / (M + 1 : ℕ) := by
  have hcard : (Finset.univ.filter (fun i : Fin (M + 1) => ¬ i.val < K)).card = M + 1 - K := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (M + 1))))
      (fun i : Fin (M + 1) => i.val < K)
    rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin, min_eq_right hK] at h
    omega
  change Pr[fun i : Fin (M + 1) => ¬ i.val < K | $ᵗ (Fin (M + 1))] = _
  rw [probEvent_uniformSample, hcard, Fintype.card_fin]

def guessState (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0) : State pp :=
  { st with
    dict := record pp st.dict s l (MvPolynomial.X (s, l))
    guesses := insert (s, l) st.guesses }

section Atomic

variable (O : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)

lemma genericResolve_inj (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h1 : st.dict s l = none) (b₁ b₂ : Bool)
    (h : genericResolve pp st s l b₁ = genericResolve pp st s l b₂) : b₁ = b₂ := by
  unfold genericResolve at h
  simp only [h1] at h
  cases b₁ <;> cases b₂ <;> simp_all

lemma resolve_valid_count (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (w : k) (h1 : st.dict s l = none) (h2 : l ∉ st.excluded s)
    (hw : Algebra.decodeLabel (σ s) l = some w)
    (hσ : σ ∈ cons pp (resolve pp σ st s l).2 O c x) :
    ((cons pp (resolve pp σ st s l).2 O c x).card : ℝ≥0∞) ≤
      (cons pp st O c x).card * Pr[= resolve pp σ st s l | (referenceResolve pp s l).run st] *
        ((Fintype.card k - (assigned pp st s).card : ℕ) : ℝ≥0∞)⁻¹ := by
  have hres : resolve pp σ st s l = (some (MvPolynomial.X (s, l)), guessState pp st s l) := by
    unfold resolve guessState; simp [h1, hw]
  rw [hres] at hσ ⊢
  have hcg : cons pp (guessState pp st s l) O c x = (cons pp st O c x).filter fun σ =>
      σ s (valueAt pp O c x (MvPolynomial.X (s, l))) = l := by
    unfold guessState
    exact cons_record pp st O c x s l _ _ h1
  rw [hcg] at hσ ⊢
  set v := valueAt pp O c x (MvPolynomial.X (s, l))
  have hσ0 : σ ∈ cons pp st O c x := (Finset.mem_filter.mp hσ).1
  have hl : l ∈ available pp st s := mem_available pp st s l h1 h2
  have hv : v ∉ valuesOf pp st O c x s := by
    intro hv
    simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨l', P, hP, hPv⟩ := hv
    have e1 := (mem_cons_iff pp st O c x σ).mp hσ0 |>.1 s l' P hP
    have e2 := (Finset.mem_filter.mp hσ).2
    rw [hPv] at e1
    rw [e1] at e2
    subst e2
    rw [h1] at hP
    cases hP
  have hcount := card_cons_eq pp st O c x s v hv l hl
  have hA := card_available pp st O c x s σ hσ0
  have hV := card_values pp st O c x s σ hσ0
  have hUA := unassigned_le_available pp st O c x s σ hσ0
  set a := (assigned pp st s).card
  set e := (st.excluded s).card
  set N := 2 ^ P0.labelBits
  have hq : (valuesOf pp st O c x s).card < Fintype.card k := by
    apply Finset.card_lt_card
    exact ⟨Finset.subset_univ _, fun h => hv (h (Finset.mem_univ v))⟩
  rw [hV] at hq hUA

  have hprob : Pr[= (some (MvPolynomial.X (s, l)), guessState pp st s l) |
      (referenceResolve pp s l).run st] =
      ((P0.q - a : ℕ) : ℝ≥0∞) / ((N - a - e - 1 + 1 : ℕ) : ℝ≥0∞) := by
    rw [refResolve_fresh pp st s l h1 h2, ← probEvent_eq_eq_probOutput, probEvent_map]
    have hg : genericResolve pp st s l true = (some (MvPolynomial.X (s, l)), guessState pp st s l) := by
      unfold genericResolve guessState; simp [h1]
    rw [← hg]
    have := uniformFin_lt_prob (N - a - e - 1) (P0.q - a) (by
      have : (available pp st s).card ≥ 1 := Finset.card_pos.mpr ⟨l, hl⟩
      rw [ZMod.card] at hUA
      omega)
    rw [← this]
    apply probEvent_congr' _ rfl
    intro u _
    constructor
    · intro h
      have := genericResolve_inj pp st s l h1 _ _ h
      simpa using this
    · intro h
      show genericResolve pp st s l (decide (u.val < P0.q - a)) = genericResolve pp st s l true
      rw [decide_eq_true h]
  rw [hprob]
  have hav : (available pp st s).card ≥ 1 := Finset.card_pos.mpr ⟨l, hl⟩
  have hN : N - a - e - 1 + 1 = (available pp st s).card := by omega
  rw [hN, ZMod.card]
  rw [ZMod.card] at hq

  set C := (cons pp st O c x).card
  set F := ((cons pp st O c x).filter fun σ => σ s v = l).card
  set A := (available pp st s).card
  have hC : (C : ℝ≥0∞) = A * F := by exact_mod_cast hcount
  have hqa : ((P0.q - a : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : 0 < P0.q - a := by omega
    exact_mod_cast this.ne'
  have hA0 : (A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  rw [hC, ENNReal.div_eq_inv_mul]
  apply le_of_eq
  have e1 : (A : ℝ≥0∞) * (A : ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel hA0 (ENNReal.natCast_ne_top _)
  have e2 : ((P0.q - a : ℕ) : ℝ≥0∞) * ((P0.q - a : ℕ) : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hqa (ENNReal.natCast_ne_top _)
  calc (F : ℝ≥0∞) = F * ((A : ℝ≥0∞) * (A : ℝ≥0∞)⁻¹) *
        (((P0.q - a : ℕ) : ℝ≥0∞) * ((P0.q - a : ℕ) : ℝ≥0∞)⁻¹) := by rw [e1, e2, mul_one, mul_one]
    _ = _ := by ring

end Atomic

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation
