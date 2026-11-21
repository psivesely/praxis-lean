import Praxis.Proofs.GroupModel.Split.Lazy.CouplingPending
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.Coupling
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Disintegration
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

lemma insert_count (st : State pp) (O : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (C : Poly pp) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp st O c x) (hσ' : σ ∈ cons pp (insertResult pp st s l C) O c x)
    (hf0 : st.first = none) (hcl : (insertResult pp st s l C).first = none) :
    ((cons pp (insertResult pp st s l C) O c x).card : ℝ≥0∞) ≤
      (cons pp st O c x).card *
        Pr[= (l, insertResult pp st s l C) | (referenceInsert pp s C).run st] := by
  have hcons := (mem_cons_iff pp st O c x σ).mp hσ
  cases hd : st.dict s l with
  | some C' =>
    have hCC : C = C' := by
      by_contra hne
      have := insertResult_first_of_new pp st s l C C' hd hne hf0
      rw [hcl] at this
      cases this
    subst hCC
    have hins : insertResult pp st s l C = st := by
      unfold insertResult
      simp [hd]
    rw [hins]
    have hval : σ s (valueAt pp O c x C) = l := hcons.1 s l C hd
    have hlab : labelOf pp st s C = some l := by
      cases h : labelOf pp st s C with
      | none => exact absurd hd (labelOf_none pp st s C h l)
      | some l₀ =>
        have h1 := labelOf_some pp st s C l₀ h
        have e1 := hcons.1 s l₀ C h1
        rw [hval] at e1
        rw [e1]
    have hrun : (referenceInsert pp s C).run st = pure (l, st) := by
      simp [referenceInsert, hlab, StateT.run_bind, StateT.run_get]
    rw [hrun, probOutput_pure_self, mul_one]
  | none =>
    have hins : insertResult pp st s l C = {st with dict := record pp st.dict s l C} := by
      unfold insertResult
      simp [hd]
    have hσ'' := (mem_cons_iff pp _ O c x σ).mp hσ'
    have hval : σ s (valueAt pp O c x C) = l := by
      apply hσ''.1 s l C
      rw [hins]
      exact record_same pp st.dict s l C
    have hlab : labelOf pp st s C = none := by
      cases h : labelOf pp st s C with
      | none => rfl
      | some l₀ =>
        exfalso
        have h1 := labelOf_some pp st s C l₀ h
        have e1 := hcons.1 s l₀ C h1
        rw [hval] at e1
        rw [← e1, hd] at h1
        cases h1
    have hav : l ∈ available pp st s :=
      mem_available pp st s l hd (fun hex => hcons.2 s l hex _ hval)
    have hne : (available pp st s).Nonempty := ⟨l, hav⟩
    have hrun : (referenceInsert pp s C).run st =
        (fun l' => (l', ({st with dict := record pp st.dict s l' C} : State pp))) <$>
          Coupling.uniform (available pp st s) := by
      simp [referenceInsert, hlab, StateT.run_bind, StateT.run_get, StateT.run_lift,
        StateT.run_set, map_eq_bind_pure_comp]
    rw [hins, hrun]
    have hinj : Function.Injective
        (fun l' => (l', ({st with dict := record pp st.dict s l' C} : State pp))) := by
      intro a b h
      exact congrArg Prod.fst h
    rw [show ((l, ({st with dict := record pp st.dict s l C} : State pp)) : Label P0 × State pp) =
      (fun l' => (l', ({st with dict := record pp st.dict s l' C} : State pp))) l from rfl,
      probOutput_map_injective _ hinj, Coupling.uniform_mass _ hne, if_pos hav]
    rw [cons_record pp st O c x s l C st.guesses hd]
    have hv : valueAt pp O c x C ∉ valuesOf pp st O c x s := by
      intro hv
      simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨l', P, hP, hPv⟩ := hv
      have e1 := hcons.1 s l' P hP
      rw [hPv, hval] at e1
      rw [← e1, hd] at hP
      cases hP
    have hcount := card_cons_eq pp st O c x s (valueAt pp O c x C) hv l hav
    set A := (available pp st s).card
    set F := ((cons pp st O c x).filter fun σ => σ s (valueAt pp O c x C) = l).card
    have hA0 : (A : ℝ≥0∞) ≠ 0 := by
      have : 0 < A := Finset.card_pos.mpr hne
      exact_mod_cast this.ne'
    rw [hcount]
    push_cast
    rw [mul_comm (A : ℝ≥0∞) (F : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hA0
      (ENNReal.natCast_ne_top _), mul_one]

lemma pool_factor_logged (r : Record pp) (O' : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (σ : LabelEncoding P0) (t : ℕ) (st₁ sh' : State pp) (v : GuessVar)
    (hgs : r.guessShadow t = sh') (hpre : O' <+: r.order) (ht : O'[t]? = some v)
    (hnodup : O'.Nodup) (hxt : σ v.1 (x t) = v.2)
    (hsh'cons : σ ∈ cons pp sh' O' c x)
    (hvX : sh'.dict v.1 v.2 = some (MvPolynomial.X v))
    (hsub : ∀ s l P, st₁.dict s l = some P → sh'.dict s l = some P ∧ ∀ w ∈ P.vars, O'.idxOf w < t)
    (hσ₁ : σ ∈ cons pp st₁ O' c x) :
    ((Fintype.card k - (assigned pp st₁ v.1).card : ℕ) : ℝ≥0∞)⁻¹ ≤ poolFactor pp r c x t := by
  haveI : Nontrivial (Coeff pp) := (atCoin pp c).domain_nontrivial
  obtain ⟨rest, hrest⟩ := hpre
  have htlt : t < O'.length := (List.getElem?_eq_some_iff.mp ht).1
  have hsort : r.sortAt t = v.1 := by
    unfold Record.sortAt
    rw [← hrest, List.getElem?_append_left htlt, ht]
    rfl
  have hidx : O'.idxOf v = t := idxOf_of_getElem? O' hnodup t v ht
  have hvO : v ∈ O' := List.mem_of_getElem? ht

  have hin : ∀ w, r.order.idxOf w < t → w ∈ O' ∧ r.order.idxOf w = O'.idxOf w := by
    intro w hw
    by_cases hwO : w ∈ O'
    · refine ⟨hwO, ?_⟩
      rw [← hrest, List.idxOf_append_of_mem hwO]
    · exfalso
      rw [← hrest, List.idxOf_append_of_notMem hwO] at hw
      omega
  have hval : ∀ P : Poly pp, (∀ w ∈ P.vars, w ∈ O') →
      valueAt pp r.order c x P = valueAt pp O' c x P := by
    intro P hP
    rw [← hrest]
    exact valueAt_append pp O' rest c x P hP
  have hsubU : valuesOf pp st₁ O' c x v.1 ⊆ usedBefore pp r c t x := by
    intro a ha
    simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨l, P, hP, rfl⟩ := ha
    obtain ⟨h1, h2⟩ := hsub v.1 l P hP
    have hvars : ∀ w ∈ P.vars, w ∈ O' := fun w hw =>
      List.idxOf_lt_length_iff.mp (lt_trans (h2 w hw) htlt)
    simp only [usedBefore, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hgs, hsort]
    refine ⟨l, P, h1, fun w hw => ?_, hval P hvars⟩
    rw [← hrest, List.idxOf_append_of_mem (hvars w hw)]
    exact h2 w hw
  have hnot : x t ∉ usedBefore pp r c t x := by
    intro hx
    simp only [usedBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hgs, hsort] at hx
    obtain ⟨l, P, hP, hvars, hvl⟩ := hx
    have hvars' : ∀ w ∈ P.vars, w ∈ O' := fun w hw => (hin w (hvars w hw)).1
    rw [hval P hvars'] at hvl
    have e1 := ((mem_cons_iff pp sh' O' c x σ).mp hsh'cons).1 v.1 l P hP
    rw [hvl, hxt] at e1
    rw [← e1, hvX] at hP
    have hPX : P = MvPolynomial.X v := (Option.some.inj hP).symm
    subst hPX
    have h3 := hvars v (by rw [MvPolynomial.vars_X]; exact Finset.mem_singleton_self _)
    rw [(hin v h3).2, hidx] at h3
    exact lt_irrefl _ h3
  have hmem : x t ∈ Finset.univ \ usedBefore pp r c t x :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
  have hpool : guessPool pp r c t x = Finset.univ \ usedBefore pp r c t x := by
    unfold guessPool
    rw [if_pos ⟨x t, hmem⟩]
  unfold poolFactor
  rw [if_pos (by rw [hpool]; exact hmem)]
  apply ENNReal.inv_le_inv.mpr
  have hV := card_values pp st₁ O' c x v.1 σ hσ₁
  have hcardU := Finset.card_le_card hsubU
  rw [hV] at hcardU
  rw [hpool, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  exact_mod_cast (by omega :
    Fintype.card k - (usedBefore pp r c t x).card ≤ Fintype.card k - (assigned pp st₁ v.1).card)

lemma resolve_fresh_dict (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (h1 : st.dict s l = none) (h2 : (Algebra.decodeLabel (σ s) l).isSome) :
    (resolve pp σ st s l).2.dict s l = some (MvPolynomial.X (s, l)) := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h2
  have hres : (resolve pp σ st s l).2 = guessState pp st s l := by
    unfold resolve guessState; simp [h1, hw]
  rw [hres]
  unfold guessState
  exact record_same pp st.dict s l _

lemma count_two (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (g : GenState pp)
    (σ : LabelEncoding P0) (s₁ s₂ s₃ : GroupModel.Sorted.PSort) (u v : Label P0)
    (C : Poly pp → Poly pp → Poly pp) (R : Option (Label P0)) (sh' : State pp)
    (O' : List GuessVar)
    (hI : Inv pp g) (hσ : σ ∈ cons pp g.shadow g.order c x) (hx : guessValuesσ pp r σ = x)
    (hO' : O' = g.order ++ ng2 g.shadow.guesses
      (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v))
    (hpre : O' <+: r.order)
    (hgs : ∀ t, g.order.length ≤ t → t < O'.length → r.guessShadow t = sh')
    (hsh' : sh' = match (resolve pp σ g.shadow s₁ u).1,
        (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).1, R with
      | some P, some Q, some l =>
          insertResult pp (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2 s₃ l (C P Q)
      | _, _, _ => (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2)
    (hRiff : R.isSome ↔ ((resolve pp σ g.shadow s₁ u).1.isSome ∧
      (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).1.isSome))
    (hcl : sh'.first = none) (hcons' : σ ∈ cons pp sh' O' c x) :
    ((cons pp sh' O' c x).card : ℝ≥0∞) * guessFactor pp r c x O'.length ≤
      (cons pp g.shadow g.order c x).card *
        Pr[= (R, sh') | ((do
            let x ← referenceResolve pp s₁ u
            let y ← referenceResolve pp s₂ v
            match x, y with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run g.shadow] *
        guessFactor pp r c x g.order.length := by
  obtain ⟨hL, hnodup, hdecL, hσL, hσ1, hσ2⟩ :=
    two_facts pp r c x g O' s₁ s₂ u v hI hpre σ hσ hx hO'.symm
  have hI' := hI
  obtain ⟨hfirst, hord, _, hvars, _, hiff, hgd⟩ := hI'
  set st := g.shadow with hst
  set O := g.order with hO
  set ρ₁ := resolve pp σ st s₁ u with hρ₁
  set ρ₂ := resolve pp σ ρ₁.2 s₂ v with hρ₂
  have hmono1 : ∀ s l P, st.dict s l = some P → ρ₁.2.dict s l = some P :=
    (resolve_props pp σ st s₁ u).2.2.2.1
  have hmono2 : ∀ s l P, ρ₁.2.dict s l = some P → ρ₂.2.dict s l = some P :=
    (resolve_props pp σ ρ₁.2 s₂ v).2.2.2.1
  have hmono3 : ∀ s l P, ρ₂.2.dict s l = some P → sh'.dict s l = some P := by
    intro s l P hP
    rw [hsh']
    split
    · exact (insertResult_props pp _ _ _ _).2.2.1 s l P hP
    · exact hP
  have hf2 : ρ₂.2.first = none := by
    rw [(resolve_props pp σ ρ₁.2 s₂ v).1, (resolve_props pp σ st s₁ u).1]
    exact hfirst

  have hins : ((cons pp sh' O' c x).card : ℝ≥0∞) ≤ (cons pp ρ₂.2 O' c x).card *
      Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2] := by
    by_cases hboth : ρ₁.1.isSome ∧ ρ₂.1.isSome
    · obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hboth.1
      obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hboth.2
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hRiff.mpr hboth)
      have hsh2 : sh' = insertResult pp ρ₂.2 s₃ l (C P Q) := by
        rw [hsh']
        simp only [hP, hQ, hl]
      have hgen1 : ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2 =
          (fun z => (some z.1, z.2)) <$> (referenceInsert pp s₃ (C P Q)).run ρ₂.2 := by
        simp only [hP, hQ, StateT.run_map]
      rw [hgen1, hl]
      have hinj : Function.Injective (fun z : Label P0 × State pp => (some z.1, z.2)) := by
        intro a b h
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        exact Prod.ext h.1 h.2
      rw [show ((some l, sh') : Option (Label P0) × State pp) =
        (fun z : Label P0 × State pp => (some z.1, z.2)) (l, sh') from rfl,
        probOutput_map_injective _ hinj]
      rw [hsh2] at hcl hcons' ⊢
      exact insert_count pp ρ₂.2 O' c x s₃ l (C P Q) σ hσ2 hcons' hf2 hcl
    · have hR : R = none := by
        cases hRc : R with
        | none => rfl
        | some l =>
          exfalso
          exact hboth (hRiff.mp (by rw [hRc]; rfl))
      have hsh2 : sh' = ρ₂.2 := by
        rw [hsh', hR]
        rcases ρ₁.1 with _ | P <;> rcases ρ₂.1 with _ | Q <;> rfl
      have hgen1 : ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2 =
          pure (none, ρ₂.2) := by
        cases h1 : ρ₁.1 with
        | none => simp only [StateT.run_pure]
        | some P =>
          cases h2 : ρ₂.1 with
          | none => simp only [StateT.run_pure]
          | some Q =>
            exfalso
            exact hboth ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
      rw [hgen1, hR, hsh2, probOutput_pure_self, mul_one]

  have hgen : Pr[= ρ₁ | (referenceResolve pp s₁ u).run st] *
      (Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
        Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2]) ≤
      Pr[= (R, sh') | ((do
            let x ← referenceResolve pp s₁ u
            let y ← referenceResolve pp s₂ v
            match x, y with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run st] := by
    simp only [StateT.run_bind]
    rw [probOutput_bind_eq_tsum]
    refine le_trans ?_ (ENNReal.le_tsum ρ₁)
    refine mul_le_mul' le_rfl ?_
    rw [probOutput_bind_eq_tsum]
    exact ENNReal.le_tsum ρ₂

  have hsteps' : ∀ t, O.length ≤ t → t < O'.length → r.guessShadow t = sh' := hgs
  have hstsub : ∀ s l P, st.dict s l = some P →
      sh'.dict s l = some P ∧ ∀ w ∈ P.vars, O'.idxOf w < O.length := by
    intro s l P hP
    refine ⟨hmono3 s l P (hmono2 s l P (hmono1 s l P hP)), fun w hw => ?_⟩
    have hwO : w ∈ O := hvars s l P hP w hw
    rw [hL, List.idxOf_append_of_mem hwO]
    exact List.idxOf_lt_length_of_mem hwO
  set m₁ := if st.dict s₁ u = none ∧ (Algebra.decodeLabel (σ s₁) u).isSome
    then O.length + 1 else O.length with hm₁
  have step1 := atomic_step pp r st O' c x s₁ u σ O.length hσL hσ1 (by
    intro h1 h2
    have hfa : st.dict s₁ u = none ∧ (Algebra.decodeLabel (σ s₁) u).isSome := ⟨h1, h2⟩
    have ht : O'[O.length]? = some (s₁, u) := by
      rw [hL, List.getElem?_append_right le_rfl, Nat.sub_self, if_pos hfa]
      rfl
    have hlt : O.length < O'.length := (List.getElem?_eq_some_iff.mp ht).1
    refine ⟨lt_of_lt_of_le hlt hpre.length_le, ?_⟩
    have hxt : σ s₁ (x O.length) = u := by
      have h := hdecL (s₁, u) (List.mem_of_getElem? ht)
      rwa [idxOf_of_getElem? O' hnodup O.length (s₁, u) ht] at h
    have hvX : sh'.dict s₁ u = some (MvPolynomial.X (s₁, u)) :=
      hmono3 _ _ _ (hmono2 _ _ _ (resolve_fresh_dict pp σ st s₁ u h1 h2))
    exact pool_factor_logged pp r O' c x σ O.length st sh' (s₁, u) (hgs _ le_rfl hlt) hpre ht
      hnodup hxt hcons' hvX hstsub hσL)
  have step2 := atomic_step pp r ρ₁.2 O' c x s₂ v σ m₁ hσ1 hσ2 (by
    intro h1 h2
    have hfb : ρ₁.2.dict s₂ v = none ∧ (Algebra.decodeLabel (σ s₂) v).isSome := ⟨h1, h2⟩
    have ht : O'[m₁]? = some (s₂, v) := by
      rw [hL, hm₁]
      split_ifs with hfa
      · rw [List.getElem?_append_right (by omega)]
        simp
      · rw [List.getElem?_append_right le_rfl, Nat.sub_self]
        simp
    have hlt : m₁ < O'.length := (List.getElem?_eq_some_iff.mp ht).1
    refine ⟨lt_of_lt_of_le hlt hpre.length_le, ?_⟩
    have hxt : σ s₂ (x m₁) = v := by
      have h := hdecL (s₂, v) (List.mem_of_getElem? ht)
      rwa [idxOf_of_getElem? O' hnodup m₁ (s₂, v) ht] at h
    have hvX : sh'.dict s₂ v = some (MvPolynomial.X (s₂, v)) :=
      hmono3 _ _ _ (resolve_fresh_dict pp σ ρ₁.2 s₂ v h1 h2)
    have hm1O : O.length ≤ m₁ := by rw [hm₁]; split_ifs <;> omega
    refine pool_factor_logged pp r O' c x σ m₁ ρ₁.2 sh' (s₂, v) (hgs _ hm1O hlt) hpre ht
      hnodup hxt hcons' hvX ?_ hσ1
    intro s l P hP
    refine ⟨hmono3 s l P (hmono2 s l P hP), fun w hw => ?_⟩
    rcases resolve_dict pp σ st s₁ u s l P hP with h | ⟨hsl, hPX, hd1, hv1⟩
    · exact lt_of_lt_of_le ((hstsub s l P h).2 w hw) hm1O
    · have hsl' : s = s₁ ∧ l = u := Prod.mk.inj hsl
      obtain ⟨rfl, rfl⟩ := hsl'
      have hfa : st.dict s l = none ∧ (Algebra.decodeLabel (σ s) l).isSome := ⟨hd1, hv1⟩
      have ht1 : O'[O.length]? = some (s, l) := by
        rw [hL, List.getElem?_append_right le_rfl, Nat.sub_self, if_pos hfa]
        rfl
      rw [hPX] at hw
      rw [mem_vars_X hw, idxOf_of_getElem? O' hnodup O.length (s, l) ht1, hm₁, if_pos hfa]
      omega)
  have hm₂ : (if ρ₁.2.dict s₂ v = none ∧ (Algebra.decodeLabel (σ s₂) v).isSome
      then m₁ + 1 else m₁) = O'.length := by
    rw [hL, hm₁]
    split_ifs <;> simp
  rw [hm₂] at step2
  have hCL : cons pp st O' c x = cons pp st O c x := by
    rw [hL]
    exact cons_extend pp st O _ c x hvars
  rw [hCL] at step1
  calc ((cons pp sh' O' c x).card : ℝ≥0∞) * guessFactor pp r c x O'.length
      ≤ ((cons pp ρ₂.2 O' c x).card *
          Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2]) *
          guessFactor pp r c x O'.length := mul_le_mul' hins le_rfl
    _ = Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2] *
          ((cons pp ρ₂.2 O' c x).card * guessFactor pp r c x O'.length) := by ring
    _ ≤ Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2] *
          ((cons pp ρ₁.2 O' c x).card * Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
            guessFactor pp r c x m₁) := mul_le_mul' le_rfl step2
    _ = Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2] *
          Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
          ((cons pp ρ₁.2 O' c x).card * guessFactor pp r c x m₁) := by ring
    _ ≤ Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
            | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
            | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run ρ₂.2] *
          Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
          ((cons pp st O c x).card * Pr[= ρ₁ | (referenceResolve pp s₁ u).run st] *
            guessFactor pp r c x O.length) := mul_le_mul' le_rfl step1
    _ = (cons pp st O c x).card *
          (Pr[= ρ₁ | (referenceResolve pp s₁ u).run st] *
            (Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
              Pr[= (R, sh') | ((match ρ₁.1, ρ₂.1 with
                | some P, some Q => some <$> referenceInsert pp s₃ (C P Q)
                | _, _ => pure none) : StateT (State pp) ProbComp (Option (Label P0))).run
                  ρ₂.2])) *
          guessFactor pp r c x O.length := by ring
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hgen) le_rfl

lemma resolve_isSome_iff (σ : LabelEncoding P0) (st : State pp) (O : List GuessVar)
    (c : CoinDomain pp) (x : ℕ → k) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (hσ : σ ∈ cons pp st O c x) :
    (resolve pp σ st s l).1.isSome ↔ (Algebra.decodeLabel (σ s) l).isSome := by
  cases hd : st.dict s l with
  | some P =>
    rw [resolve_known pp σ st s l P hd]
    have h1 := ((mem_cons_iff pp st O c x σ).mp hσ).1 s l P hd
    rw [(decodeLabel_eq_some_iff _ _ _).mpr h1]
    simp
  | none =>
    cases hdec : Algebra.decodeLabel (σ s) l with
    | none => simp [resolve, hd, hdec]
    | some w => simp [resolve, hd, hdec]

theorem count_step_proof (n : ℕ) (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) :
    CountStep pp n r c x := by
  intro g gq σ w hI _ hr hgp hσ hx hcl _ hm
  have hI' := hI
  obtain ⟨hfirst, hord, hcov, hvars, hnd, hiff, hgd⟩ := hI'
  have hstep : r.steps[g.steps.length]? =
      some ⟨⟨.inl (.inl (.inr gq)), w.1⟩, realShadow pp σ g gq,
        g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq⟩ := by
    rw [hm]
    simp [afterGroup]
  have hpre : g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq <+: r.order :=
    hr _ (List.mem_of_getElem? hstep)
  have hgs : ∀ t, g.order.length ≤ t →
      t < (g.order ++ newGuesses pp g.shadow (realShadow pp σ g gq) gq).length →
      r.guessShadow t = realShadow pp σ g gq := by
    intro t ht1 ht2
    obtain ⟨rest, hrest⟩ := hgp
    have hstep' := hstep
    rw [← hrest, List.getElem?_append_right le_rfl, Nat.sub_self] at hstep'
    cases rest with
    | nil => simp at hstep'
    | cons s0 rest' =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hstep'
      subst hstep'
      unfold Record.guessShadow
      rw [← hrest, List.find?_append, List.find?_eq_none.mpr, Option.none_or,
        List.find?_cons_of_pos]
      · rfl
      · simpa using ht2
      · intro s hs
        simp only [decide_eq_true_eq, not_lt]
        exact le_trans (hord s hs).length_le ht1
  have hcons' := cons_step_proof pp r c x g gq σ hI hσ hx hcl hpre
  have hσ' := (mem_cons_iff pp _ _ c x σ).mp hσ
  have hsh : ShInv pp σ g.shadow :=
    ⟨fun s l P hP w hw => (hiff w).mp (hvars s l P hP w hw), hgd, hσ'.2⟩
  cases gq with
  | lin s a b u v =>
    have hO' : g.order ++ newGuesses pp g.shadow (realShadow pp σ g (.lin s a b u v))
        (.lin s a b u v) = g.order ++ ng2 g.shadow.guesses
          (resolve pp σ (resolve pp σ g.shadow s u).2 s v).2.guesses (s, u) (s, v) := by
      show g.order ++ ng2 _ (realShadow pp σ g (.lin s a b u v)).guesses _ _ = _
      rw [realShadow_guesses_lin]
    have hσ1 : σ ∈ cons pp (resolve pp σ g.shadow s u).2
        (g.order ++ newGuesses pp g.shadow (realShadow pp σ g (.lin s a b u v))
          (.lin s a b u v)) c x := by
      rw [hO']
      exact (two_facts pp r c x g _ s s u v hI (hO' ▸ hpre) σ hσ hx rfl).2.2.2.2.1
    have hRiff : (realResult pp σ g (.lin s a b u v) : Option (Label P0)).isSome ↔
        ((resolve pp σ g.shadow s u).1.isSome ∧
          (resolve pp σ (resolve pp σ g.shadow s u).2 s v).1.isSome) := by
      rw [resolve_isSome_iff pp σ g.shadow g.order c x s u hσ,
        resolve_isSome_iff pp σ _ _ c x s v hσ1]
      simp only [realResult, groupAnswer]
      cases Algebra.decodeLabel (σ s) u <;> cases Algebra.decodeLabel (σ s) v <;> simp
    exact count_two pp r c x g σ s s s u v (fun P Q => scalar pp a * P + scalar pp b * Q)
      (realResult pp σ g (.lin s a b u v)) (realShadow pp σ g (.lin s a b u v)) _ hI hσ hx hO'
      hpre hgs (by
        simp only [realShadow, observeGroup]
        rcases (resolve pp σ g.shadow s u).1 with _ | P <;>
          rcases (resolve pp σ (resolve pp σ g.shadow s u).2 s v).1 with _ | Q <;>
          rcases (realResult pp σ g (.lin s a b u v) : Option (Label P0)) with _ | l <;> rfl)
      hRiff hcl hcons'
  | pair u v =>
    have hnd2 : ∀ (G₀ G : Finset GuessVar),
        ([((.g₁ : GroupModel.Sorted.PSort), u), ((.g₂ : GroupModel.Sorted.PSort), v)].filter
          fun w => w ∈ G ∧ w ∉ G₀) = ng2 G₀ G (.g₁, u) (.g₂, v) := by
      intro G₀ G
      unfold ng2
      symm
      apply List.Nodup.dedup
      apply List.Nodup.filter
      simp
    have hO' : g.order ++ newGuesses pp g.shadow (realShadow pp σ g (.pair u v)) (.pair u v) =
        g.order ++ ng2 g.shadow.guesses
          (resolve pp σ (resolve pp σ g.shadow .g₁ u).2 .g₂ v).2.guesses (.g₁, u) (.g₂, v) := by
      show g.order ++ ([((.g₁ : GroupModel.Sorted.PSort), u),
        ((.g₂ : GroupModel.Sorted.PSort), v)].filter
          fun w => w ∈ (realShadow pp σ g (.pair u v)).guesses ∧ w ∉ g.shadow.guesses) = _
      rw [hnd2, realShadow_guesses_pair]
    have hσ1 : σ ∈ cons pp (resolve pp σ g.shadow .g₁ u).2
        (g.order ++ newGuesses pp g.shadow (realShadow pp σ g (.pair u v)) (.pair u v)) c x := by
      rw [hO']
      exact (two_facts pp r c x g _ .g₁ .g₂ u v hI (hO' ▸ hpre) σ hσ hx rfl).2.2.2.2.1
    have hRiff : (realResult pp σ g (.pair u v) : Option (Label P0)).isSome ↔
        ((resolve pp σ g.shadow .g₁ u).1.isSome ∧
          (resolve pp σ (resolve pp σ g.shadow .g₁ u).2 .g₂ v).1.isSome) := by
      rw [resolve_isSome_iff pp σ g.shadow g.order c x .g₁ u hσ,
        resolve_isSome_iff pp σ _ _ c x .g₂ v hσ1]
      simp only [realResult, groupAnswer]
      cases Algebra.decodeLabel (σ .g₁) u <;> cases Algebra.decodeLabel (σ .g₂) v <;> simp
    exact count_two pp r c x g σ .g₁ .g₂ .gₜ u v (fun P Q => P * Q)
      (realResult pp σ g (.pair u v)) (realShadow pp σ g (.pair u v)) _ hI hσ hx hO'
      hpre hgs (by
        simp only [realShadow, observeGroup]
        rcases (resolve pp σ g.shadow .g₁ u).1 with _ | P <;>
          rcases (resolve pp σ (resolve pp σ g.shadow .g₁ u).2 .g₂ v).1 with _ | Q <;>
          rcases (realResult pp σ g (.pair u v) : Option (Label P0)) with _ | l <;> rfl)
      hRiff hcl hcons'
  | name u =>
    have hng : newGuesses pp g.shadow (realShadow pp σ g (.name u)) (.name u) = [] := rfl
    show ((cons pp (realShadow pp σ g (.name u))
        (g.order ++ newGuesses pp g.shadow (realShadow pp σ g (.name u)) (.name u)) c x).card :
          ℝ≥0∞) * guessFactor pp r c x
          (g.order ++ newGuesses pp g.shadow (realShadow pp σ g (.name u)) (.name u)).length ≤ _
    rw [hng, List.append_nil] at hcons' ⊢
    apply mul_le_mul' _ le_rfl
    by_cases hu : u ∈ g.oracle.issuedT
    · obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (hcov u hu)
      have hu0 : σ .gₜ (valueAt pp g.order c x P) = u := hσ'.1 .gₜ u P hP
      have hdec : Algebra.decodeLabel (σ .gₜ) u = some (valueAt pp g.order c x P) :=
        (decodeLabel_eq_some_iff _ _ _).mpr hu0
      set x₀ := valueAt pp g.order c x P with hx₀
      have hR : realResult pp σ g (.name u) = some (labelName (σ .gₜ) x₀) := by
        simp [realResult, groupAnswer, hu, hdec]
      have hother : otherLabel u (labelName (σ .gₜ) x₀) = σ .gₜ (-x₀) := by
        rw [← hu0]
        exact otherLabel_name (σ .gₜ) x₀
      have hshn : realShadow pp σ g (.name u) =
          insertResult pp g.shadow .gₜ (σ .gₜ (-x₀)) (-P) := by
        simp only [realShadow, observeGroup, hR, hother, hP, Option.getD_some]
      have hgen : (referenceGroup pp g.oracle.issuedT (.name u)).run g.shadow =
          (fun z : Label P0 × State pp => ((some s(u, z.1) : Option (ClassName P0)), z.2)) <$>
            (referenceInsert pp .gₜ (-P)).run g.shadow := by
        simp [referenceGroup, hu, hP, StateT.run_bind, StateT.run_get, map_eq_bind_pure_comp]
      have hname : labelName (σ .gₜ) x₀ = s(u, σ .gₜ (-x₀)) := by
        simp [labelName, hu0]
      have hinj : Function.Injective
          (fun z : Label P0 × State pp => ((some s(u, z.1) : Option (ClassName P0)), z.2)) := by
        intro p q h
        simp only [Prod.mk.injEq, Option.some.injEq, Sym2.congr_right] at h
        exact Prod.ext h.1 h.2
      rw [hR, hgen, hname]
      rw [hshn] at hcons' hcl ⊢
      rw [show ((some s(u, σ .gₜ (-x₀)) : Option (ClassName P0)),
          insertResult pp g.shadow .gₜ (σ .gₜ (-x₀)) (-P)) =
        (fun z : Label P0 × State pp => ((some s(u, z.1) : Option (ClassName P0)), z.2))
          (σ .gₜ (-x₀), insertResult pp g.shadow .gₜ (σ .gₜ (-x₀)) (-P)) from rfl,
        probOutput_map_injective _ hinj]
      exact insert_count pp g.shadow g.order c x .gₜ (σ .gₜ (-x₀)) (-P) σ hσ hcons' hfirst hcl
    · have hR : realResult pp σ g (.name u) = none := by
        simp [realResult, groupAnswer, hu]
      have hshn : realShadow pp σ g (.name u) = g.shadow := by
        simp only [realShadow, observeGroup, hR]
      have hgen : (referenceGroup pp g.oracle.issuedT (.name u)).run g.shadow =
          pure (none, g.shadow) := by
        simp [referenceGroup, hu, StateT.run_pure]
      rw [hR, hshn, hgen, probOutput_pure_self, mul_one]

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation
