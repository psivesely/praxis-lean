import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
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

lemma valueAt_append (O Δ : List GuessVar) (c : CoinDomain pp) (x : ℕ → k) (P : Poly pp)
    (h : ∀ v ∈ P.vars, v ∈ O) : valueAt pp (O ++ Δ) c x P = valueAt pp O c x P := by
  unfold valueAt
  simp only [MvPolynomial.coe_eval₂Hom]
  apply MvPolynomial.eval₂_congr
  intro i d hi hd
  have hv : i ∈ P.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨d, MvPolynomial.mem_support_iff.mpr hd, hi⟩
  rw [List.idxOf_append_of_mem (h i hv)]

lemma cons_extend (st : State pp) (O Δ : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (h : ∀ s l P, st.dict s l = some P → ∀ v ∈ P.vars, v ∈ O) :
    cons pp st (O ++ Δ) c x = cons pp st O c x := by
  ext σ
  rw [mem_cons_iff, mem_cons_iff]
  constructor
  · rintro ⟨hd, he⟩
    refine ⟨fun s l P hP => ?_, he⟩
    rw [← valueAt_append pp O Δ c x P (h s l P hP)]
    exact hd s l P hP
  · rintro ⟨hd, he⟩
    refine ⟨fun s l P hP => ?_, he⟩
    rw [valueAt_append pp O Δ c x P (h s l P hP)]
    exact hd s l P hP

lemma valueAt_X (O : List GuessVar) (c : CoinDomain pp) (x : ℕ → k) (v : GuessVar) :
    valueAt pp O c x (MvPolynomial.X v) = x (O.idxOf v) := by
  simp [valueAt]

lemma dec_of_valid (r : Record pp) (σ : LabelEncoding P0) (x : ℕ → k)
    (hx : guessValuesσ pp r σ = x) (w : GuessVar) (hw : w ∈ r.order)
    (hv : (Algebra.decodeLabel (σ w.1) w.2).isSome) :
    σ w.1 (x (r.order.idxOf w)) = w.2 := by
  obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hv
  have hget : r.order[r.order.idxOf w]? = some w := List.getElem?_idxOf hw
  have h1 : x (r.order.idxOf w) = val := by
    rw [← hx]
    simp only [guessValuesσ, hget, hval, Option.getD_some]
  rw [h1]
  exact (decodeLabel_eq_some_iff _ _ _).mp hval

def exclState (st : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0) : State pp :=
  {st with excluded := Function.update st.excluded s (insert l (st.excluded s))}

lemma resolve_cons (st : State pp) (O : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp st O c x)
    (hnew : st.dict s l = none → (Algebra.decodeLabel (σ s) l).isSome →
      σ s (x (O.idxOf (s, l))) = l) :
    σ ∈ cons pp (resolve pp σ st s l).2 O c x := by
  cases hd : st.dict s l with
  | some P =>
    rw [resolve_known pp σ st s l P hd]
    exact hσ
  | none =>
    cases hdec : Algebra.decodeLabel (σ s) l with
    | none =>
      have hres : (resolve pp σ st s l).2 =
          {st with excluded := Function.update st.excluded s (insert l (st.excluded s))} := by
        simp [resolve, hd, hdec]
      rw [hres, cons_exclude, Finset.mem_filter]
      exact ⟨hσ, (decode_none_iff _ _).mp hdec⟩
    | some w =>
      have hres : (resolve pp σ st s l).2 = guessState pp st s l := by
        unfold resolve guessState; simp [hd, hdec]
      have hcg : cons pp (guessState pp st s l) O c x = (cons pp st O c x).filter fun σ =>
          σ s (valueAt pp O c x (MvPolynomial.X (s, l))) = l := by
        unfold guessState
        exact cons_record pp st O c x s l _ _ hd
      rw [hres, hcg, Finset.mem_filter, valueAt_X]
      exact ⟨hσ, hnew hd (by rw [hdec]; rfl)⟩

lemma resolve_guesses (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) :
    (resolve pp σ st s l).2.guesses = if st.dict s l = none ∧ (Algebra.decodeLabel (σ s) l).isSome
      then insert (s, l) st.guesses else st.guesses := by
  cases hd : st.dict s l with
  | some P =>
    rw [resolve_known pp σ st s l P hd]
    simp
  | none =>
    cases hdec : Algebra.decodeLabel (σ s) l with
    | none => simp [resolve, hd, hdec]
    | some val => simp [resolve, hd, hdec]

lemma resolve_dict (σ : LabelEncoding P0) (st : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (s' : GroupModel.Sorted.PSort) (l' : Label P0) (P : Poly pp)
    (h : (resolve pp σ st s l).2.dict s' l' = some P) :
    st.dict s' l' = some P ∨ ((s', l') = (s, l) ∧ P = MvPolynomial.X (s, l) ∧
      st.dict s l = none ∧ (Algebra.decodeLabel (σ s) l).isSome) := by
  cases hd : st.dict s l with
  | some Q =>
    rw [resolve_known pp σ st s l Q hd] at h
    exact Or.inl h
  | none =>
    cases hdec : Algebra.decodeLabel (σ s) l with
    | none =>
      have hres : (resolve pp σ st s l).2 =
          {st with excluded := Function.update st.excluded s (insert l (st.excluded s))} := by
        simp [resolve, hd, hdec]
      rw [hres] at h
      exact Or.inl h
    | some val =>
      have hres : (resolve pp σ st s l).2 = guessState pp st s l := by
        unfold resolve guessState; simp [hd, hdec]
      rw [hres] at h
      simp only [guessState, record] at h
      by_cases hs : s' = s
      · subst hs
        rw [Function.update_self] at h
        by_cases hl : l' = l
        · subst hl
          rw [Function.update_self] at h
          cases h
          exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
        · rw [Function.update_of_ne hl] at h
          exact Or.inl h
      · rw [Function.update_of_ne hs] at h
        exact Or.inl h

lemma atomic_resolve (st : State pp) (O : List GuessVar) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp st O c x) (hσ' : σ ∈ cons pp (resolve pp σ st s l).2 O c x) :
    ((cons pp (resolve pp σ st s l).2 O c x).card : ℝ≥0∞) ≤
      (cons pp st O c x).card * Pr[= resolve pp σ st s l | (referenceResolve pp s l).run st] *
        (if st.dict s l = none ∧ (Algebra.decodeLabel (σ s) l).isSome then
          ((Fintype.card k - (assigned pp st s).card : ℕ) : ℝ≥0∞)⁻¹ else 1) := by
  cases hd : st.dict s l with
  | some P =>
    rw [resolve_known pp σ st s l P hd, refResolve_known pp st s l P hd]
    simp
  | none =>
    by_cases hex : l ∈ st.excluded s
    · have hdec : Algebra.decodeLabel (σ s) l = none := by
        rw [decode_none_iff]
        exact ((mem_cons_iff pp st O c x σ).mp hσ).2 s l hex
      have hst : ({st with excluded := Function.update st.excluded s (insert l (st.excluded s))} :
          State pp) = st := by
        rw [Finset.insert_eq_of_mem hex, Function.update_eq_self]
      have hres : resolve pp σ st s l = (none, st) := by
        have h0 : resolve pp σ st s l =
            (none, {st with excluded := Function.update st.excluded s (insert l (st.excluded s))}) := by
          simp [resolve, hd, hdec]
        rw [h0, hst]
      rw [hres, refResolve_excluded pp st s l hd hex, probOutput_pure_self]
      simp only [hdec, Option.isSome_none, Bool.false_eq_true, and_false, if_false, mul_one,
        le_refl]
    · cases hdec : Algebra.decodeLabel (σ s) l with
      | some w =>
        have h := resolve_valid_count pp O c x σ st s l w hd hex hdec hσ'
        refine h.trans (le_of_eq ?_)
        rw [if_pos ⟨rfl, rfl⟩]
      | none =>
        have hl : l ∈ available pp st s := mem_available pp st s l hd hex
        have hres : resolve pp σ st s l = (none, exclState pp st s l) := by
          unfold resolve exclState; simp [hd, hdec]
        rw [hres]
        simp only [Option.isSome_none, Bool.false_eq_true, and_false, if_false, mul_one]
        rw [show cons pp (exclState pp st s l) O c x =
          (cons pp st O c x).filter fun σ => ∀ v, σ s v ≠ l from by
            unfold exclState; exact cons_exclude pp st O c x s l]
        have hcount := card_exclude pp st O c x s l hl σ hσ
        have hA := card_available pp st O c x s σ hσ
        have hV := card_values pp st O c x s σ hσ
        have hUA := unassigned_le_available pp st O c x s σ hσ
        set a := (assigned pp st s).card
        set e := (st.excluded s).card
        set N := 2 ^ P0.labelBits
        rw [hV] at hcount hUA
        have hav : (available pp st s).card ≥ 1 := Finset.card_pos.mpr ⟨l, hl⟩
        rw [ZMod.card] at hcount hUA
        have hprob : Pr[= (none, exclState pp st s l) | (referenceResolve pp s l).run st] =
            ((N - a - e - 1 + 1 - (P0.q - a) : ℕ) : ℝ≥0∞) / ((N - a - e - 1 + 1 : ℕ) : ℝ≥0∞) := by
          rw [refResolve_fresh pp st s l hd hex, ← probEvent_eq_eq_probOutput, probEvent_map]
          have hg : genericResolve pp st s l false = (none, exclState pp st s l) := by
            unfold genericResolve exclState; simp [hd]
          rw [← hg]
          have := uniformFin_ge_prob (N - a - e - 1) (P0.q - a) (by omega)
          rw [← this]
          apply probEvent_congr' _ rfl
          intro u _
          constructor
          · intro h
            have := genericResolve_inj pp st s l hd _ _ h
            simpa using this
          · intro h
            show genericResolve pp st s l (decide (u.val < P0.q - a)) =
              genericResolve pp st s l false
            rw [decide_eq_false h]
        rw [hprob]
        have hN : N - a - e - 1 + 1 = (available pp st s).card := by omega
        rw [hN]
        set A := (available pp st s).card
        set C := (cons pp st O c x).card
        set F := ((cons pp st O c x).filter fun σ => ∀ v, σ s v ≠ l).card
        have hA0 : (A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
        rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hA0)
          (Or.inl (ENNReal.natCast_ne_top _))]
        exact_mod_cast hcount.le

def poolFactor (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (t : ℕ) : ℝ≥0∞ :=
  if x t ∈ guessPool pp r c t x then ((guessPool pp r c t x).card : ℝ≥0∞)⁻¹ else 0

lemma guessFactor_succ (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (m : ℕ)
    (hm : m < r.order.length) :
    guessFactor pp r c x m = poolFactor pp r c x m * guessFactor pp r c x (m + 1) := by
  unfold guessFactor poolFactor
  rw [Finset.prod_eq_prod_Ico_succ_bot hm]

lemma atomic_step (r : Record pp) (st₁ : State pp) (L : List GuessVar) (c : CoinDomain pp)
    (x : ℕ → k) (s₁ : GroupModel.Sorted.PSort) (l₁ : Label P0) (σ : LabelEncoding P0) (m : ℕ)
    (hσ : σ ∈ cons pp st₁ L c x) (hσ' : σ ∈ cons pp (resolve pp σ st₁ s₁ l₁).2 L c x)
    (hpool : st₁.dict s₁ l₁ = none → (Algebra.decodeLabel (σ s₁) l₁).isSome →
      m < r.order.length ∧
        ((Fintype.card k - (assigned pp st₁ s₁).card : ℕ) : ℝ≥0∞)⁻¹ ≤ poolFactor pp r c x m) :
    ((cons pp (resolve pp σ st₁ s₁ l₁).2 L c x).card : ℝ≥0∞) *
        guessFactor pp r c x (if st₁.dict s₁ l₁ = none ∧ (Algebra.decodeLabel (σ s₁) l₁).isSome
          then m + 1 else m) ≤
      (cons pp st₁ L c x).card *
        Pr[= resolve pp σ st₁ s₁ l₁ | (referenceResolve pp s₁ l₁).run st₁] *
        guessFactor pp r c x m := by
  have h := atomic_resolve pp st₁ L c x s₁ l₁ σ hσ hσ'
  by_cases hfv : st₁.dict s₁ l₁ = none ∧ (Algebra.decodeLabel (σ s₁) l₁).isSome
  · rw [if_pos hfv] at h ⊢
    obtain ⟨hm, hK⟩ := hpool hfv.1 hfv.2
    rw [guessFactor_succ pp r c x m hm]
    calc _ ≤ (cons pp st₁ L c x).card *
          Pr[= resolve pp σ st₁ s₁ l₁ | (referenceResolve pp s₁ l₁).run st₁] *
          ((Fintype.card k - (assigned pp st₁ s₁).card : ℕ) : ℝ≥0∞)⁻¹ *
          guessFactor pp r c x (m + 1) := mul_le_mul' h le_rfl
      _ ≤ (cons pp st₁ L c x).card *
          Pr[= resolve pp σ st₁ s₁ l₁ | (referenceResolve pp s₁ l₁).run st₁] *
          poolFactor pp r c x m * guessFactor pp r c x (m + 1) :=
          mul_le_mul' (mul_le_mul' le_rfl hK) le_rfl
      _ = _ := by ring
  · rw [if_neg hfv] at h ⊢
    rw [mul_one] at h
    exact mul_le_mul' h le_rfl

lemma idxOf_of_getElem? {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (L : List α), L.Nodup → ∀ (t : ℕ) (v : α), L[t]? = some v → L.idxOf v = t
  | [], _, t, v, h => by simp at h
  | a :: L, _, 0, v, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
  | a :: L, hL, t + 1, v, h => by
      simp only [List.getElem?_cons_succ] at h
      have hv : v ∈ L := List.mem_of_getElem? h
      have hne : a ≠ v := fun hav => (List.nodup_cons.mp hL).1 (hav ▸ hv)
      rw [List.idxOf_cons_ne L hne, idxOf_of_getElem? L (List.nodup_cons.mp hL).2 t v h]

lemma pool_factor (r : Record pp) (st : State pp) (O L : List GuessVar) (c : CoinDomain pp)
    (x : ℕ → k) (σ : LabelEncoding P0) (t : ℕ) (st₁ : State pp) (v : GuessVar)
    (hshadow : r.shadow = st) (horder : r.order = L)
    (hsteps : ∀ s ∈ r.steps, s.order.length ≤ O.length)
    (hOt : O.length ≤ t) (ht : L[t]? = some v) (hnodup : L.Nodup)
    (hfresh : st.dict v.1 v.2 = none)
    (hdecL : ∀ w ∈ L, σ w.1 (x (L.idxOf w)) = w.2)
    (hstcons : ∀ s l P, st.dict s l = some P →
      σ s (valueAt pp L c x P) = l ∧ ∀ w ∈ P.vars, L.idxOf w < O.length)
    (hst₁ : ∀ s l P, st₁.dict s l = some P → st.dict s l = some P ∨
      (P = MvPolynomial.X (s, l) ∧ st.dict s l = none ∧ (s, l) ∈ L ∧ L.idxOf (s, l) < t))
    (hσ₁ : σ ∈ cons pp st₁ L c x) :
    ((Fintype.card k - (assigned pp st₁ v.1).card : ℕ) : ℝ≥0∞)⁻¹ ≤ poolFactor pp r c x t := by
  haveI : Nontrivial (Coeff pp) := (atCoin pp c).domain_nontrivial
  have hgs : r.guessShadow t = r.pendingShadow := by
    unfold Record.guessShadow
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro s hs
      have := hsteps s hs
      simp only [decide_eq_true_eq, not_lt]
      omega
  have hsort : r.sortAt t = v.1 := by
    unfold Record.sortAt
    rw [horder, ht]
    rfl
  have hidx : L.idxOf v = t := idxOf_of_getElem? L hnodup t v ht
  have hvL : v ∈ L := List.mem_of_getElem? ht
  have hpd : ∀ s l, r.pendingShadow.dict s l = (match st.dict s l with
      | some P => some P
      | none => if (s, l) ∈ L then some (MvPolynomial.X (s, l)) else none) := by
    intro s l
    unfold Record.pendingShadow
    rw [hshadow, horder]
    rfl
  have hsub : valuesOf pp st₁ L c x v.1 ⊆ usedBefore pp r c t x := by
    intro a ha
    simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨l, P, hP, rfl⟩ := ha
    simp only [usedBefore, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hgs, hsort, horder]
    rcases hst₁ v.1 l P hP with h1 | ⟨rfl, h2, h3, h4⟩
    · refine ⟨l, P, ?_, fun w hw => ?_, rfl⟩
      · rw [hpd, h1]
      · exact lt_of_lt_of_le ((hstcons v.1 l P h1).2 w hw) hOt
    · refine ⟨l, MvPolynomial.X (v.1, l), ?_, fun w hw => ?_, rfl⟩
      · rw [hpd, h2]
        simp [h3]
      · rw [mem_vars_X hw]
        exact h4
  have hxt : σ v.1 (x t) = v.2 := by
    rw [← hidx]
    exact hdecL v hvL
  have hnot : x t ∉ usedBefore pp r c t x := by
    intro hx
    simp only [usedBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hgs, hsort, horder] at hx
    obtain ⟨l, P, hP, hvars, hval⟩ := hx
    rw [hpd] at hP
    cases h1 : st.dict v.1 l with
    | some Q =>
      rw [h1] at hP
      have hQP : Q = P := Option.some.inj hP
      subst hQP
      have h2 := (hstcons v.1 l Q h1).1
      rw [hval, hxt] at h2
      rw [← h2, hfresh] at h1
      cases h1
    | none =>
      rw [h1] at hP
      split_ifs at hP with hm
      cases hP
      rw [valueAt_X] at hval
      have hlt : L.idxOf (v.1, l) < t :=
        hvars (v.1, l) (by rw [MvPolynomial.vars_X]; exact Finset.mem_singleton_self _)
      have h2 := hdecL (v.1, l) hm
      dsimp only at h2
      rw [hval, hxt] at h2
      have hv : (v.1, l) = v := by
        rw [← h2]
      rw [hv, hidx] at hlt
      exact lt_irrefl _ hlt
  have hmem : x t ∈ Finset.univ \ usedBefore pp r c t x :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
  have hpool : guessPool pp r c t x = Finset.univ \ usedBefore pp r c t x := by
    unfold guessPool
    rw [if_pos ⟨x t, hmem⟩]
  unfold poolFactor
  rw [if_pos (by rw [hpool]; exact hmem)]
  apply ENNReal.inv_le_inv.mpr
  have hV := card_values pp st₁ L c x v.1 σ hσ₁
  have hcardU := Finset.card_le_card hsub
  rw [hV] at hcardU
  rw [hpool, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  exact_mod_cast (by omega :
    Fintype.card k - (usedBefore pp r c t x).card ≤ Fintype.card k - (assigned pp st₁ v.1).card)

def ng2 (G₀ G : Finset GuessVar) (a b : GuessVar) : List GuessVar :=
  ([a, b].filter fun w => w ∈ G ∧ w ∉ G₀).dedup

lemma ng2_cases (G₀ : Finset GuessVar) (a b : GuessVar) (fa fb : Prop) [Decidable fa]
    [Decidable fb] (ha : fa → a ∉ G₀) (hb : fb → b ∉ (if fa then insert a G₀ else G₀)) :
    ng2 G₀ (if fb then insert b (if fa then insert a G₀ else G₀)
        else (if fa then insert a G₀ else G₀)) a b =
      (if fa then [a] else []) ++ (if fb then [b] else []) := by
  unfold ng2
  by_cases hfa : fa <;> by_cases hfb : fb
  · have ha' := ha hfa
    have hb' := hb hfb
    simp only [hfa, hfb, if_true] at hb' ⊢
    rw [Finset.mem_insert, not_or] at hb'
    have hba : b ≠ a := hb'.1
    have hf : [a, b].filter (fun w => decide (w ∈ insert b (insert a G₀) ∧ w ∉ G₀)) = [a, b] := by
      simp [List.filter, ha', hb'.2]
    rw [hf, List.dedup_cons_of_notMem (by simpa using hba.symm)]
    simp
  · have ha' := ha hfa
    simp only [hfa, hfb, if_true, if_false, List.append_nil]
    by_cases hab : b = a
    · subst hab
      simp [List.filter, ha']
    · by_cases hb0 : b ∈ G₀
      · simp [List.filter, ha', hb0]
      · simp [List.filter, ha', hb0, hab]
  · have hb' := hb hfb
    simp only [hfa, hfb, if_true, if_false, List.nil_append] at hb' ⊢
    by_cases hab : a = b
    · subst hab
      simp [List.filter, hb']
    · by_cases ha0 : a ∈ G₀
      · simp [List.filter, ha0, hb']
      · simp [List.filter, ha0, hab, hb']
  · simp only [hfa, hfb, if_false, List.nil_append]
    simp [List.filter]

lemma ng2_resolve (σ : LabelEncoding P0) (st : State pp) (s₁ s₂ : GroupModel.Sorted.PSort)
    (u v : Label P0) (hsh : ShInv pp σ st) :
    ng2 st.guesses (resolve pp σ (resolve pp σ st s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v) =
      (if st.dict s₁ u = none ∧ (Algebra.decodeLabel (σ s₁) u).isSome then [(s₁, u)] else []) ++
      (if (resolve pp σ st s₁ u).2.dict s₂ v = none ∧ (Algebra.decodeLabel (σ s₂) v).isSome
        then [(s₂, v)] else []) := by
  have hsh1 := (resolve_shInv pp σ st s₁ u hsh).1
  rw [resolve_guesses pp σ _ s₂ v]
  have hg1 := resolve_guesses pp σ st s₁ u
  rw [hg1]
  apply ng2_cases
  · intro hfa hm
    have := hsh.2.1 _ hm
    rw [hfa.1] at this
    cases this
  · intro hfb hm
    rw [← hg1] at hm
    have := hsh1.2.1 _ hm
    rw [hfb.1] at this
    cases this

lemma two_facts (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (g : GenState pp)
    (L : List GuessVar) (s₁ s₂ : GroupModel.Sorted.PSort) (u v : Label P0)
    (hI : Inv pp g) (horder : L <+: r.order) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp g.shadow g.order c x) (hx : guessValuesσ pp r σ = x)
    (hE : g.order ++ ng2 g.shadow.guesses
      (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v) = L) :
    L = g.order ++ ((if g.shadow.dict s₁ u = none ∧ (Algebra.decodeLabel (σ s₁) u).isSome
        then [(s₁, u)] else []) ++
      (if (resolve pp σ g.shadow s₁ u).2.dict s₂ v = none ∧ (Algebra.decodeLabel (σ s₂) v).isSome
        then [(s₂, v)] else [])) ∧
    L.Nodup ∧
    (∀ w ∈ L, σ w.1 (x (L.idxOf w)) = w.2) ∧
    σ ∈ cons pp g.shadow L c x ∧
    σ ∈ cons pp (resolve pp σ g.shadow s₁ u).2 L c x ∧
    σ ∈ cons pp (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2 L c x := by
  obtain ⟨_, _, _, hvars, hnd, hiff, hgd⟩ := hI
  have hσ' := (mem_cons_iff pp _ _ c x σ).mp hσ
  have hsh : ShInv pp σ g.shadow :=
    ⟨fun s l P hP w hw => (hiff w).mp (hvars s l P hP w hw), hgd, hσ'.2⟩

  have hngnd : (ng2 g.shadow.guesses
      (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v)).Nodup :=
    List.nodup_dedup _
  have hngout : ∀ w ∈ ng2 g.shadow.guesses
      (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v),
      w ∉ g.order := by
    intro w hw hwO
    unfold ng2 at hw
    rw [List.mem_dedup, List.mem_filter] at hw
    have h2 := hw.2
    simp only [decide_eq_true_eq] at h2
    exact h2.2 ((hiff w).mp hwO)
  have hnodup : L.Nodup := by
    rw [← hE]
    exact List.nodup_append.mpr ⟨hnd, hngnd, fun a ha b hb hab => hngout b hb (hab ▸ ha)⟩
  have hng := ng2_resolve pp σ g.shadow s₁ s₂ u v hsh
  rw [hng] at hE
  have hL := hE.symm

  have hvalid : ∀ w ∈ L, (Algebra.decodeLabel (σ w.1) w.2).isSome := by
    intro w hw
    rw [hL] at hw
    rcases List.mem_append.mp hw with hw | hw
    · have h1 := hσ'.1 w.1 w.2 _ (hgd w ((hiff w).mp hw))
      rw [(decodeLabel_eq_some_iff _ _ _).mpr h1]
      rfl
    · rcases List.mem_append.mp hw with hw | hw
      · split_ifs at hw with hfa
        · rw [List.mem_singleton.mp hw]
          exact hfa.2
        · cases hw
      · split_ifs at hw with hfb
        · rw [List.mem_singleton.mp hw]
          exact hfb.2
        · cases hw
  have hdecL : ∀ w ∈ L, σ w.1 (x (L.idxOf w)) = w.2 := by
    intro w hw
    have h := dec_of_valid pp r σ x hx w (horder.subset hw) (hvalid w hw)
    obtain ⟨rest, hrest⟩ := horder
    rwa [← hrest, List.idxOf_append_of_mem hw] at h
  have hσL : σ ∈ cons pp g.shadow L c x := by
    rw [hL, cons_extend pp g.shadow g.order _ c x hvars]
    exact hσ
  have hmem1 : g.shadow.dict s₁ u = none → (Algebra.decodeLabel (σ s₁) u).isSome → (s₁, u) ∈ L := by
    intro h1 h2
    rw [hL]
    exact List.mem_append_right _ (List.mem_append_left _ (by rw [if_pos ⟨h1, h2⟩]; simp))
  have hσ1 : σ ∈ cons pp (resolve pp σ g.shadow s₁ u).2 L c x :=
    resolve_cons pp g.shadow L c x s₁ u σ hσL
      (fun h1 h2 => hdecL (s₁, u) (hmem1 h1 h2))
  have hmem2 : (resolve pp σ g.shadow s₁ u).2.dict s₂ v = none →
      (Algebra.decodeLabel (σ s₂) v).isSome → (s₂, v) ∈ L := by
    intro h1 h2
    rw [hL]
    exact List.mem_append_right _ (List.mem_append_right _ (by rw [if_pos ⟨h1, h2⟩]; simp))
  have hσ2 : σ ∈ cons pp (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2 L c x :=
    resolve_cons pp _ L c x s₂ v σ hσ1 (fun h1 h2 => hdecL (s₂, v) (hmem2 h1 h2))
  exact ⟨hL, hnodup, hdecL, hσL, hσ1, hσ2⟩

lemma two_chain (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (g : GenState pp)
    (L : List GuessVar) (s₁ s₂ : GroupModel.Sorted.PSort) (u v : Label P0)
    (hI : Inv pp g) (hsteps : r.steps = g.steps) (hsh : r.shadow = g.shadow)
    (horder : r.order = L) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp g.shadow g.order c x) (hx : guessValuesσ pp r σ = x)
    (hE : g.order ++ ng2 g.shadow.guesses
      (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v) = L) :
    ((cons pp (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2 L c x).card : ℝ≥0∞) ≤
      (cons pp g.shadow g.order c x).card *
        (Pr[= resolve pp σ g.shadow s₁ u | (referenceResolve pp s₁ u).run g.shadow] *
          Pr[= resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v |
            (referenceResolve pp s₂ v).run (resolve pp σ g.shadow s₁ u).2]) *
        guessFactor pp r c x g.order.length := by
  obtain ⟨hL, hnodup, hdecL, hσL, hσ1, hσ2⟩ :=
    two_facts pp r c x g L s₁ s₂ u v hI (horder ▸ List.prefix_refl _) σ hσ hx hE
  have hI' := hI
  obtain ⟨_, hord, _, hvars, _, hiff, hgd⟩ := hI'
  set st := g.shadow with hst
  set O := g.order with hO
  set ρ₁ := resolve pp σ st s₁ u with hρ₁
  set ρ₂ := resolve pp σ ρ₁.2 s₂ v with hρ₂
  have hsteps' : ∀ s ∈ r.steps, s.order.length ≤ O.length := by
    intro s hs
    rw [hsteps] at hs
    exact (hord s hs).length_le
  have hσ' := (mem_cons_iff pp _ _ c x σ).mp hσL
  have hstcons : ∀ s l P, st.dict s l = some P →
      σ s (valueAt pp L c x P) = l ∧ ∀ w ∈ P.vars, L.idxOf w < O.length := by
    intro s l P hP
    refine ⟨hσ'.1 s l P hP, fun w hw => ?_⟩
    have hwO : w ∈ O := hvars s l P hP w hw
    rw [hL, List.idxOf_append_of_mem hwO]
    exact List.idxOf_lt_length_of_mem hwO

  set m₁ := if st.dict s₁ u = none ∧ (Algebra.decodeLabel (σ s₁) u).isSome
    then O.length + 1 else O.length with hm₁
  have step1 := atomic_step pp r st L c x s₁ u σ O.length hσL hσ1 (by
    intro h1 h2
    have hfa : st.dict s₁ u = none ∧ (Algebra.decodeLabel (σ s₁) u).isSome := ⟨h1, h2⟩
    have ht : L[O.length]? = some (s₁, u) := by
      rw [hL, List.getElem?_append_right le_rfl, Nat.sub_self, if_pos hfa]
      rfl
    refine ⟨?_, ?_⟩
    · rw [horder]
      exact (List.getElem?_eq_some_iff.mp ht).1
    · exact pool_factor pp r st O L c x σ O.length st (s₁, u) hsh horder hsteps' le_rfl ht
        hnodup h1 hdecL hstcons (fun s l P hP => Or.inl hP) hσL)
  have step2 := atomic_step pp r ρ₁.2 L c x s₂ v σ m₁ hσ1 hσ2 (by
    intro h1 h2
    have hfb : ρ₁.2.dict s₂ v = none ∧ (Algebra.decodeLabel (σ s₂) v).isSome := ⟨h1, h2⟩
    have ht : L[m₁]? = some (s₂, v) := by
      rw [hL, hm₁]
      split_ifs with hfa
      · rw [List.getElem?_append_right (by omega)]
        simp
      · rw [List.getElem?_append_right le_rfl, Nat.sub_self]
        simp
    refine ⟨?_, ?_⟩
    · rw [horder]
      exact (List.getElem?_eq_some_iff.mp ht).1
    · have hfresh : st.dict s₂ v = none := by
        cases hd : st.dict s₂ v with
        | none => rfl
        | some P =>
          have := (resolve_props pp σ st s₁ u).2.2.2.1 s₂ v P hd
          rw [h1] at this
          cases this
      have hm1O : O.length ≤ m₁ := by rw [hm₁]; split_ifs <;> omega
      refine pool_factor pp r st O L c x σ m₁ ρ₁.2 (s₂, v) hsh horder hsteps' hm1O ht
        hnodup hfresh hdecL hstcons ?_ hσ1
      intro s l P hP
      rcases resolve_dict pp σ st s₁ u s l P hP with h | ⟨hsl, hPX, hd1, hv1⟩
      · exact Or.inl h
      · right
        have hsl' : s = s₁ ∧ l = u := Prod.mk.inj hsl
        obtain ⟨rfl, rfl⟩ := hsl'
        have hfa : st.dict s l = none ∧ (Algebra.decodeLabel (σ s) l).isSome := ⟨hd1, hv1⟩
        have ht1 : L[O.length]? = some (s, l) := by
          rw [hL, List.getElem?_append_right le_rfl, Nat.sub_self, if_pos hfa]
          rfl
        refine ⟨hPX, hd1, List.mem_of_getElem? ht1, ?_⟩
        rw [idxOf_of_getElem? L hnodup O.length (s, l) ht1, hm₁, if_pos hfa]
        omega)

  have hm₂ : r.order.length ≤ (if ρ₁.2.dict s₂ v = none ∧ (Algebra.decodeLabel (σ s₂) v).isSome
      then m₁ + 1 else m₁) := by
    rw [horder, hL, hm₁]
    split_ifs <;> simp
  rw [guessFactor_of_le pp r c x _ hm₂, mul_one] at step2
  have hCL : cons pp st L c x = cons pp st O c x := by
    rw [hL]
    exact cons_extend pp st O _ c x hvars
  rw [hCL] at step1
  calc ((cons pp ρ₂.2 L c x).card : ℝ≥0∞)
      ≤ (cons pp ρ₁.2 L c x).card * Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
          guessFactor pp r c x m₁ := step2
    _ = Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
          ((cons pp ρ₁.2 L c x).card * guessFactor pp r c x m₁) := by ring
    _ ≤ Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
          ((cons pp st O c x).card * Pr[= ρ₁ | (referenceResolve pp s₁ u).run st] *
            guessFactor pp r c x O.length) := mul_le_mul' le_rfl step1
    _ = _ := by ring

theorem pending_core (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (g : GenState pp)
    (L : List GuessVar) (s₁ s₂ : GroupModel.Sorted.PSort) (u v : Label P0)
    (hI : Inv pp g) (hsteps : r.steps = g.steps) (hsh : r.shadow = g.shadow)
    (horder : r.order = L) (W : Finset (LabelEncoding P0))
    (hW : ∀ σ ∈ W, σ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r σ = x) :
    ((W.filter fun σ => g.order ++ ng2 g.shadow.guesses
        (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v) = L).card :
        ℝ≥0∞) ≤
      (cons pp g.shadow g.order c x).card *
        (∑' ρ₁ : Option (Poly pp) × State pp, Pr[= ρ₁ | (referenceResolve pp s₁ u).run g.shadow] *
          ∑' ρ₂ : Option (Poly pp) × State pp, Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
            (if g.order ++ ng2 g.shadow.guesses ρ₂.2.guesses (s₁, u) (s₂, v) = L then 1 else 0)) *
        guessFactor pp r c x g.order.length := by
  haveI hdeq : DecidableEq ((Option (Poly pp) × State pp) × (Option (Poly pp) × State pp)) :=
    Classical.decEq _
  let key : LabelEncoding P0 → (Option (Poly pp) × State pp) × (Option (Poly pp) × State pp) :=
    fun σ => (resolve pp σ g.shadow s₁ u, resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v)
  let F : (Option (Poly pp) × State pp) × (Option (Poly pp) × State pp) → ℝ≥0∞ := fun kk =>
    Pr[= kk.1 | (referenceResolve pp s₁ u).run g.shadow] *
      (Pr[= kk.2 | (referenceResolve pp s₂ v).run kk.1.2] *
        (if g.order ++ ng2 g.shadow.guesses kk.2.2.guesses (s₁, u) (s₂, v) = L then 1 else 0))
  set W' := W.filter fun σ => g.order ++ ng2 g.shadow.guesses
    (resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v).2.guesses (s₁, u) (s₂, v) = L with hW'
  have hfib : ∀ kk ∈ W'.image key, ((W'.filter fun σ => key σ = kk).card : ℝ≥0∞) ≤
      (cons pp g.shadow g.order c x).card * F kk * guessFactor pp r c x g.order.length := by
    intro kk hkk
    obtain ⟨σ₀, hσ₀, rfl⟩ := Finset.mem_image.mp hkk
    obtain ⟨hσ₀W, hE₀⟩ := Finset.mem_filter.mp hσ₀
    obtain ⟨hc₀, hx₀⟩ := hW σ₀ hσ₀W
    have hsub : (W'.filter fun σ => key σ = key σ₀) ⊆
        cons pp (resolve pp σ₀ (resolve pp σ₀ g.shadow s₁ u).2 s₂ v).2 L c x := by
      intro σ hσ
      obtain ⟨hσW', hk⟩ := Finset.mem_filter.mp hσ
      obtain ⟨hσW, hE⟩ := Finset.mem_filter.mp hσW'
      obtain ⟨hc, hx⟩ := hW σ hσW
      have h := (two_facts pp r c x g L s₁ s₂ u v hI (horder ▸ List.prefix_refl _) σ hc hx
        hE).2.2.2.2.2
      have hk2 : resolve pp σ (resolve pp σ g.shadow s₁ u).2 s₂ v =
          resolve pp σ₀ (resolve pp σ₀ g.shadow s₁ u).2 s₂ v := congrArg Prod.snd hk
      rw [hk2] at h
      exact h
    have hchain := two_chain pp r c x g L s₁ s₂ u v hI hsteps hsh horder σ₀ hc₀ hx₀ hE₀
    have hF : F (key σ₀) = Pr[= resolve pp σ₀ g.shadow s₁ u | (referenceResolve pp s₁ u).run g.shadow] *
        Pr[= resolve pp σ₀ (resolve pp σ₀ g.shadow s₁ u).2 s₂ v |
          (referenceResolve pp s₂ v).run (resolve pp σ₀ g.shadow s₁ u).2] := by
      simp only [F, key]
      rw [if_pos hE₀, mul_one]
    rw [hF]
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hchain
  calc ((W'.card : ℕ) : ℝ≥0∞)
      = ∑ kk ∈ W'.image key, ((W'.filter fun σ => key σ = kk).card : ℝ≥0∞) := by
        rw [Finset.card_eq_sum_card_image key W', Nat.cast_sum]
    _ ≤ ∑ kk ∈ W'.image key, (cons pp g.shadow g.order c x).card * F kk *
          guessFactor pp r c x g.order.length := Finset.sum_le_sum hfib
    _ = (cons pp g.shadow g.order c x).card * (∑ kk ∈ W'.image key, F kk) *
          guessFactor pp r c x g.order.length := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (cons pp g.shadow g.order c x).card * (∑' kk, F kk) *
          guessFactor pp r c x g.order.length := by
        gcongr
        exact ENNReal.sum_le_tsum _
    _ = (cons pp g.shadow g.order c x).card *
          (∑' ρ₁ : Option (Poly pp) × State pp, ∑' ρ₂ : Option (Poly pp) × State pp, F (ρ₁, ρ₂)) *
          guessFactor pp r c x g.order.length := by
        rw [← ENNReal.tsum_prod]
    _ = _ := by
        congr 2
        apply tsum_congr
        intro ρ₁
        simp only [F]
        rw [ENNReal.tsum_mul_left]

lemma realShadow_guesses_lin (σ : LabelEncoding P0) (g : GenState pp)
    (s : GroupModel.Sorted.PSort) (a b : k) (u v : Label P0) :
    (realShadow pp σ g (.lin s a b u v)).guesses =
      (resolve pp σ (resolve pp σ g.shadow s u).2 s v).2.guesses := by
  simp only [realShadow, observeGroup]
  split
  · exact insertResult_guesses pp _ _ _ _
  · rfl

lemma realShadow_guesses_pair (σ : LabelEncoding P0) (g : GenState pp) (u v : Label P0) :
    (realShadow pp σ g (.pair u v)).guesses =
      (resolve pp σ (resolve pp σ g.shadow .g₁ u).2 .g₂ v).2.guesses := by
  simp only [realShadow, observeGroup]
  split
  · exact insertResult_guesses pp _ _ _ _
  · rfl

lemma refInsert_guesses (s : GroupModel.Sorted.PSort) (P : Poly pp) (st : State pp) :
    ∀ z ∈ support ((referenceInsert pp s P).run st), z.2.guesses = st.guesses := by
  intro z hz
  unfold referenceInsert at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_set,
      StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨l, _, hz⟩ := hz
    rw [hz]

lemma probEvent_guesses {β : Type} (m : ProbComp (β × State pp)) (G : Finset GuessVar)
    (φ : Finset GuessVar → Prop) [DecidablePred φ] (h : ∀ z ∈ support m, z.2.guesses = G) :
    Pr[fun z => φ z.2.guesses | m] = if φ G then 1 else 0 := by
  split_ifs with hφ
  · rw [probEvent_eq_one_iff]
    exact ⟨probFailure_eq_zero, fun z hz => by rw [h z hz]; exact hφ⟩
  · rw [probEvent_eq_zero_iff]
    intro z hz hz'
    rw [h z hz] at hz'
    exact hφ hz'

lemma refGroup_two {R : Type} (st : State pp) (s₁ s₂ : GroupModel.Sorted.PSort) (u v : Label P0)
    (fin : Option (Poly pp) → Option (Poly pp) → StateT (State pp) ProbComp R)
    (hfin : ∀ p q (st' : State pp), ∀ z ∈ support ((fin p q).run st'), z.2.guesses = st'.guesses)
    (φ : Finset GuessVar → Prop) [DecidablePred φ] :
    Pr[fun z => φ z.2.guesses | ((do
        let x ← referenceResolve pp s₁ u
        let y ← referenceResolve pp s₂ v
        fin x y) : StateT (State pp) ProbComp R).run st] =
      ∑' ρ₁ : Option (Poly pp) × State pp, Pr[= ρ₁ | (referenceResolve pp s₁ u).run st] *
        ∑' ρ₂ : Option (Poly pp) × State pp, Pr[= ρ₂ | (referenceResolve pp s₂ v).run ρ₁.2] *
          (if φ ρ₂.2.guesses then 1 else 0) := by
  simp only [StateT.run_bind]
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ρ₁
  congr 1
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ρ₂
  congr 1
  exact probEvent_guesses pp _ ρ₂.2.guesses φ (hfin ρ₁.1 ρ₂.1 ρ₂.2)

theorem pending_step_proof (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) :
    PendingStep pp r c x := by
  intro g gq W L hI hsteps hsh hpo hW
  have horder : r.order = L := by
    unfold Record.order
    rw [hpo]
    rfl
  cases gq with
  | lin s a b u v =>
    have hreal : ∀ σ, newGuesses pp g.shadow (realShadow pp σ g (.lin s a b u v)) (.lin s a b u v) =
        ng2 g.shadow.guesses (resolve pp σ (resolve pp σ g.shadow s u).2 s v).2.guesses
          (s, u) (s, v) := by
      intro σ
      show ng2 _ (realShadow pp σ g (.lin s a b u v)).guesses _ _ = _
      rw [realShadow_guesses_lin]
    have hgen : Pr[fun z => g.order ++ newGuesses pp g.shadow z.2 (.lin s a b u v) = L |
        (referenceGroup pp g.oracle.issuedT (.lin s a b u v)).run g.shadow] =
        ∑' ρ₁ : Option (Poly pp) × State pp, Pr[= ρ₁ | (referenceResolve pp s u).run g.shadow] *
          ∑' ρ₂ : Option (Poly pp) × State pp, Pr[= ρ₂ | (referenceResolve pp s v).run ρ₁.2] *
            (if g.order ++ ng2 g.shadow.guesses ρ₂.2.guesses (s, u) (s, v) = L then 1 else 0) := by
      show Pr[fun z => g.order ++ ng2 g.shadow.guesses z.2.guesses (s, u) (s, v) = L |
        (referenceGroup pp g.oracle.issuedT (.lin s a b u v)).run g.shadow] = _
      simp only [referenceGroup]
      refine refGroup_two pp g.shadow s s u v _ ?_
        (fun G => g.order ++ ng2 g.shadow.guesses G (s, u) (s, v) = L)
      intro p q st' z hz
      rcases p with _ | P <;> rcases q with _ | Q
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      · simp only [StateT.run_map, support_map, Set.mem_image] at hz
        obtain ⟨z', hz', rfl⟩ := hz
        exact refInsert_guesses pp s _ st' z' hz'
    simp only [hreal]
    rw [hgen]
    exact pending_core pp r c x g L s s u v hI hsteps hsh horder W hW
  | pair u v =>
    have hnd : ∀ (G₀ G : Finset GuessVar),
        ([((.g₁ : GroupModel.Sorted.PSort), u), ((.g₂ : GroupModel.Sorted.PSort), v)].filter
          fun w => w ∈ G ∧ w ∉ G₀) = ng2 G₀ G (.g₁, u) (.g₂, v) := by
      intro G₀ G
      unfold ng2
      symm
      apply List.Nodup.dedup
      apply List.Nodup.filter
      simp
    have hreal : ∀ σ, newGuesses pp g.shadow (realShadow pp σ g (.pair u v)) (.pair u v) =
        ng2 g.shadow.guesses (resolve pp σ (resolve pp σ g.shadow .g₁ u).2 .g₂ v).2.guesses
          (.g₁, u) (.g₂, v) := by
      intro σ
      show ([((.g₁ : GroupModel.Sorted.PSort), u), ((.g₂ : GroupModel.Sorted.PSort), v)].filter
          fun w => w ∈ (realShadow pp σ g (.pair u v)).guesses ∧ w ∉ g.shadow.guesses) = _
      rw [hnd, realShadow_guesses_pair]
    have hgen : Pr[fun z => g.order ++ newGuesses pp g.shadow z.2 (.pair u v) = L |
        (referenceGroup pp g.oracle.issuedT (.pair u v)).run g.shadow] =
        ∑' ρ₁ : Option (Poly pp) × State pp, Pr[= ρ₁ | (referenceResolve pp .g₁ u).run g.shadow] *
          ∑' ρ₂ : Option (Poly pp) × State pp, Pr[= ρ₂ | (referenceResolve pp .g₂ v).run ρ₁.2] *
            (if g.order ++ ng2 g.shadow.guesses ρ₂.2.guesses (.g₁, u) (.g₂, v) = L
              then 1 else 0) := by
      have hev : (fun z : (GQuery.pair u v : GQuery P0).Result × State pp =>
          g.order ++ newGuesses pp g.shadow z.2 (.pair u v) = L) =
          fun z => g.order ++ ng2 g.shadow.guesses z.2.guesses (.g₁, u) (.g₂, v) = L := by
        funext z
        show (g.order ++ ([((.g₁ : GroupModel.Sorted.PSort), u),
          ((.g₂ : GroupModel.Sorted.PSort), v)].filter
            fun w => w ∈ z.2.guesses ∧ w ∉ g.shadow.guesses) = L) = _
        rw [hnd]
      rw [hev]
      simp only [referenceGroup]
      refine refGroup_two pp g.shadow .g₁ .g₂ u v _ ?_
        (fun G => g.order ++ ng2 g.shadow.guesses G (.g₁, u) (.g₂, v) = L)
      intro p q st' z hz
      rcases p with _ | P <;> rcases q with _ | Q
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      · simp only [StateT.run_map, support_map, Set.mem_image] at hz
        obtain ⟨z', hz', rfl⟩ := hz
        exact refInsert_guesses pp _ _ st' z' hz'
    simp only [hreal]
    rw [hgen]
    exact pending_core pp r c x g L .g₁ .g₂ u v hI hsteps hsh horder W hW
  | name u =>

    have hreal : ∀ σ, newGuesses pp g.shadow (realShadow pp σ g (.name u)) (.name u) = [] :=
      fun σ => rfl
    have hgen : ∀ z, newGuesses pp g.shadow z (.name u) = [] := fun z => rfl
    simp only [hreal, hgen, List.append_nil]
    by_cases hL : g.order = L
    · have hgf : guessFactor pp r c x g.order.length = 1 :=
        guessFactor_of_le pp r c x _ (by rw [horder, hL])
      rw [hgf, mul_one]
      have h1 : Pr[fun _ => g.order = L |
          (referenceGroup pp g.oracle.issuedT (.name u)).run g.shadow] = 1 := by
        rw [probEvent_eq_one_iff]
        exact ⟨probFailure_eq_zero, fun _ _ => hL⟩
      rw [h1, mul_one]
      rw [Finset.filter_true_of_mem (fun σ _ => hL)]
      exact Nat.cast_le.mpr (Finset.card_le_card (fun σ hσ => (hW σ hσ).1))
    · rw [Finset.filter_false_of_mem (fun σ _ => hL), Finset.card_empty, Nat.cast_zero]
      exact zero_le

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation
