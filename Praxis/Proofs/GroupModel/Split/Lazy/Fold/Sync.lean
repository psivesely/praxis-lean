import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Reduction
import Praxis.Algebra.Definitions.Games
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0) (v : Fin P0.n → Vec k P0.N)

structure Projects (st : IdealState P0) (sh : State pp) : Prop where
  g1 : Exposure.Projects (Exposure.value1 pp) st.d1 (sh.dict .g₁)
  g2 : Exposure.Projects (Exposure.value2 pp v) st.d2 (sh.dict .g₂)
  gt : Exposure.Projects (Exposure.valueT pp v) st.dT (sh.dict .gₜ)

lemma resolve_projects (σ : LabelEncoding P0) (st : IdealState P0) (sh : State pp)
    (h : Projects pp v st sh) (s : GroupModel.Sorted.PSort) (l : Label P0) :
    Projects pp v st (resolve pp σ sh s l).2 := by
  unfold resolve
  cases hd : sh.dict s l with
  | some P => exact h
  | none =>
    cases hc : Algebra.decodeLabel (σ s) l with
    | none => exact ⟨h.g1, h.g2, h.gt⟩
    | some x =>
      cases s <;> constructor
      all_goals first
        | simpa [record, Exposure.resolve, hd] using h.g1.resolve _ l
        | simpa [record, Exposure.resolve, hd] using h.g2.resolve _ l
        | simpa [record, Exposure.resolve, hd] using h.gt.resolve _ l
        | simpa [record] using h.g1
        | simpa [record] using h.g2
        | simpa [record] using h.gt

lemma insert_first_none (sh : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) :
    (insertResult pp sh s l P).first = none ↔
      sh.first = none ∧ Exposure.Agrees (sh.dict s) l P := by
  cases hd : sh.dict s l with
  | none => simp [insertResult, hd, Exposure.Agrees]
  | some Q =>
    by_cases hp : P = Q
    · simp [insertResult, hd, hp, Exposure.Agrees]
    · cases hf : sh.first <;> simp [insertResult, hd, hp, hf, Exposure.Agrees]

lemma insert_first_some (sh : State pp) (hf : sh.first = none)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp) (e : Collision pp)
    (he : (insertResult pp sh s l P).first = some e) :
    ∃ Q, sh.dict s l = some Q ∧ P ≠ Q ∧ e = ⟨s, l, P, Q⟩ := by
  cases hd : sh.dict s l with
  | none => simp [insertResult, hd, hf] at he
  | some Q =>
    by_cases hp : P = Q
    · simp [insertResult, hd, hf, hp] at he
    · exact ⟨Q, rfl, hp, (Option.some.inj (by simpa [insertResult, hd, hf, hp] using he)).symm⟩

lemma insert_dict (sh : State pp) (s s' : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) :
    (insertResult pp sh s l P).dict s' =
      if s' = s then Exposure.issue (sh.dict s') l P else sh.dict s' := by
  cases hd : sh.dict s l with
  | none => by_cases hs : s' = s <;> simp [insertResult, hd, record, hs, Exposure.issue]
  | some Q =>
    by_cases hs : s' = s <;> by_cases hp : P = Q <;>
      simp [insertResult, hd, hs, hp, Exposure.issue]

lemma target_insert_mark (cx : IdealCtx P0)
    (hcx : ∀ E F, cx.eqT E F ↔ FormalEqT pp v E F)
    (st : IdealState P0) (sh : State pp)
    (hp : Exposure.Projects (Exposure.valueT pp v) st.dT (sh.dict .gₜ))
    (l : Label P0) (F : ExprT P0) (P Q : Poly pp) (E : ExprT P0)
    (hQ : sh.dict .gₜ l = some Q) (hE : st.dT l = some E)
    (hP : MvPolynomial.constantCoeff P = Exposure.valueT pp v F)
    (hne : P ≠ Q) (hg : GuessFree (⟨.gₜ, l, P, Q⟩ : Collision pp)) :
    (idealT cx false st l F).mark = some (.diff (F - E)) ∧
      (⟨.gₜ, l, P, Q⟩ : Collision pp).value = Exposure.valueT pp v (F - E) := by
  have hq : MvPolynomial.constantCoeff Q = Exposure.valueT pp v E := by
    simpa only [hQ, hE, Option.getD_some] using hp.1 l
  have hval : (⟨.gₜ, l, P, Q⟩ : Collision pp).value = Exposure.valueT pp v (F - E) := by
    simp only [Collision.value, Collision.diff, map_sub, hP, hq]
  have hn : ¬ cx.eqT F E := by
    intro hh
    have hh' := (Exposure.valueT_eq_iff pp v F E).mpr ((hcx F E).mp hh)
    have hz : (⟨.gₜ, l, P, Q⟩ : Collision pp).value = 0 := by
      simp only [Collision.value, Collision.diff, map_sub, hP, hq, hh', sub_self]
    have hd : P - Q = 0 := by
      change (⟨.gₜ, l, P, Q⟩ : Collision pp).diff = 0
      rw [hg, hz, map_zero]
    exact hne (sub_eq_zero.mp hd)
  exact ⟨by simp [idealT, hE, hn], hval⟩

def IsolatedAt (d : Dict pp) (w : GuessVar) : Prop :=
  (∀ P, d w.1 w.2 = some P → P = MvPolynomial.X w) ∧
    ∀ s l P, d s l = some P → (s, l) ≠ w → w ∉ P.vars

def Orphans (st : IdealState P0) (sh : State pp) : Prop :=
  ∀ l, st.dT l = none → IsolatedAt pp sh.dict (.gₜ, l)

lemma isolated_record (d : Dict pp) (w : GuessVar) (h : IsolatedAt pp d w)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hp : if (s, l) = w then P = MvPolynomial.X w else w ∉ P.vars) :
    IsolatedAt pp (record pp d s l P) w := by
  constructor
  · intro Q hQ
    by_cases hs : w.1 = s
    · by_cases hl : w.2 = l
      · have hw : (s, l) = w := Prod.ext hs.symm hl.symm
        have hPQ : P = Q := by simpa [record, hs, hl] using hQ
        rw [← hPQ]
        simpa only [hw, if_true] using hp
      · exact h.1 Q (by simpa [record, hs, hl] using hQ)
    · exact h.1 Q (by simpa [record, hs] using hQ)
  · intro s' l' Q hQ hne
    by_cases hs : s' = s
    · subst s'
      by_cases hl : l' = l
      · subst l'
        have hPQ : P = Q := by simpa [record] using hQ
        rw [← hPQ]
        simpa only [hne, if_false] using hp
      · exact h.2 s l' Q (by simpa [record, hl] using hQ) hne
    · exact h.2 s' l' Q (by simpa [record, hs] using hQ) hne

lemma isolated_resolve (σ : LabelEncoding P0) (sh : State pp) (w : GuessVar)
    (h : IsolatedAt pp sh.dict w) (s : GroupModel.Sorted.PSort) (l : Label P0) :
    IsolatedAt pp (resolve pp σ sh s l).2.dict w := by
  unfold resolve
  cases hd : sh.dict s l with
  | some P => exact h
  | none =>
    cases hc : Algebra.decodeLabel (σ s) l with
    | none => exact h
    | some x =>
      apply isolated_record pp sh.dict w h s l (MvPolynomial.X (s, l))
      split_ifs with hw
      · rw [hw]
      · intro hm
        obtain ⟨d, hd, hw⟩ := (MvPolynomial.mem_vars_iff_mem_support w).mp hm
        have hd' := MvPolynomial.support_monomial_subset hd
        rw [Finset.mem_singleton] at hd'
        subst hd'
        have heq := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
        exact (show (s, l) ≠ w from by assumption) heq.symm

lemma orphans_resolve (σ : LabelEncoding P0) (st : IdealState P0) (sh : State pp)
    (h : Orphans pp st sh) (s : GroupModel.Sorted.PSort) (l : Label P0) :
    Orphans pp st (resolve pp σ sh s l).2 := by
  intro t ht
  exact isolated_resolve pp σ sh (.gₜ, t) (h t ht) s l

lemma guessFree_X_impossible [Nontrivial (Coeff pp)] (w : GuessVar) (P : Poly pp)
    (hn : w ∉ P.vars) :
    ¬ GuessFree (⟨w.1, w.2, P, MvPolynomial.X w⟩ : Collision pp) := by
  intro hg
  have heq : P = MvPolynomial.X w + MvPolynomial.C
      (⟨w.1, w.2, P, MvPolynomial.X w⟩ : Collision pp).value := by
    have hh := hg
    unfold Collision.diff at hh
    exact sub_eq_iff_eq_add'.mp hh
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single w 1)) heq
  have hz : MvPolynomial.coeff (Finsupp.single w 1) P = 0 := by
    by_contra hc
    have hm := MvPolynomial.mem_support_notMem_vars_zero
      (MvPolynomial.mem_support_iff.mpr hc) hn
    simp at hm
  simp [hz, Finsupp.single_ne_zero, eq_comm] at hcoeff

lemma key_none (z : WorldOut P0)
    (st : IdealState P0) (sh : State pp)
    (hp : Exposure.Projects (Exposure.valueT pp (formVec z.out.forms))
      st.dT (sh.dict .gₜ))
    (he : keyCmp pp z sh = none) :
    (idealKdf (idealCtx pp z) st (targetName pp z)).mark =
      some .guessName := by
  have hh : ∀ l, sh.dict .gₜ l = none → st.dT l = none := by
    intro l hl
    cases hd : st.dT l with
    | none => rfl
    | some E => obtain ⟨P, hP⟩ := hp.2 l E hd; simp [hl] at hP
  unfold keyCmp at he
  cases hpos : sh.dict .gₜ (z.enc .gₜ (kappa pp z.out.coins)) with
  | some P => simp [hpos] at he
  | none =>
    cases hneg : sh.dict .gₜ (z.enc .gₜ (-kappa pp z.out.coins)) with
    | some P => simp [hpos, hneg] at he
    | none =>
      have hp0 := hh _ hpos
      have hn0 := hh _ hneg
      simp [idealKdf, idealCtx, hp0, hn0]

lemma key_boundary [Nonempty (CoinDomain pp)] (z : WorldOut P0)
    (noKey : ∀ E, ¬ FormalKey pp (formVec z.out.forms) E) (st : IdealState P0) (sh : State pp)
    (hp : Exposure.Projects (Exposure.valueT pp (formVec z.out.forms))
      st.dT (sh.dict .gₜ)) (ho : Orphans pp st sh)
    (e : Collision pp) (he : keyCmp pp z sh = some e)
    (hg : GuessFree e) :
    ∃ D : ExprT P0,
      (idealKdf (idealCtx pp z) st (targetName pp z)).mark =
        some (.key D) ∧
      e.value = Exposure.valueT pp (formVec z.out.forms) D -
        Exposure.valueKey pp := by
  haveI : Nontrivial (Coeff pp) :=
    (atCoin pp (Classical.choice (inferInstance : Nonempty (CoinDomain pp)))).domain_nontrivial
  unfold keyCmp at he
  cases hpos : sh.dict .gₜ (z.enc .gₜ (kappa pp z.out.coins)) with
  | some P =>
    simp only [hpos, Option.some.injEq] at he
    subst e
    cases hE : st.dT (z.enc .gₜ (kappa pp z.out.coins)) with
    | none =>
      have hPX := (ho _ hE).1 P hpos
      have h0 : (0 : GuessVar →₀ ℕ) ≠
          Finsupp.single (.gₜ, z.enc .gₜ (kappa pp z.out.coins)) 1 := by
        intro hh
        have := congrArg (fun f : GuessVar →₀ ℕ => f (.gₜ, z.enc .gₜ (kappa pp z.out.coins))) hh
        simp at this
      have hcoeff := congrArg
        (MvPolynomial.coeff (Finsupp.single (.gₜ, z.enc .gₜ (kappa pp z.out.coins)) 1)) hg
      simp [Collision.diff, key, hPX, h0] at hcoeff
    | some E =>
      refine ⟨E, ?_, ?_⟩
      · simp [idealKdf, idealCtx, formsOfRun, hE, noKey E, List.find?]
      · have hproj := hp.1 (z.enc .gₜ (kappa pp z.out.coins))
        simp only [hpos, hE, Option.getD_some] at hproj
        simp only [Collision.value, Collision.diff, map_sub, hproj]
        simp only [key, MvPolynomial.constantCoeff_C]
        funext a
        rfl
  | none =>
    have hEpos : st.dT (z.enc .gₜ (kappa pp z.out.coins)) = none := by
      cases hh : st.dT (z.enc .gₜ (kappa pp z.out.coins)) with
      | none => rfl
      | some E => obtain ⟨P, hP⟩ := hp.2 _ E hh; simp [hpos] at hP
    cases hneg : sh.dict .gₜ (z.enc .gₜ (-kappa pp z.out.coins)) with
    | none => simp [hpos, hneg] at he
    | some P =>
      simp only [hpos, hneg, Option.some.injEq] at he
      subst e
      cases hE : st.dT (z.enc .gₜ (-kappa pp z.out.coins)) with
      | none =>
        have hPX := (ho _ hE).1 P hneg
        have h0 : (0 : GuessVar →₀ ℕ) ≠
            Finsupp.single (.gₜ, z.enc .gₜ (-kappa pp z.out.coins)) 1 := by
          intro hh
          have := congrArg (fun f : GuessVar →₀ ℕ => f (.gₜ, z.enc .gₜ (-kappa pp z.out.coins))) hh
          simp at this
        have hcoeff := congrArg
          (MvPolynomial.coeff (Finsupp.single (.gₜ, z.enc .gₜ (-kappa pp z.out.coins)) 1)) hg
        have hh : (fun _ : {a : Assign P0 // ValidCoins pp.qap a.coins} => (-1 : k)) = 0 := by
          simpa only [Collision.diff, key, scalar, hPX, MvPolynomial.coeff_sub,
            MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_same, MvPolynomial.coeff_C,
            h0, if_false, mul_one, sub_zero] using hcoeff
        exact False.elim ((neg_ne_zero.mpr one_ne_zero) hh)
      | some E =>
        refine ⟨(-1 : k) • E, ?_, ?_⟩
        · simp [idealKdf, idealCtx, formsOfRun, hEpos, hE, noKey (-E), List.find?]
        · have hproj := hp.1 (z.enc .gₜ (-kappa pp z.out.coins))
          simp only [hneg, hE, Option.getD_some] at hproj
          simp only [Collision.value, Collision.diff, map_sub, map_mul, scalar,
            MvPolynomial.constantCoeff_C, hproj, map_smul]
          simp only [key, MvPolynomial.constantCoeff_C, Pi.smul_def, smul_eq_mul, Pi.mul_def]
          funext a
          rfl

lemma insert_g1 (cx : IdealCtx P0)
    (hcx : ∀ E F, Exposure.value1 pp E = Exposure.value1 pp F → cx.eq1 E F)
    (st : IdealState P0) (sh : State pp) (h : Projects pp v st sh)
    (l : Label P0) (E : Expr1 P0) (P : Poly pp)
    (hp : MvPolynomial.constantCoeff P = Exposure.value1 pp E)
    (ha : Exposure.Agrees (sh.dict .g₁) l P) :
    Projects pp v (ideal1 cx .g1 st l E) (insertResult pp sh .g₁ l P) ∧
      (ideal1 cx .g1 st l E).mark = st.mark := by
  have hh := Exposure.ideal1_no_collision cx (Exposure.value1 pp) hcx st h.g1 .g1 l E P hp ha
  refine ⟨⟨?_, ?_, ?_⟩, hh.1⟩
  · simpa only [insert_dict, if_pos rfl, ite_true] using hh.2
  · rw [insert_dict]
    simp only [reduceCtorEq, if_false]
    unfold ideal1
    split <;> (try split) <;> exact h.g2
  · rw [insert_dict]
    simp only [reduceCtorEq, if_false]
    unfold ideal1
    split <;> (try split) <;> exact h.gt

lemma insert_g2 (cx : IdealCtx P0)
    (hcx : ∀ E F, Exposure.value2 pp v E = Exposure.value2 pp v F → cx.eq2 E F)
    (st : IdealState P0) (sh : State pp) (h : Projects pp v st sh)
    (l : Label P0) (E : Expr2 P0) (P : Poly pp)
    (hp : MvPolynomial.constantCoeff P = Exposure.value2 pp v E)
    (ha : Exposure.Agrees (sh.dict .g₂) l P) :
    Projects pp v (ideal2 cx .g2 st l E) (insertResult pp sh .g₂ l P) ∧
      (ideal2 cx .g2 st l E).mark = st.mark := by
  have hh := Exposure.ideal2_no_collision cx (Exposure.value2 pp v) hcx st h.g2 .g2 l E P hp ha
  refine ⟨⟨?_, ?_, ?_⟩, hh.1⟩
  · rw [insert_dict]
    simp only [reduceCtorEq, if_false]
    unfold ideal2
    split <;> (try split) <;> exact h.g1
  · simpa only [insert_dict, if_pos rfl, ite_true] using hh.2
  · rw [insert_dict]
    simp only [reduceCtorEq, if_false]
    unfold ideal2
    split <;> (try split) <;> exact h.gt

lemma insert_gt (cx : IdealCtx P0)
    (hcx : ∀ E F, Exposure.valueT pp v E = Exposure.valueT pp v F → cx.eqT E F)
    (st : IdealState P0) (sh : State pp) (h : Projects pp v st sh)
    (l : Label P0) (E : ExprT P0) (P : Poly pp)
    (hp : MvPolynomial.constantCoeff P = Exposure.valueT pp v E)
    (ha : Exposure.Agrees (sh.dict .gₜ) l P) :
    Projects pp v (idealT cx false st l E) (insertResult pp sh .gₜ l P) ∧
      (idealT cx false st l E).mark = st.mark := by
  have hh := Exposure.idealT_no_collision cx (Exposure.valueT pp v) hcx st h.gt false l E P hp ha
  refine ⟨⟨?_, ?_, ?_⟩, hh.1⟩
  · rw [insert_dict]
    simp only [reduceCtorEq, if_false]
    unfold idealT
    split <;> (try split) <;> exact h.g1
  · rw [insert_dict]
    simp only [reduceCtorEq, if_false]
    unfold idealT
    split <;> (try split) <;> exact h.g2
  · simpa only [insert_dict, if_pos rfl, ite_true] using hh.2

lemma resolve_coeff {E : Type} [Zero E] (value : E → Coeff pp)
    (hzero : value 0 = 0) (d : Label P0 → Option E) (sh : State pp)
    (σ : LabelEncoding P0) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (h : Exposure.Projects value d (sh.dict s)) (P : Poly pp)
    (hp : (resolve pp σ sh s l).1 = some P) :
    MvPolynomial.constantCoeff P = value ((d l).getD 0) := by
  classical
  have hh := h.1 l
  unfold resolve at hp
  cases hd : sh.dict s l with
  | some Q =>
    simp only [hd, Option.some.injEq] at hp
    subst P
    simpa [hd] using hh
  | none =>
    cases hc : Algebra.decodeLabel (σ s) l with
    | none => simp [hd, hc] at hp
    | some x =>
      simp only [hd, hc, Option.some.injEq] at hp
      subst P
      simpa [hd] using hh

lemma resolve_entry (σ : LabelEncoding P0) (sh : State pp) (s : GroupModel.Sorted.PSort)
    (l : Label P0) (P : Poly pp) (hp : (resolve pp σ sh s l).1 = some P) :
    (resolve pp σ sh s l).2.dict s l = some P := by
  unfold resolve at hp ⊢
  cases hd : sh.dict s l with
  | some Q => simpa [hd] using hp
  | none =>
    cases hc : Algebra.decodeLabel (σ s) l with
    | none => simp [hd, hc] at hp
    | some x => simpa [hd, hc, record] using hp

lemma resolve_preserves_entry (σ : LabelEncoding P0) (sh : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0)
    (s' : GroupModel.Sorted.PSort) (t : Label P0) (P : Poly pp)
    (hp : sh.dict s' t = some P) :
    (resolve pp σ sh s l).2.dict s' t = some P := by
  unfold resolve
  cases hd : sh.dict s l with
  | some Q => exact hp
  | none =>
    cases hc : Algebra.decodeLabel (σ s) l with
    | none => exact hp
    | some x =>
      by_cases hs : s' = s
      · subst s'
        have ht : t ≠ l := by intro ht; subst t; simp [hd] at hp
        simpa [record, ht] using hp
      · simpa [record, hs] using hp

lemma recordT_projects (σ : LabelEncoding P0) (st : IdealState P0) (sh : State pp)
    (h : Projects pp v st sh) (u w : Label P0) (P Q : Poly pp)
    (hp : (resolve pp σ sh .gₜ u).1 = some P)
    (hq : (resolve pp σ (resolve pp σ sh .gₜ u).2 .gₜ w).1 = some Q) :
    Projects pp v (recordT st u w) (resolve pp σ (resolve pp σ sh .gₜ u).2 .gₜ w).2 := by
  have hh := resolve_projects pp v σ st _ (resolve_projects pp v σ st sh h .gₜ u) .gₜ w
  refine ⟨hh.g1, hh.g2, ⟨?_, ?_⟩⟩
  · intro l
    have hl := hh.gt.1 l
    dsimp only [recordT]
    split_ifs with hc
    · have hn : st.dT l = none := by simpa using hc.2
      simpa [hn] using hl
    · exact hl
  · intro l E he
    dsimp only [recordT] at he
    split_ifs at he with hc
    · rcases hc.1 with hu | hw
      · subst l
        exact ⟨P, resolve_preserves_entry pp σ _ .gₜ w .gₜ u P
          (resolve_entry pp σ sh .gₜ u P hp)⟩
      · subst l
        exact ⟨Q, resolve_entry pp σ _ .gₜ w Q hq⟩
    · exact hh.gt.2 l E he

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync
