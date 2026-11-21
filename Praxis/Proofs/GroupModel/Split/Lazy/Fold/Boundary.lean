import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Operations
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Initial
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Sync
import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Reduction
import Praxis.Algebra.Definitions.Games
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option linter.constructorNameAsVariable false

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0) (v : Fin P0.n → Vec k P0.N)

lemma const_orphans (st : IdealState P0) (sh : State pp) (h : sh.dict = constDict pp v st) :
    Orphans pp st sh := by
  classical
  intro l hl
  constructor
  · intro P hp
    rw [h] at hp
    simp [constDict, hl] at hp
  · intro s t P hp hne
    rw [h] at hp
    cases s with
    | g₁ =>
      cases he : st.d1 t <;> simp only [constDict, he, Option.map_none,
        Option.map_some, reduceCtorEq, Option.some.injEq] at hp
      subst P
      simp
    | g₂ =>
      cases he : st.d2 t <;> simp only [constDict, he, Option.map_none,
        Option.map_some, reduceCtorEq, Option.some.injEq] at hp
      subst P
      simp
    | gₜ =>
      cases he : st.dT t <;> simp only [constDict, he, Option.map_none,
        Option.map_some, reduceCtorEq, Option.some.injEq] at hp
      subst P
      simp

lemma const_domain (st : IdealState P0) (sh : State pp) (h : sh.dict = constDict pp v st)
    (l : Label P0) (P : Poly pp) (hp : sh.dict .gₜ l = some P) : (st.dT l).isSome := by
  rw [h] at hp
  cases he : st.dT l <;> simp [constDict, he] at hp ⊢

@[simp] lemma ideal1_dT (cx : IdealCtx P0) (st : IdealState P0) (k : Mark P0)
    (l : Label P0) (E : Expr1 P0) : (ideal1 cx k st l E).dT = st.dT := by
  unfold ideal1
  split <;> (try split) <;> rfl

@[simp] lemma ideal2_dT (cx : IdealCtx P0) (st : IdealState P0) (k : Mark P0)
    (l : Label P0) (E : Expr2 P0) : (ideal2 cx k st l E).dT = st.dT := by
  unfold ideal2
  split <;> (try split) <;> rfl

lemma idealT_preserves (cx : IdealCtx P0) (initial : Bool) (st : IdealState P0)
    (l t : Label P0) (E F : ExprT P0) (hF : st.dT t = some F) :
    (idealT cx initial st l E).dT t = some F := by
  classical
  cases he : st.dT l with
  | none =>
    have hne : t ≠ l := by intro heq; subst t; simp [he] at hF
    simpa only [idealT, he, Function.update_of_ne hne] using hF
  | some G => simp only [idealT, he]; split <;> exact hF

lemma recordT_preserves (st : IdealState P0) (u w t : Label P0)
    (E : ExprT P0) (he : st.dT t = some E) : (recordT st u w).dT t = some E := by
  simp [recordT, he]

lemma idealOp_preserves (cx : IdealCtx P0) (st : IdealState P0) (o : TrOp P0)
    (l : Label P0) (E : ExprT P0) (he : st.dT l = some E) :
    (idealOp cx st o).dT l = some E := by
  cases o with
  | lin s a b u w res =>
    cases s with
    | g₁ => simpa only [idealOp, ideal1_dT] using he
    | g₂ => simpa only [idealOp, ideal2_dT] using he
    | gₜ =>
      exact idealT_preserves cx false (recordT st u w) res l _ E
        (recordT_preserves st u w l E he)
  | pair u w res => exact idealT_preserves cx false st res l _ E he
  | name u nm =>
    simp only [idealOp]
    split
    · exact he
    · exact idealT_preserves cx false {st with named := Function.update st.named u true} _ l _ E he

lemma idealT_result (cx : IdealCtx P0) (initial : Bool) (st : IdealState P0)
    (l : Label P0) (E : ExprT P0) : ((idealT cx initial st l E).dT l).isSome := by
  classical
  cases he : st.dT l with
  | none => simp [idealT, he]
  | some F => simp only [idealT, he]; split <;> simp [he]

lemma idealOp_result (cx : IdealCtx P0) (st : IdealState P0) (o : TrOp P0)
    (l : Label P0) (hl : o.issuedGT = some l) : ((idealOp cx st o).dT l).isSome := by
  cases o with
  | lin s a b u w res =>
    cases s <;> simp only [TrOp.issuedGT, reduceCtorEq, Option.some.injEq] at hl
    subst l
    exact idealT_result cx false (recordT st u w) res _
  | pair u w res =>
    simp only [TrOp.issuedGT, Option.some.injEq] at hl
    subst l
    exact idealT_result cx false st res _
  | name u nm => simp [TrOp.issuedGT] at hl

lemma group_issued (cx : IdealCtx P0) (st : IdealState P0) (oracle : OracleState P0)
    (h : ∀ l ∈ oracle.issuedT, (st.dT l).isSome) (q : GQuery P0) (R : q.Result)
    (r : q.Answer × OracleState P0) (hr : r ∈ support ((finishGroup q R).run oracle)) :
    ∀ l ∈ r.2.issuedT, ((groupIdeal cx st q R).dT l).isSome := by
  intro l hl
  rcases Simulation.finishGroup_issued q R oracle r hr l hl with hl | ⟨o, ho, hol⟩
  · obtain ⟨E, he⟩ := Option.isSome_iff_exists.mp (h l hl)
    unfold groupIdeal
    cases ho : trEntry q R with
    | none => exact h l hl
    | some o => exact Option.isSome_iff_exists.mpr ⟨E, idealOp_preserves cx st o l E he⟩
  · simp only [groupIdeal, ho]
    exact idealOp_result cx st o l hol

lemma not_mem_linear (w : GuessVar) (a b : k) (P Q : Poly pp)
    (hp : w ∉ P.vars) (hq : w ∉ Q.vars) :
    w ∉ (scalar pp a * P + scalar pp b * Q).vars := by
  intro hm
  have hh := MvPolynomial.vars_add_subset _ _ hm
  rcases Finset.mem_union.mp hh with hh | hh
  · have hh' := MvPolynomial.vars_mul _ _ hh
    apply hp
    simpa only [scalar, MvPolynomial.vars_C, Finset.empty_union] using hh'
  · have hh' := MvPolynomial.vars_mul _ _ hh
    apply hq
    simpa only [scalar, MvPolynomial.vars_C, Finset.empty_union] using hh'

lemma not_mem_pair (w : GuessVar) (P Q : Poly pp) (hp : w ∉ P.vars) (hq : w ∉ Q.vars) :
    w ∉ (P * Q).vars := by
  intro hm
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul P Q hm) with hm | hm
  · exact hp hm
  · exact hq hm

lemma orphans_source_insert (st st' : IdealState P0) (sh : State pp)
    (h : Orphans pp st sh) (hT : st'.dT = st.dT)
    (s : GroupModel.Sorted.PSort) (hs : s ≠ .gₜ) (l : Label P0) (P : Poly pp)
    (hp : ∀ t, st.dT t = none → (.gₜ, t) ∉ P.vars) :
    Orphans pp st' (insertResult pp sh s l P) := by
  intro t ht
  rw [hT] at ht
  exact isolated_insert pp sh (.gₜ, t) (h t ht) s l P
    (fun heq => hs (congrArg Prod.fst heq)) (hp t ht)

lemma group_orphans (cx : IdealCtx P0) (σ : LabelEncoding P0)
    (st : IdealState P0) (sh : State pp) (ho : Orphans pp st sh)
    (hn : Named pp σ st.named sh) (issued : Finset (Label P0))
    (hideal : ∀ l ∈ issued, (st.dT l).isSome)
    (hcover : ∀ l ∈ issued, ∃ P, sh.dict .gₜ l = some P)
    (q : GQuery P0) :
    Orphans pp (groupIdeal cx st q (groupAnswer σ issued q))
      (observeGroup pp σ sh q (groupAnswer σ issued q)) := by
  classical
  cases q with
  | lin s a b u w =>
    have hx := orphans_resolve pp σ st sh ho s u
    have hy := orphans_resolve pp σ st _ hx s w
    cases hr : groupAnswer σ issued (.lin s a b u w) with
    | none =>
      cases hp : (resolve pp σ sh s u).1 <;>
        cases hq : (resolve pp σ (resolve pp σ sh s u).2 s w).1 <;>
        simpa only [groupIdeal, trEntry, hr, Option.map_none, observeGroup, hp, hq] using hy
    | some l =>
      have hdec : ∃ x y, Algebra.decodeLabel (σ s) u = some x ∧
          Algebra.decodeLabel (σ s) w = some y := by
        cases hu : Algebra.decodeLabel (σ s) u <;>
          cases hw : Algebra.decodeLabel (σ s) w <;> simp [groupAnswer, hu, hw] at hr
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨x, y, hu, hw⟩ := hdec
      obtain ⟨P, hp⟩ := Simulation.resolve_some_of_decode pp σ sh s u x hu
      obtain ⟨Q, hq⟩ := Simulation.resolve_some_of_decode pp σ (resolve pp σ sh s u).2 s w y hw
      have hP := resolve_preserves_entry pp σ _ s w s u P (resolve_entry pp σ sh s u P hp)
      have hQ := resolve_entry pp σ _ s w Q hq
      cases s with
      | g₁ =>
        have hh := orphans_source_insert pp st (idealOp cx st (.lin .g₁ a b u w l)) _ hy
          (by simp [idealOp]) .g₁ (by decide) l (scalar pp a * P + scalar pp b * Q) (by
            intro t ht
            exact not_mem_linear pp (.gₜ, t) a b P Q
              ((hy t ht).2 .g₁ u P hP (by simp)) ((hy t ht).2 .g₁ w Q hQ (by simp)))
        simpa only [groupIdeal, trEntry, hr, Option.map_some, observeGroup, hp, hq] using hh
      | g₂ =>
        have hh := orphans_source_insert pp st (idealOp cx st (.lin .g₂ a b u w l)) _ hy
          (by simp [idealOp]) .g₂ (by decide) l (scalar pp a * P + scalar pp b * Q) (by
            intro t ht
            exact not_mem_linear pp (.gₜ, t) a b P Q
              ((hy t ht).2 .g₂ u P hP (by simp)) ((hy t ht).2 .g₂ w Q hQ (by simp)))
        simpa only [groupIdeal, trEntry, hr, Option.map_some, observeGroup, hp, hq] using hh
      | gₜ =>
        have hrec := orphans_recordT pp σ st sh ho u w
        have hh := orphans_insert_gt pp cx (recordT st u w) _ hrec l (a • (st.dT u).getD 0 + b • (st.dT w).getD 0)
          (scalar pp a * P + scalar pp b * Q) (by
            intro t ht hne
            obtain ⟨hp0, hq0⟩ := recordT_not_mem pp σ st sh ho u w t ht P Q hp hq
            exact not_mem_linear pp (.gₜ, t) a b P Q hp0 hq0)
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, observeGroup, hp, hq] using hh
  | pair u w =>
    have hx := orphans_resolve pp σ st sh ho .g₁ u
    have hy := orphans_resolve pp σ st _ hx .g₂ w
    cases hr : groupAnswer σ issued (.pair u w) with
    | none =>
      cases hp : (resolve pp σ sh .g₁ u).1 <;>
        cases hq : (resolve pp σ (resolve pp σ sh .g₁ u).2 .g₂ w).1 <;>
        simpa only [groupIdeal, trEntry, hr, Option.map_none, observeGroup, hp, hq] using hy
    | some l =>
      have hdec : ∃ x y, Algebra.decodeLabel (σ .g₁) u = some x ∧
          Algebra.decodeLabel (σ .g₂) w = some y := by
        cases hu : Algebra.decodeLabel (σ .g₁) u <;>
          cases hw : Algebra.decodeLabel (σ .g₂) w <;> simp [groupAnswer, hu, hw] at hr
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨x, y, hu, hw⟩ := hdec
      obtain ⟨P, hp⟩ := Simulation.resolve_some_of_decode pp σ sh .g₁ u x hu
      obtain ⟨Q, hq⟩ := Simulation.resolve_some_of_decode pp σ (resolve pp σ sh .g₁ u).2 .g₂ w y hw
      have hP := resolve_preserves_entry pp σ _ .g₂ w .g₁ u P (resolve_entry pp σ sh .g₁ u P hp)
      have hQ := resolve_entry pp σ _ .g₂ w Q hq
      have hh := orphans_insert_gt pp cx st _ hy l (pairExpr ((st.d1 u).getD 0) ((st.d2 w).getD 0)) (P * Q) (by
        intro t ht hne
        exact not_mem_pair pp (.gₜ, t) P Q
          ((hy t ht).2 .g₁ u P hP (by simp)) ((hy t ht).2 .g₂ w Q hQ (by simp)))
      simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, observeGroup, hp, hq] using hh
  | name u =>
    cases hr : groupAnswer σ issued (.name u) with
    | none => simpa only [groupIdeal, trEntry, hr, Option.map_none, observeGroup] using ho
    | some nm =>
      have hu : u ∈ issued := by by_contra hu; simp [groupAnswer, hu] at hr
      obtain ⟨P, hp⟩ := hcover u hu
      obtain ⟨E, hE⟩ := Option.isSome_iff_exists.mp (hideal u hu)
      have hdec : ∃ x, Algebra.decodeLabel (σ .gₜ) u = some x ∧ nm = labelName (σ .gₜ) x := by
        cases hd : Algebra.decodeLabel (σ .gₜ) u with
        | none => simp [groupAnswer, hu, hd] at hr
        | some x => exact ⟨x, rfl, by simpa [groupAnswer, hu, hd] using hr.symm⟩
      obtain ⟨x, hd, rfl⟩ := hdec
      have hlabel : otherLabel u (labelName (σ .gₜ) x) = σ .gₜ (-x) := by
        rw [← (decodeLabel_eq_some_iff _ _ _).mp hd, otherLabel_name]
      by_cases hnamed : st.named u = true
      · obtain ⟨Q, hQ, hi⟩ := hn u hnamed
        have hPQ : Q = P := Option.some.inj (hQ.symm.trans hp)
        have hInv : sh.dict .gₜ (otherLabel u (labelName (σ .gₜ) x)) = some (-P) := by
          simpa only [hd, Option.getD_some, hPQ, hlabel] using hi
        have hsh : observeGroup pp σ sh (.name u) (some (labelName (σ .gₜ) x)) = sh := by
          simp only [observeGroup, hp, Option.getD_some]
          exact insertResult_of_same pp sh .gₜ _ _ hInv
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, hnamed,
          if_true, hsh] using ho
      · have hh := orphans_insert_gt pp cx {st with named := Function.update st.named u true}
          sh ho (otherLabel u (labelName (σ .gₜ) x)) (-(st.dT u).getD 0) (-P) (by
            intro t ht hne
            have htu : u ≠ t := by intro heq; subst t; simp [hE] at ht
            simpa only [MvPolynomial.vars_neg] using
              (ho t ht).2 .gₜ u P hp (by simpa using htu))
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, hnamed,
          Bool.false_eq_true, ite_false, observeGroup, hp, Option.getD_some] using hh

lemma target_boundary [Nontrivial (Coeff pp)] (cx : IdealCtx P0)
    (hcx : ∀ E F, cx.eqT E F ↔ FormalEqT pp v E F)
    (st : IdealState P0) (sh : State pp) (hf : sh.first = none)
    (hp : Exposure.Projects (Exposure.valueT pp v) st.dT (sh.dict .gₜ))
    (ho : Orphans pp st sh) (l : Label P0) (F : ExprT P0) (P : Poly pp)
    (hP : MvPolynomial.constantCoeff P = Exposure.valueT pp v F)
    (hfree : st.dT l = none → (.gₜ, l) ∉ P.vars)
    (e : Collision pp) (he : (insertResult pp sh .gₜ l P).first = some e)
    (hg : GuessFree e) :
    ∃ D, (idealT cx false st l F).mark = some (.diff D) ∧
      e.value = Exposure.valueT pp v D := by
  obtain ⟨Q, hQ, hne, rfl⟩ := insert_first_some pp sh hf .gₜ l P e he
  cases hE : st.dT l with
  | none =>
    have hQX := (ho l hE).1 Q hQ
    subst Q
    exact False.elim (guessFree_X_impossible pp (.gₜ, l) P (hfree hE) hg)
  | some E =>
    exact ⟨F - E, target_insert_mark pp v cx hcx st sh hp l F P Q E hQ hE hP hne hg⟩

lemma group_boundary [Nonempty (CoinDomain pp)] (cx : IdealCtx P0)
    (hcx : ∀ E F, cx.eqT E F ↔ FormalEqT pp v E F)
    (σ : LabelEncoding P0) (st : IdealState P0) (sh : State pp) (hf : sh.first = none)
    (h : Projects pp v st sh) (ho : Orphans pp st sh) (hn : Named pp σ st.named sh)
    (issued : Finset (Label P0))
    (hideal : ∀ l ∈ issued, (st.dT l).isSome)
    (hcover : ∀ l ∈ issued, ∃ P, sh.dict .gₜ l = some P)
    (q : GQuery P0) (e : Collision pp)
    (he : (observeGroup pp σ sh q (groupAnswer σ issued q)).first = some e)
    (hg : GuessFree e) (hs : e.sort = .gₜ) :
    ∃ D, (groupIdeal cx st q (groupAnswer σ issued q)).mark = some (.diff D) ∧
      e.value = Exposure.valueT pp v D := by
  classical
  haveI : Nontrivial (Coeff pp) :=
    (atCoin pp (Classical.choice (inferInstance : Nonempty (CoinDomain pp)))).domain_nontrivial
  cases q with
  | lin s a b u w =>
    have hx := resolve_projects pp v σ st sh h s u
    have hy := resolve_projects pp v σ st _ hx s w
    have hof := orphans_resolve pp σ st _ (orphans_resolve pp σ st sh ho s u) s w
    have hf2 : (resolve pp σ (resolve pp σ sh s u).2 s w).2.first = none := by
      rw [resolve_first, resolve_first, hf]
    cases hr : groupAnswer σ issued (.lin s a b u w) with
    | none =>
      cases hp : (resolve pp σ sh s u).1 <;>
        cases hq : (resolve pp σ (resolve pp σ sh s u).2 s w).1 <;>
        simp only [observeGroup, hr, hp, hq, hf2, reduceCtorEq] at he
    | some l =>
      have hdec : ∃ x y, Algebra.decodeLabel (σ s) u = some x ∧
          Algebra.decodeLabel (σ s) w = some y := by
        cases hu : Algebra.decodeLabel (σ s) u <;>
          cases hw : Algebra.decodeLabel (σ s) w <;> simp [groupAnswer, hu, hw] at hr
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨x, y, hu, hw⟩ := hdec
      obtain ⟨P, hp⟩ := Simulation.resolve_some_of_decode pp σ sh s u x hu
      obtain ⟨Q, hq⟩ := Simulation.resolve_some_of_decode pp σ (resolve pp σ sh s u).2 s w y hw
      have hins : (insertResult pp (resolve pp σ (resolve pp σ sh s u).2 s w).2 s l
          (scalar pp a * P + scalar pp b * Q)).first = some e := by
        simpa only [observeGroup, hp, hq, hr] using he
      cases s with
      | g₁ =>
        obtain ⟨Qold, _, _, rfl⟩ := insert_first_some pp _ hf2 .g₁ l _ e hins
        cases hs
      | g₂ =>
        obtain ⟨Qold, _, _, rfl⟩ := insert_first_some pp _ hf2 .g₂ l _ e hins
        cases hs
      | gₜ =>
        have hpc := resolve_coeff pp (Exposure.valueT pp v) (map_zero _) st.dT sh σ .gₜ u h.gt P hp
        have hqc := resolve_coeff pp (Exposure.valueT pp v) (map_zero _) st.dT _ σ .gₜ w hx.gt Q hq
        have hrec := recordT_projects pp v σ st sh h u w P Q hp hq
        have horec := orphans_recordT pp σ st sh ho u w
        have hh := target_boundary pp v cx hcx (recordT st u w) _ hf2 hrec.gt horec l
          (a • (st.dT u).getD 0 + b • (st.dT w).getD 0) (scalar pp a * P + scalar pp b * Q)
          (linear_coeff pp (Exposure.valueT pp v) a b _ _ P Q hpc hqc)
          (by
            intro ht
            obtain ⟨hp0, hq0⟩ := recordT_not_mem pp σ st sh ho u w l ht P Q hp hq
            exact not_mem_linear pp (.gₜ, l) a b P Q hp0 hq0) e hins hg
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp] using hh
  | pair u w =>
    have hx := resolve_projects pp v σ st sh h .g₁ u
    have hy := resolve_projects pp v σ st _ hx .g₂ w
    have hof := orphans_resolve pp σ st _ (orphans_resolve pp σ st sh ho .g₁ u) .g₂ w
    have hf2 : (resolve pp σ (resolve pp σ sh .g₁ u).2 .g₂ w).2.first = none := by
      rw [resolve_first, resolve_first, hf]
    cases hr : groupAnswer σ issued (.pair u w) with
    | none =>
      cases hp : (resolve pp σ sh .g₁ u).1 <;>
        cases hq : (resolve pp σ (resolve pp σ sh .g₁ u).2 .g₂ w).1 <;>
        simp only [observeGroup, hr, hp, hq, hf2, reduceCtorEq] at he
    | some l =>
      have hdec : ∃ x y, Algebra.decodeLabel (σ .g₁) u = some x ∧
          Algebra.decodeLabel (σ .g₂) w = some y := by
        cases hu : Algebra.decodeLabel (σ .g₁) u <;>
          cases hw : Algebra.decodeLabel (σ .g₂) w <;> simp [groupAnswer, hu, hw] at hr
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨x, y, hu, hw⟩ := hdec
      obtain ⟨P, hp⟩ := Simulation.resolve_some_of_decode pp σ sh .g₁ u x hu
      obtain ⟨Q, hq⟩ := Simulation.resolve_some_of_decode pp σ (resolve pp σ sh .g₁ u).2 .g₂ w y hw
      have hins : (insertResult pp (resolve pp σ (resolve pp σ sh .g₁ u).2 .g₂ w).2 .gₜ l
          (P * Q)).first = some e := by simpa only [observeGroup, hp, hq, hr] using he
      have hpc := resolve_coeff pp (Exposure.value1 pp) (map_zero _) st.d1 sh σ .g₁ u h.g1 P hp
      have hqc := resolve_coeff pp (Exposure.value2 pp v) (map_zero _) st.d2 _ σ .g₂ w hx.g2 Q hq
      have hP := resolve_preserves_entry pp σ _ .g₂ w .g₁ u P (resolve_entry pp σ sh .g₁ u P hp)
      have hQ := resolve_entry pp σ _ .g₂ w Q hq
      have hh := target_boundary pp v cx hcx st _ hf2 hy.gt hof l
        (pairExpr ((st.d1 u).getD 0) ((st.d2 w).getD 0)) (P * Q)
        (by rw [map_mul, hpc, hqc, Exposure.value_pair]) (by
          intro ht
          exact not_mem_pair pp (.gₜ, l) P Q
            ((hof l ht).2 .g₁ u P hP (by simp)) ((hof l ht).2 .g₂ w Q hQ (by simp))) e hins hg
      simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp] using hh
  | name u =>
    cases hr : groupAnswer σ issued (.name u) with
    | none => simp only [observeGroup, hr, hf, reduceCtorEq] at he
    | some nm =>
      have hu : u ∈ issued := by by_contra hu; simp [groupAnswer, hu] at hr
      obtain ⟨P, hp⟩ := hcover u hu
      obtain ⟨E, hE⟩ := Option.isSome_iff_exists.mp (hideal u hu)
      have hdec : ∃ x, Algebra.decodeLabel (σ .gₜ) u = some x ∧ nm = labelName (σ .gₜ) x := by
        cases hd : Algebra.decodeLabel (σ .gₜ) u with
        | none => simp [groupAnswer, hu, hd] at hr
        | some x => exact ⟨x, rfl, by simpa [groupAnswer, hu, hd] using hr.symm⟩
      obtain ⟨x, hd, rfl⟩ := hdec
      have hlabel : otherLabel u (labelName (σ .gₜ) x) = σ .gₜ (-x) := by
        rw [← (decodeLabel_eq_some_iff _ _ _).mp hd, otherLabel_name]
      by_cases hnamed : st.named u = true
      · obtain ⟨Q, hQ, hi⟩ := hn u hnamed
        have hPQ : Q = P := Option.some.inj (hQ.symm.trans hp)
        have hInv : sh.dict .gₜ (otherLabel u (labelName (σ .gₜ) x)) = some (-P) := by
          simpa only [hd, Option.getD_some, hPQ, hlabel] using hi
        have hsh : observeGroup pp σ sh (.name u) (some (labelName (σ .gₜ) x)) = sh := by
          simp only [observeGroup, hp, Option.getD_some]
          exact insertResult_of_same pp sh .gₜ _ _ hInv
        simp only [hr, hsh, hf, reduceCtorEq] at he
      · have hins : (insertResult pp sh .gₜ (otherLabel u (labelName (σ .gₜ) x)) (-P)).first = some e := by
          simpa only [observeGroup, hr, hp, Option.getD_some] using he
        have hpc := h.gt.1 u
        simp only [hp, Option.getD_some] at hpc
        have hh := target_boundary pp v cx hcx
          {st with named := Function.update st.named u true} sh hf h.gt ho
          (otherLabel u (labelName (σ .gₜ) x)) (-(st.dT u).getD 0) (-P)
          (by rw [map_neg, hpc, map_neg]) (by
            intro ht
            have htu : u ≠ otherLabel u (labelName (σ .gₜ) x) := by
              intro heq
              rw [← heq] at ht
              simp only [hE, reduceCtorEq] at ht
            simpa only [MvPolynomial.vars_neg] using
              (ho _ ht).2 .gₜ u P hp (by simpa using htu)) e hins hg
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, hnamed,
          Bool.false_eq_true, ite_false] using hh

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync
