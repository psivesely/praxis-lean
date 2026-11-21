import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Initial
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Sync
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Reduction
import Praxis.Algebra.Definitions.Games
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

def Named (σ : LabelEncoding P0) (named : Label P0 → Bool) (sh : State pp) : Prop :=
  ∀ u, named u = true → ∃ P, sh.dict .gₜ u = some P ∧
    sh.dict .gₜ (σ .gₜ (-((Algebra.decodeLabel (σ .gₜ) u).getD 0))) = some (-P)

lemma named_mono (σ : LabelEncoding P0) (named : Label P0 → Bool) (sh sh' : State pp)
    (h : Named pp σ named sh)
    (hm : ∀ s l P, sh.dict s l = some P → sh'.dict s l = some P) :
    Named pp σ named sh' := by
  intro u hu
  obtain ⟨P, hp, hneg⟩ := h u hu
  exact ⟨P, hm _ _ _ hp, hm _ _ _ hneg⟩

lemma scalar_mul (a : k) (P : Poly pp) : scalar pp a * P = a • P := by
  classical
  ext d ω
  simp [scalar, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_smul,
    Pi.smul_apply, smul_eq_mul]

lemma linear_coeff {T : Type} [AddCommMonoid T] [Module k T]
    (value : T →ₗ[k] Coeff pp) (a b : k) (E F : T) (P Q : Poly pp)
    (hp : MvPolynomial.constantCoeff P = value E)
    (hq : MvPolynomial.constantCoeff Q = value F) :
    MvPolynomial.constantCoeff (scalar pp a * P + scalar pp b * Q) = value (a • E + b • F) := by
  rw [scalar_mul, scalar_mul, map_add, MvPolynomial.constantCoeff_smul,
    MvPolynomial.constantCoeff_smul, hp, hq, map_add, map_smul, map_smul]

lemma isolated_insert (sh : State pp) (w : GuessVar) (h : IsolatedAt pp sh.dict w)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hne : (s, l) ≠ w) (hp : w ∉ P.vars) :
    IsolatedAt pp (insertResult pp sh s l P).dict w := by
  classical
  unfold insertResult
  cases hd : sh.dict s l with
  | none => exact isolated_record pp sh.dict w h s l P (by simpa [hne] using hp)
  | some Q => simp only [hd]; split <;> exact h

lemma idealT_none (cx : IdealCtx P0) (initial : Bool) (st : IdealState P0)
    (l t : Label P0) (E : ExprT P0)
    (ht : (idealT cx initial st l E).dT t = none) : st.dT t = none ∧ t ≠ l := by
  classical
  cases hl : st.dT l with
  | none =>
    have hne : t ≠ l := by intro hh; subst t; simp [idealT, hl] at ht
    exact ⟨by simpa [idealT, hl, hne] using ht, hne⟩
  | some F =>
    have hprev : st.dT t = none := by
      unfold idealT at ht
      simp only [hl] at ht
      split at ht <;> exact ht
    exact ⟨hprev, by intro hh; subst t; simp [hl] at hprev⟩

lemma orphans_insert_gt (cx : IdealCtx P0) (st : IdealState P0) (sh : State pp)
    (h : Orphans pp st sh) (l : Label P0) (E : ExprT P0) (P : Poly pp)
    (hp : ∀ t, st.dT t = none → t ≠ l → (.gₜ, t) ∉ P.vars) :
    Orphans pp (idealT cx false st l E) (insertResult pp sh .gₜ l P) := by
  intro t ht
  obtain ⟨ht0, hne⟩ := idealT_none cx false st l t E ht
  exact isolated_insert pp sh (.gₜ, t) (h t ht0) .gₜ l P
    (by simpa [eq_comm] using hne) (hp t ht0 hne)

lemma orphans_recordT (σ : LabelEncoding P0) (st : IdealState P0) (sh : State pp)
    (h : Orphans pp st sh) (u w : Label P0) :
    Orphans pp (recordT st u w) (resolve pp σ (resolve pp σ sh .gₜ u).2 .gₜ w).2 := by
  intro t ht
  have ht0 : st.dT t = none := by
    cases hd : st.dT t with
    | none => rfl
    | some E => simp [recordT, hd] at ht

  exact isolated_resolve pp σ _ (.gₜ, t)
    (isolated_resolve pp σ sh (.gₜ, t) (h t ht0) .gₜ u) .gₜ w

lemma recordT_not_mem (σ : LabelEncoding P0) (st : IdealState P0) (sh : State pp)
    (h : Orphans pp st sh) (u w l : Label P0)
    (hl : (recordT st u w).dT l = none) (P Q : Poly pp)
    (hp : (resolve pp σ sh .gₜ u).1 = some P)
    (hq : (resolve pp σ (resolve pp σ sh .gₜ u).2 .gₜ w).1 = some Q) :
    (.gₜ, l) ∉ P.vars ∧ (.gₜ, l) ∉ Q.vars := by
  have hne : l ≠ u ∧ l ≠ w := by
    constructor
    · intro heq
      subst l
      cases hd : st.dT u <;> simp [recordT, hd] at hl
    · intro heq
      subst l
      cases hd : st.dT w <;> simp [recordT, hd] at hl
  have hh := orphans_recordT pp σ st sh h u w l hl
  constructor
  · exact hh.2 .gₜ u P (resolve_preserves_entry pp σ _ .gₜ w .gₜ u P
      (resolve_entry pp σ sh .gₜ u P hp)) (by simpa [eq_comm] using hne.1)
  · exact hh.2 .gₜ w Q (resolve_entry pp σ _ .gₜ w Q hq)
      (by simpa [eq_comm] using hne.2)

def groupIdeal (cx : IdealCtx P0) (st : IdealState P0) (q : GQuery P0) (R : q.Result) :
    IdealState P0 :=
  match trEntry q R with | none => st | some o => idealOp cx st o

lemma group_clear (cx : IdealCtx P0)
    (h1 : ∀ E F, Exposure.value1 pp E = Exposure.value1 pp F → cx.eq1 E F)
    (h2 : ∀ E F, Exposure.value2 pp v E = Exposure.value2 pp v F → cx.eq2 E F)
    (hT : ∀ E F, Exposure.valueT pp v E = Exposure.valueT pp v F → cx.eqT E F)
    (σ : LabelEncoding P0) (st : IdealState P0) (sh : State pp)
    (h : Projects pp v st sh) (hn : Named pp σ st.named sh)
    (issued : Finset (Label P0))
    (hcover : ∀ l ∈ issued, ∃ P, sh.dict .gₜ l = some P)
    (q : GQuery P0)
    (hc : (observeGroup pp σ sh q (groupAnswer σ issued q)).first = none) :
    Projects pp v (groupIdeal cx st q (groupAnswer σ issued q))
      (observeGroup pp σ sh q (groupAnswer σ issued q)) ∧
    (groupIdeal cx st q (groupAnswer σ issued q)).mark = st.mark := by
  classical
  cases q with
  | lin s a b u w =>
    have hx := resolve_projects pp v σ st sh h s u
    have hy := resolve_projects pp v σ st _ hx s w
    cases hr : groupAnswer σ issued (.lin s a b u w) with
    | none =>
      cases hp : (resolve pp σ sh s u).1 <;>
        cases hq : (resolve pp σ (resolve pp σ sh s u).2 s w).1 <;>
        simpa only [groupIdeal, trEntry, hr, Option.map_none, observeGroup, hp, hq] using
          And.intro hy (Eq.refl st.mark)
    | some l =>
      have hdec : ∃ x y, Algebra.decodeLabel (σ s) u = some x ∧
          Algebra.decodeLabel (σ s) w = some y := by
        cases hu : Algebra.decodeLabel (σ s) u <;>
          cases hw : Algebra.decodeLabel (σ s) w <;> simp [groupAnswer, hu, hw] at hr
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨x, y, hu, hw⟩ := hdec
      obtain ⟨P, hp⟩ := Simulation.resolve_some_of_decode pp σ sh s u x hu
      obtain ⟨Q, hq⟩ := Simulation.resolve_some_of_decode pp σ (resolve pp σ sh s u).2 s w y hw
      have hclear : (insertResult pp (resolve pp σ (resolve pp σ sh s u).2 s w).2 s l
          (scalar pp a * P + scalar pp b * Q)).first = none := by
        simpa only [observeGroup, hp, hq, hr] using hc
      have ha := ((insert_first_none pp _ s l _).mp hclear).2
      cases s with
      | g₁ =>
        have hpc := resolve_coeff pp (Exposure.value1 pp) (map_zero _) st.d1 sh σ .g₁ u h.g1 P hp
        have hqc := resolve_coeff pp (Exposure.value1 pp) (map_zero _) st.d1 _ σ .g₁ w hx.g1 Q hq
        have hh := insert_g1 pp v cx h1 st _ hy l _ _
          (linear_coeff pp (Exposure.value1 pp) a b _ _ P Q hpc hqc) ha
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, observeGroup, hp, hq] using hh
      | g₂ =>
        have hpc := resolve_coeff pp (Exposure.value2 pp v) (map_zero _) st.d2 sh σ .g₂ u h.g2 P hp
        have hqc := resolve_coeff pp (Exposure.value2 pp v) (map_zero _) st.d2 _ σ .g₂ w hx.g2 Q hq
        have hh := insert_g2 pp v cx h2 st _ hy l _ _
          (linear_coeff pp (Exposure.value2 pp v) a b _ _ P Q hpc hqc) ha
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, observeGroup, hp, hq] using hh
      | gₜ =>
        have hpc := resolve_coeff pp (Exposure.valueT pp v) (map_zero _) st.dT sh σ .gₜ u h.gt P hp
        have hqc := resolve_coeff pp (Exposure.valueT pp v) (map_zero _) st.dT _ σ .gₜ w hx.gt Q hq
        have hrec := recordT_projects pp v σ st sh h u w P Q hp hq
        have hh := insert_gt pp v cx hT (recordT st u w) _ hrec l _ _
          (linear_coeff pp (Exposure.valueT pp v) a b _ _ P Q hpc hqc) ha
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, observeGroup, hp, hq, recordT] using hh
  | pair u w =>
    have hx := resolve_projects pp v σ st sh h .g₁ u
    have hy := resolve_projects pp v σ st _ hx .g₂ w
    cases hr : groupAnswer σ issued (.pair u w) with
    | none =>
      cases hp : (resolve pp σ sh .g₁ u).1 <;>
        cases hq : (resolve pp σ (resolve pp σ sh .g₁ u).2 .g₂ w).1 <;>
        simpa only [groupIdeal, trEntry, hr, Option.map_none, observeGroup, hp, hq] using
          And.intro hy (Eq.refl st.mark)
    | some l =>
      have hdec : ∃ x y, Algebra.decodeLabel (σ .g₁) u = some x ∧
          Algebra.decodeLabel (σ .g₂) w = some y := by
        cases hu : Algebra.decodeLabel (σ .g₁) u <;>
          cases hw : Algebra.decodeLabel (σ .g₂) w <;> simp [groupAnswer, hu, hw] at hr
        exact ⟨_, _, rfl, rfl⟩
      obtain ⟨x, y, hu, hw⟩ := hdec
      obtain ⟨P, hp⟩ := Simulation.resolve_some_of_decode pp σ sh .g₁ u x hu
      obtain ⟨Q, hq⟩ := Simulation.resolve_some_of_decode pp σ (resolve pp σ sh .g₁ u).2 .g₂ w y hw
      have ha := ((insert_first_none pp _ .gₜ l (P * Q)).mp
        (show (insertResult pp (resolve pp σ (resolve pp σ sh .g₁ u).2 .g₂ w).2 .gₜ l
          (P * Q)).first = none by simpa only [observeGroup, hp, hq, hr] using hc)).2
      have hpc := resolve_coeff pp (Exposure.value1 pp) (map_zero _) st.d1 sh σ .g₁ u h.g1 P hp
      have hqc := resolve_coeff pp (Exposure.value2 pp v) (map_zero _) st.d2 _ σ .g₂ w hx.g2 Q hq
      have hh := insert_gt pp v cx hT st _ hy l _ (P * Q)
        (by rw [map_mul, hpc, hqc, Exposure.value_pair]) ha
      simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, observeGroup, hp, hq] using hh
  | name u =>
    cases hr : groupAnswer σ issued (.name u) with
    | none => exact ⟨by simpa [groupIdeal, trEntry, observeGroup, hr] using h,
        by simp [groupIdeal, trEntry, hr]⟩
    | some nm =>
      have hu : u ∈ issued := by
        by_contra hu
        simp [groupAnswer, hu] at hr
      obtain ⟨P, hp⟩ := hcover u hu
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
          if_true, hsh] using And.intro h (Eq.refl st.mark)
      · have hclear : (insertResult pp sh .gₜ (otherLabel u (labelName (σ .gₜ) x)) (-P)).first = none := by
          simpa only [observeGroup, hr, hp, Option.getD_some] using hc
        have ha := ((insert_first_none pp sh .gₜ _ (-P)).mp hclear).2
        have hpc := h.gt.1 u
        simp only [hp, Option.getD_some] at hpc
        have hh := insert_gt pp v cx hT
          {st with named := Function.update st.named u true} sh ⟨h.g1, h.g2, h.gt⟩
          _ (-(st.dT u).getD 0) (-P) (by rw [map_neg, hpc, map_neg]) ha
        simpa only [groupIdeal, trEntry, hr, Option.map_some, idealOp, hnamed,
          Bool.false_eq_true, ite_false, observeGroup, hp, Option.getD_some] using hh

@[simp] lemma ideal1_named (cx : IdealCtx P0) (st : IdealState P0) (k : Mark P0)
    (l : Label P0) (E : Expr1 P0) : (ideal1 cx k st l E).named = st.named := by
  unfold ideal1
  split <;> (try split) <;> rfl

@[simp] lemma ideal2_named (cx : IdealCtx P0) (st : IdealState P0) (k : Mark P0)
    (l : Label P0) (E : Expr2 P0) : (ideal2 cx k st l E).named = st.named := by
  unfold ideal2
  split <;> (try split) <;> rfl

@[simp] lemma idealT_named (cx : IdealCtx P0) (st : IdealState P0) (initial : Bool)
    (l : Label P0) (E : ExprT P0) : (idealT cx initial st l E).named = st.named := by
  unfold idealT
  split <;> (try split) <;> rfl

lemma groupIdeal_named (cx : IdealCtx P0) (st : IdealState P0) (q : GQuery P0) (R : q.Result) :
    (groupIdeal cx st q R).named =
      match q, R with
      | .name u, some _ => Function.update st.named u true
      | _, _ => st.named := by
  classical
  cases q with
  | lin s a b u w => cases R <;> cases s <;> simp [groupIdeal, trEntry, idealOp, recordT]
  | pair u w => cases R <;> simp [groupIdeal, trEntry, idealOp]
  | name u =>
    cases R with
    | none => rfl
    | some nm =>
      by_cases hn : st.named u = true
      · have he : Function.update st.named u true = st.named := by
          funext t
          by_cases ht : t = u <;> simp [ht, hn]
        simp [groupIdeal, trEntry, idealOp, hn, he]
      · simp [groupIdeal, trEntry, idealOp, hn]

lemma insert_clean_entry (sh : State pp) (s : GroupModel.Sorted.PSort) (l : Label P0)
    (P : Poly pp) (hc : (insertResult pp sh s l P).first = none) :
    (insertResult pp sh s l P).dict s l = some P := by
  classical
  cases hd : sh.dict s l with
  | none => simp [insertResult, hd, record]
  | some Q =>
    have hPQ := insertResult_eq_of_no_collision pp sh s l P Q hd hc
    simpa only [insertResult, hd, hPQ, if_true] using hd

lemma group_named (cx : IdealCtx P0) (σ : LabelEncoding P0)
    (st : IdealState P0) (sh : State pp) (hn : Named pp σ st.named sh)
    (issued : Finset (Label P0))
    (hcover : ∀ l ∈ issued, ∃ P, sh.dict .gₜ l = some P)
    (q : GQuery P0)
    (hc : (observeGroup pp σ sh q (groupAnswer σ issued q)).first = none) :
    Named pp σ (groupIdeal cx st q (groupAnswer σ issued q)).named
      (observeGroup pp σ sh q (groupAnswer σ issued q)) := by
  classical
  have hmono := Simulation.observeGroup_mono pp σ sh q (groupAnswer σ issued q)
  have hold := named_mono pp σ st.named sh _ hn hmono
  rw [groupIdeal_named]
  cases q with
  | lin s a b u w => exact hold
  | pair u w => exact hold
  | name u =>
    cases hr : groupAnswer σ issued (.name u) with
    | none => simpa only [hr] using hold
    | some nm =>
      have hu : u ∈ issued := by
        by_contra hu
        simp [groupAnswer, hu] at hr
      obtain ⟨P, hp⟩ := hcover u hu
      have hdec : ∃ x, Algebra.decodeLabel (σ .gₜ) u = some x ∧ nm = labelName (σ .gₜ) x := by
        cases hd : Algebra.decodeLabel (σ .gₜ) u with
        | none => simp [groupAnswer, hu, hd] at hr
        | some x => exact ⟨x, rfl, by simpa [groupAnswer, hu, hd] using hr.symm⟩
      obtain ⟨x, hd, rfl⟩ := hdec
      have hlabel : otherLabel u (labelName (σ .gₜ) x) = σ .gₜ (-x) := by
        rw [← (decodeLabel_eq_some_iff _ _ _).mp hd, otherLabel_name]
      rw [hr] at hold hmono hc

      intro t ht
      by_cases htu : t = u
      · subst t
        refine ⟨P, hmono .gₜ u P hp, ?_⟩
        have hclear : (insertResult pp sh .gₜ (σ .gₜ (-x)) (-P)).first = none := by
          simpa only [observeGroup, hp, Option.getD_some, hlabel] using hc
        have he := insert_clean_entry pp sh .gₜ (σ .gₜ (-x)) (-P) hclear
        simpa only [observeGroup, hp, hd, Option.getD_some, hlabel] using he
      · apply hold t
        simpa only [Function.update_of_ne htu] using ht

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Sync
