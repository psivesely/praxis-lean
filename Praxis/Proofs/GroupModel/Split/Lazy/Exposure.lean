import Praxis.Proofs.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic
import Praxis.Enc
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Exposure

open Classical

variable {P : Params} {R : Type} [CommRing R]

abbrev Coordinate (P : Params) := GroupModel.Sorted.PSort × Label P

abbrev Polynomial (P : Params) (R : Type) [CommRing R] :=
  MvPolynomial (Coordinate P) R

abbrev Dictionary (P : Params) (R : Type) [CommRing R] :=
  Label P → Option (Polynomial P R)

def resolve (s : GroupModel.Sorted.PSort) (d : Dictionary P R) (l : Label P) :
    Polynomial P R × Dictionary P R :=
  match d l with
  | some p => (p, d)
  | none => (MvPolynomial.X (s, l), Function.update d l (some (MvPolynomial.X (s, l))))

def issue (d : Dictionary P R) (l : Label P) (p : Polynomial P R) : Dictionary P R :=
  match d l with
  | some _ => d
  | none => Function.update d l (some p)

def Agrees (d : Dictionary P R) (l : Label P) (p : Polynomial P R) : Prop :=
  ∀ q, d l = some q → p = q

lemma resolve_preserves (s : GroupModel.Sorted.PSort) (d : Dictionary P R)
    (l t : Label P) (p : Polynomial P R) (h : d t = some p) :
    (resolve s d l).2 t = some p := by
  unfold resolve
  split
  · exact h
  · rename_i hl
    have htl : t ≠ l := by intro ht; subst t; simp_all
    simpa [htl] using h

lemma resolve_dictionary_projection (s : GroupModel.Sorted.PSort) (d : Dictionary P R)
    (l t : Label P) :
    MvPolynomial.constantCoeff (((resolve s d l).2 t).getD 0) =
      MvPolynomial.constantCoeff ((d t).getD 0) := by
  unfold resolve
  split
  · rfl
  · rename_i hl
    by_cases ht : t = l
    · subst t; simp [hl]
    · simp [ht]

variable {E : Type} [Zero E]

def Projects (value : E → R) (ideal : Label P → Option E) (generic : Dictionary P R) : Prop :=
  (∀ l, MvPolynomial.constantCoeff ((generic l).getD 0) = value ((ideal l).getD 0)) ∧
  (∀ l e, ideal l = some e → ∃ p, generic l = some p)

lemma Projects.resolve {value : E → R} {ideal : Label P → Option E}
    {generic : Dictionary P R} (h : Projects value ideal generic)
    (s : GroupModel.Sorted.PSort) (l : Label P) :
    Projects value ideal (resolve s generic l).2 := by
  constructor
  · intro t
    rw [resolve_dictionary_projection]
    exact h.1 t
  · intro t e he
    obtain ⟨p, hp⟩ := h.2 t e he
    exact ⟨p, resolve_preserves s generic l t p hp⟩

lemma Projects.issued_eq {value : E → R} {ideal : Label P → Option E}
    {generic : Dictionary P R} (h : Projects value ideal generic)
    {l : Label P} {e : E} {p : Polynomial P R}
    (he : ideal l = some e) (hp : Agrees generic l p) :
    MvPolynomial.constantCoeff p = value e := by
  obtain ⟨q, hq⟩ := h.2 l e he
  have hh := h.1 l
  simpa [he, hq, hp q hq] using hh

lemma Projects.insert {value : E → R} {ideal : Label P → Option E}
    {generic : Dictionary P R} (h : Projects value ideal generic)
    (l : Label P) (e : E) (p : Polynomial P R)
    (he : MvPolynomial.constantCoeff p = value e) (hp : Agrees generic l p) :
    Projects value
      (if (ideal l).isSome then ideal else Function.update ideal l (some e))
      (issue generic l p) := by
  constructor
  · intro t
    by_cases ht : t = l
    · subst t
      cases hi : ideal l with
      | none =>
          cases hg : generic l with
          | none => simp [issue, hg, he]
          | some q => simp [issue, hg, ← hp q hg, he]
      | some f =>
          obtain ⟨q, hq⟩ := h.2 l f hi
          simpa [issue, hi, hq] using h.1 l
    · have hg : issue generic l p t = generic t := by
        cases hh : generic l <;> simp [issue, hh, ht]
      have hi : (if (ideal l).isSome then ideal else Function.update ideal l (some e)) t =
          ideal t := by split <;> simp [ht]
      rw [hg, hi]
      exact h.1 t
  · intro t f hf
    by_cases ht : t = l
    · subst t
      cases hg : generic l with
      | none => exact ⟨p, by simp [issue, hg]⟩
      | some q => exact ⟨q, by simp [issue, hg]⟩
    · have htf : ideal t = some f := by
        split at hf
        · exact hf
        · simpa [ht] using hf
      obtain ⟨q, hq⟩ := h.2 t f htf
      unfold issue
      cases hg : generic l with
      | some r => exact ⟨q, hq⟩
      | none => exact ⟨q, by simpa [ht] using hq⟩

lemma ideal1_no_collision (cx : IdealCtx P) (value : Expr1 P → R)
    (hcmp : ∀ E F, value E = value F → cx.eq1 E F)
    (st : IdealState P) {generic : Dictionary P R}
    (h : Projects value st.d1 generic) (mark : Mark P) (l : Label P)
    (F : Expr1 P) (p : Polynomial P R)
    (hf : MvPolynomial.constantCoeff p = value F) (hp : Agrees generic l p) :
    (ideal1 cx mark st l F).mark = st.mark ∧
      Projects value (ideal1 cx mark st l F).d1 (issue generic l p) := by
  have hi := h.insert l F p hf hp
  cases he : st.d1 l with
  | none =>
      constructor
      · simp [ideal1, he]
      · simpa [ideal1, he] using hi
  | some E =>
      have hfe := hcmp F E (hf.symm.trans (h.issued_eq he hp))
      constructor
      · simp [ideal1, he, hfe]
      · simpa [ideal1, he, hfe] using hi

lemma ideal2_no_collision (cx : IdealCtx P) (value : Expr2 P → R)
    (hcmp : ∀ E F, value E = value F → cx.eq2 E F)
    (st : IdealState P) {generic : Dictionary P R}
    (h : Projects value st.d2 generic) (mark : Mark P) (l : Label P)
    (F : Expr2 P) (p : Polynomial P R)
    (hf : MvPolynomial.constantCoeff p = value F) (hp : Agrees generic l p) :
    (ideal2 cx mark st l F).mark = st.mark ∧
      Projects value (ideal2 cx mark st l F).d2 (issue generic l p) := by
  have hi := h.insert l F p hf hp
  cases he : st.d2 l with
  | none =>
      constructor
      · simp [ideal2, he]
      · simpa [ideal2, he] using hi
  | some E =>
      have hfe := hcmp F E (hf.symm.trans (h.issued_eq he hp))
      constructor
      · simp [ideal2, he, hfe]
      · simpa [ideal2, he, hfe] using hi

lemma idealT_no_collision (cx : IdealCtx P) (value : ExprT P → R)
    (hcmp : ∀ E F, value E = value F → cx.eqT E F)
    (st : IdealState P) {generic : Dictionary P R}
    (h : Projects value st.dT generic) (initial : Bool) (l : Label P)
    (F : ExprT P) (p : Polynomial P R)
    (hf : MvPolynomial.constantCoeff p = value F) (hp : Agrees generic l p) :
    (idealT cx initial st l F).mark = st.mark ∧
      Projects value (idealT cx initial st l F).dT (issue generic l p) := by
  have hi := h.insert l F p hf hp
  cases he : st.dT l with
  | none =>
      constructor
      · simp [idealT, he]
      · simpa [idealT, he] using hi
  | some E =>
      have hfe := hcmp F E (hf.symm.trans (h.issued_eq he hp))
      constructor
      · simp [idealT, he, hfe]
      · simpa [idealT, he, hfe] using hi

lemma charged_not_goodMark [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    (w : WorldOut P) (D : ExprT P) (ι : Fq P) (hc : ChargedCmp pp w) :
    ¬ GoodMark pp w D ι := by
  rintro ⟨kg, hkg, hdata, hg⟩
  obtain ⟨kc, hkc, hcharged⟩ := hc
  have hk : kc = kg := Option.some.inj (hkc.symm.trans hkg)
  subst kc
  rcases hcharged with h | h | h | ⟨E, j, hj, hn⟩
  · subst kg; simp [Mark.data] at hdata
  · subst kg; simp [Mark.data] at hdata
  · subst kg; simp [Mark.data] at hdata
  · have hh : (E, j) = (D, ι) := Option.some.inj (hj.symm.trans hdata)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hh
    exact hn hg

lemma idealEvent_absorbs (cx : IdealCtx P) (st : IdealState P)
    (k : Mark P) (hk : st.mark = some k) (e : MonEvent P) :
    idealEvent cx st e = st := by simp [idealEvent, hk]

lemma fold_absorbs (cx : IdealCtx P) (st : IdealState P)
    (k : Mark P) (hk : st.mark = some k) (events : List (MonEvent P)) :
    events.foldl (idealEvent cx) st = st := by
  induction events with
  | nil => rfl
  | cons e es ih =>
      simpa only [List.foldl_cons, idealEvent_absorbs cx st k hk e] using ih

section Values

variable [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    (v : Fin P.n → Vec (Fq P) P.N)

abbrev Coeff := {ω : Assign P // ValidCoins pp.qap ω.coins} → Fq P

def value1 : Expr1 P →ₗ[Fq P] Coeff pp where
  toFun E ω := val1 pp ω.val E
  map_add' E F := by
    funext ω
    simp [val1, add_mul, List.sum_map_add]
  map_smul' a E := by
    funext ω
    simp [val1, smul_eq_mul, mul_assoc, List.sum_map_mul_left]

def value2 : Expr2 P →ₗ[Fq P] Coeff pp where
  toFun E ω := val2 pp v ω.val E
  map_add' E F := by
    funext ω
    simp [val2, add_mul, List.sum_map_add]
  map_smul' a E := by
    funext ω
    simp [val2, smul_eq_mul, mul_assoc, List.sum_map_mul_left]

def valueT : ExprT P →ₗ[Fq P] Coeff pp where
  toFun E ω := valT pp v ω.val E
  map_add' E F := by
    funext ω
    simp [valT, add_mul, List.sum_map_add]
    ring
  map_smul' a E := by
    funext ω
    simp [valT, smul_eq_mul, mul_assoc, List.sum_map_mul_left, mul_add]

def valueKey : Coeff pp := fun ω => kappa pp ω.val.coins

lemma value1_eq_iff (E F : Expr1 P) :
    value1 pp E = value1 pp F ↔ FormalEq1 pp E F := by
  constructor
  · intro h ω hω
    exact congrFun h ⟨ω, hω⟩
  · intro h
    funext ω
    exact h ω.val ω.property

lemma value2_eq_iff (E F : Expr2 P) :
    value2 pp v E = value2 pp v F ↔ FormalEq2 pp v E F := by
  constructor
  · intro h ω hω
    exact congrFun h ⟨ω, hω⟩
  · intro h
    funext ω
    exact h ω.val ω.property

lemma valueT_eq_iff (E F : ExprT P) :
    valueT pp v E = valueT pp v F ↔ FormalEqT pp v E F := by
  constructor
  · intro h ω hω
    exact congrFun h ⟨ω, hω⟩
  · intro h
    funext ω
    exact h ω.val ω.property

lemma valueKey_eq_iff (E : ExprT P) :
    valueT pp v E = valueKey pp ↔ FormalKey pp v E := by
  constructor
  · intro h ω hω
    exact congrFun h ⟨ω, hω⟩
  · intro h
    funext ω
    exact h ω.val ω.property

lemma value_pair (A : Expr1 P) (B : Expr2 P) :
    valueT pp v (pairExpr A B) = value1 pp A * value2 pp v B := by
  funext ω
  change valT pp v ω.val (pairExpr A B) = val1 pp ω.val A * val2 pp v ω.val B
  simp only [valT, pairExpr, zero_mul, add_zero]
  have hm (a : Option (G1Idx P)) (b : Option (G2Idx P)) :
      A a * B b * (e1At pp ω.val a * e2At pp v ω.val b) =
        (A a * e1At pp ω.val a) * (B b * e2At pp v ω.val b) := by ring
  simp_rw [hm, List.sum_map_mul_left]
  rw [List.sum_map_mul_right]
  rfl

end Values

end Praxis.Proofs.GroupModel.Split.Lazy.Exposure
