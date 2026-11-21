import Praxis.Algebra.Label.Injections

namespace Praxis.Proofs.Names.Reservoir

open OracleComp OracleSpec OracleComp.EvalDist Praxis.Algebra.Label.RefCoupling

open scoped ENNReal

variable {α β H : Type}

theorem unifSet_equiv [Fintype H] [Nonempty H] [DecidableEq H]
    (W : Finset H) (hW : W.Nonempty) (e : H ≃ H)
    (he : ∀ x, e x ∈ W ↔ x ∈ W) :
    evalSPMF (e <$> unifSet W) = evalSPMF (unifSet W) := by
  apply evalSPMF_ext_iff.mpr
  intro y
  have hy : e (e.symm y) = y := e.apply_symm_apply y
  calc
    Pr[= y | e <$> unifSet W] = Pr[= e.symm y | unifSet W] := by
      conv_lhs => rw [← hy]
      exact probOutput_map_injective _ e.injective _
    _ = Pr[= y | unifSet W] := by
      rw [probOutput_unifSet W hW, probOutput_unifSet W hW]
      simp only [← he (e.symm y), hy]

def relabel (e : β ≃ β) : (α ↪ β) ≃ (α ↪ β) :=
  Equiv.embeddingCongr (Equiv.refl α) e

@[simp] theorem relabel_apply (e : β ≃ β) (σ : α ↪ β) (x : α) :
    relabel e σ x = e (σ x) := rfl

def Symmetric [DecidableEq β] (W : Finset (α ↪ β)) (used : Finset β) : Prop :=
  ∀ e : β ≃ β, (∀ t ∈ used, e t = t) → ∀ σ, relabel e σ ∈ W ↔ σ ∈ W

theorem point_mass_eq [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] (W : Finset (α ↪ β)) (hW : W.Nonempty)
    (used : Finset β) (hs : Symmetric W used) (x : α) (a b : β)
    (ha : a ∉ used) (hb : b ∉ used) :
    Pr[fun σ => σ x = a | unifSet W] = Pr[fun σ => σ x = b | unifSet W] := by
  classical
  let e : β ≃ β := Equiv.swap a b
  have he : ∀ t ∈ used, e t = t := by
    intro t ht
    have hta : t ≠ a := fun h => ha (h ▸ ht)
    have htb : t ≠ b := fun h => hb (h ▸ ht)
    simp [e, Equiv.swap_apply_def, hta, htb]
  have h := unifSet_equiv W hW (relabel e) (hs e he)
  calc
    _ = Pr[fun σ => σ x = a | relabel e <$> unifSet W] :=
      (probEvent_congr' (fun _ _ => Iff.rfl) h).symm
    _ = _ := by
      rw [probEvent_map]
      apply probEvent_congr' _ rfl
      intro σ _
      change e (σ x) = a ↔ σ x = b
      rw [← e.eq_symm_apply]
      simp [e]

theorem point_mass [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] (W : Finset (α ↪ β)) (hW : W.Nonempty)
    (used : Finset β) (hs : Symmetric W used) (x : α)
    (hx : ∀ σ ∈ W, σ x ∉ used) (a : β) (ha : a ∉ used) :
    (Pr[fun σ => σ x = a | unifSet W]).toReal =
      1 / ((Fintype.card β - used.card : ℕ) : ℝ) := by
  classical
  let Avail := {t : β // t ∉ used}
  let : Nonempty Avail := ⟨⟨a, ha⟩⟩
  let f : (α ↪ β) → Avail := fun σ =>
    if hσ : σ ∈ W then ⟨σ x, hx σ hσ⟩ else ⟨a, ha⟩
  let comp : ProbComp Avail := f <$> unifSet W
  have hc (b : Avail) : (Pr[= b | comp]).toReal =
      (Pr[fun σ => σ x = a | unifSet W]).toReal := by
    rw [probOutput_map]
    have hb : Pr[fun σ => f σ = b | unifSet W] =
        Pr[fun σ => σ x = b.val | unifSet W] := by
      apply probEvent_congr' _ rfl
      intro σ hσ
      have hw := mem_unifSet_support W hW σ hσ
      change (if hσ : σ ∈ W then (⟨σ x, hx σ hσ⟩ : Avail) else ⟨a, ha⟩) = b ↔ _
      rw [dif_pos hw]
      exact Subtype.ext_iff
    rw [hb, point_mass_eq W hW used hs x b.val a b.property ha]
  have hsum := congrArg ENNReal.toReal (sum_probOutput_eq_one (mx := comp) (by simp))
  rw [ENNReal.toReal_sum (fun _ _ => probOutput_ne_top)] at hsum
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.toReal_one] at hsum
  have hcard : Fintype.card Avail = Fintype.card β - used.card := by
    simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun t : β => t ∈ used)
  rw [hcard] at hsum
  have hpos : (0 : ℝ) < (Fintype.card β - used.card : ℕ) := by
    rw [← hcard]
    exact_mod_cast Fintype.card_pos (α := Avail)
  apply (eq_div_iff (ne_of_gt hpos)).mpr
  nlinarith

theorem point_le [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] (W : Finset (α ↪ β)) (hW : W.Nonempty)
    (used : Finset β) (hs : Symmetric W used) (x : α)
    (hx : ∀ σ ∈ W, σ x ∉ used) (a : β) (R : ℕ) (hR : 0 < R)
    (hsize : R ≤ Fintype.card β - used.card) :
    Pr[fun σ => σ x = a | unifSet W] ≤ (R : ℝ≥0∞)⁻¹ := by
  classical
  by_cases ha : a ∈ used
  · have hz : Pr[fun σ => σ x = a | unifSet W] = 0 := by
      apply probEvent_eq_zero
      intro σ hσ he
      have hh := hx σ (mem_unifSet_support W hW σ hσ)
      rw [he] at hh
      exact hh ha
    rw [hz]
    exact zero_le
  · apply (ENNReal.toReal_le_toReal probEvent_ne_top
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast hR.ne'))).mp
    rw [point_mass W hW used hs x hx a ha]
    simpa [ENNReal.toReal_inv, one_div] using
      one_div_le_one_div_of_le (by exact_mod_cast hR : (0 : ℝ) < R)
        (by exact_mod_cast hsize : (R : ℝ) ≤ (Fintype.card β - used.card : ℕ))

noncomputable def decode (σ : α ↪ β) (t : β) : Option α := by
  classical
  letI : Decidable (∃ x, σ x = t) := Classical.propDecidable _
  exact if h : ∃ x, σ x = t then some (Classical.choose h) else none

theorem decode_some_iff (σ : α ↪ β) (t : β) (x : α) :
    decode σ t = some x ↔ σ x = t := by
  classical
  have : Decidable (∃ y, σ y = t) := Classical.propDecidable _
  by_cases h : ∃ y, σ y = t
  · rw [decode, dif_pos h]
    simp only [Option.some.injEq]
    exact ⟨fun he => he ▸ Classical.choose_spec h,
      fun he => σ.injective ((Classical.choose_spec h).trans he.symm)⟩
  · rw [decode, dif_neg h]
    simp only [reduceCtorEq, false_iff]
    exact fun he => h ⟨x, he⟩

theorem decode_relabel (e : β ≃ β) (σ : α ↪ β) (t : β) (ht : e t = t) :
    decode (relabel e σ) t = decode σ t := by
  classical
  cases hd : decode σ t with
  | some x =>
    apply (decode_some_iff _ _ _).mpr
    simp [relabel_apply, (decode_some_iff σ t x).mp hd, ht]
  | none =>
    cases he : decode (relabel e σ) t with
    | none => rfl
    | some x =>
      have hx := (decode_some_iff _ _ _).mp he
      have hx' : σ x = t := e.injective (by simpa [ht] using hx)
      have hh := (decode_some_iff σ t x).mpr hx'
      rw [hd] at hh
      contradiction

inductive Query (α β : Type)
  | encode (x : α)
  | decode (t : β)

@[reducible] def Query.Answer : Query α β → Type
  | .encode _ => β
  | .decode _ => Option α

instance [DecidableEq α] [DecidableEq β] (q : Query α β) : DecidableEq q.Answer := by
  cases q <;> simp only [Query.Answer] <;> infer_instance

noncomputable def observe (q : Query α β) (σ : α ↪ β) : q.Answer :=
  match q with
  | .encode x => σ x
  | .decode t => decode σ t

def touched (q : Query α β) : q.Answer → β :=
  match q with
  | .encode _ => id
  | .decode t => fun _ => t

theorem symmetric_fibre [DecidableEq α] [DecidableEq β]
    (W : Finset (α ↪ β)) (used : Finset β) (hs : Symmetric W used)
    (q : Query α β) (o : q.Answer) :
    Symmetric (W.filter fun σ => observe q σ = o) (insert (touched q o) used) := by
  classical
  intro e he σ
  have hfix : ∀ t ∈ used, e t = t := fun t ht => he t (Finset.mem_insert_of_mem ht)
  have ht : e (touched q o) = touched q o := he _ (Finset.mem_insert_self _ _)
  simp only [Finset.mem_filter, hs e hfix]
  cases q with
  | encode x =>
    simp only [observe, touched, id_eq] at ht ⊢
    rw [relabel_apply]
    exact and_congr_right fun _ => ⟨fun h => e.injective (h.trans ht.symm), fun h => h ▸ ht⟩
  | decode t =>
    simp only [observe, decode_relabel e σ t ht]

inductive Phase
  | fresh
  | seenLeft
  | seenRight
  | success
  | dead
  deriving DecidableEq

noncomputable def advance [DecidableEq α] (left right : α) (p : Phase)
    (q : Query α β) (o : q.Answer) : Phase :=
  match p with
  | .success => .success
  | .dead => .dead
  | .fresh => match q with
    | .encode x => if x = left ∨ x = right then .dead else .fresh
    | .decode _ => if o = some left then .seenLeft else
        if o = some right then .seenRight else .fresh
  | .seenLeft => match q with
    | .encode x => if x = left ∨ x = right then .dead else .seenLeft
    | .decode _ => if o = some right then .success else .seenLeft
  | .seenRight => match q with
    | .encode x => if x = left ∨ x = right then .dead else .seenRight
    | .decode _ => if o = some left then .success else .seenRight

def Fresh (W : Finset (α ↪ β)) (used : Finset β) (x : α) : Prop :=
  ∀ σ ∈ W, σ x ∉ used

def Unseen (left right : α) (W : Finset (α ↪ β)) (used : Finset β) : Phase → Prop
  | .fresh => Fresh W used left ∧ Fresh W used right
  | .seenLeft => Fresh W used right
  | .seenRight => Fresh W used left
  | .success | .dead => True

theorem fresh_fibre_encode [DecidableEq α] [DecidableEq β]
    (W : Finset (α ↪ β)) (used : Finset β) (x y : α) (hy : Fresh W used y)
    (hxy : y ≠ x) (o : β) :
    Fresh (W.filter fun σ => observe (.encode x) σ = o) (insert o used) y := by
  intro σ hσ
  obtain ⟨hσ, ho⟩ := Finset.mem_filter.mp hσ
  simp only [Finset.mem_insert, not_or]
  refine ⟨?_, hy σ hσ⟩
  intro he
  exact hxy (σ.injective (he.trans ho.symm))

theorem fresh_fibre_decode [DecidableEq α] [DecidableEq β]
    (W : Finset (α ↪ β)) (used : Finset β) (y : α) (hy : Fresh W used y)
    (t : β) (o : Option α) (ho : o ≠ some y) :
    Fresh (W.filter fun σ => observe (.decode t) σ = o) (insert t used) y := by
  intro σ hσ
  obtain ⟨hσ, ht⟩ := Finset.mem_filter.mp hσ
  simp only [Finset.mem_insert, not_or]
  refine ⟨?_, hy σ hσ⟩
  intro he
  exact ho (ht.symm.trans ((decode_some_iff σ t y).mpr he))

theorem unseen_fibre [DecidableEq α] [DecidableEq β]
    (left right : α) (hne : left ≠ right) (W : Finset (α ↪ β)) (used : Finset β)
    (p : Phase) (hu : Unseen left right W used p) (q : Query α β) (o : q.Answer) :
    Unseen left right (W.filter fun σ => observe q σ = o) (insert (touched q o) used)
      (advance left right p q o) := by
  classical
  cases p with
  | success => trivial
  | dead => trivial
  | fresh =>
    obtain ⟨hl, hr⟩ := hu
    cases q with
    | encode x =>
      by_cases hx : x = left ∨ x = right
      · simp [advance, hx, Unseen]
      · simp only [advance, if_neg hx, Unseen, touched, id_eq]
        exact ⟨fresh_fibre_encode W used x left hl (fun he => hx (Or.inl he.symm)) o,
          fresh_fibre_encode W used x right hr (fun he => hx (Or.inr he.symm)) o⟩
    | decode t =>
      by_cases hol : o = some left
      · subst o
        simpa [advance, Unseen, touched] using
          fresh_fibre_decode W used right hr t (some left) (by simpa using hne)
      · by_cases hor : o = some right
        · subst o
          simpa [advance, Unseen, touched, hne.symm] using
            fresh_fibre_decode W used left hl t (some right) (by simpa using hne.symm)
        · simp only [advance, if_neg hol, if_neg hor, Unseen, touched]
          exact ⟨fresh_fibre_decode W used left hl t o hol,
            fresh_fibre_decode W used right hr t o hor⟩
  | seenLeft =>
    cases q with
    | encode x =>
      by_cases hx : x = left ∨ x = right
      · simp [advance, hx, Unseen]
      · simp only [advance, if_neg hx, Unseen, touched, id_eq]
        exact fresh_fibre_encode W used x right hu (fun he => hx (Or.inr he.symm)) o
    | decode t =>
      by_cases ho : o = some right
      · simp [advance, ho, Unseen]
      · simpa [advance, ho, Unseen, touched] using fresh_fibre_decode W used right hu t o ho
  | seenRight =>
    cases q with
    | encode x =>
      by_cases hx : x = left ∨ x = right
      · simp [advance, hx, Unseen]
      · simp only [advance, if_neg hx, Unseen, touched, id_eq]
        exact fresh_fibre_encode W used x left hu (fun he => hx (Or.inl he.symm)) o
    | decode t =>
      by_cases ho : o = some left
      · simp [advance, ho, Unseen]
      · simpa [advance, ho, Unseen, touched] using fresh_fibre_decode W used left hu t o ho

noncomputable def potential (δ : ℝ≥0∞) (n : ℕ) : Phase → ℝ≥0∞
  | .fresh => (n : ℝ≥0∞) ^ 2 * δ ^ 2
  | .seenLeft | .seenRight => n * δ
  | .success => 1
  | .dead => 0

theorem potential_mono (δ : ℝ≥0∞) (p : Phase) {n m : ℕ} (h : n ≤ m) :
    potential δ n p ≤ potential δ m p := by
  cases p <;> simp only [potential] <;> gcongr

theorem advance_encode_potential_le [DecidableEq α] (left right x : α)
    (p : Phase) (o : β) (δ : ℝ≥0∞) (n : ℕ) :
    potential δ n (advance left right p (.encode x) o) ≤ potential δ n p := by
  classical
  cases p <;> simp only [advance, potential]
  all_goals (try split_ifs) <;> simp

theorem expect_decode_one_le [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] (W : Finset (α ↪ β)) (hW : W.Nonempty)
    (used : Finset β) (hs : Symmetric W used) (x : α) (hx : Fresh W used x)
    (t : β) (R n : ℕ) (hR : 0 < R) (hsize : R ≤ Fintype.card β - used.card) :
    expectedValue (unifSet W) (fun σ =>
      if decode σ t = some x then 1 else (n : ℝ≥0∞) * (R : ℝ≥0∞)⁻¹) ≤
        (n + 1 : ℕ) * (R : ℝ≥0∞)⁻¹ := by
  classical
  let δ : ℝ≥0∞ := (R : ℝ≥0∞)⁻¹
  have hp : Pr[fun σ => decode σ t = some x | unifSet W] ≤ δ := by
    simpa only [decode_some_iff] using point_le W hW used hs x hx t R hR hsize
  calc
    _ ≤ expectedValue (unifSet W) (fun σ =>
        (if decode σ t = some x then 1 else 0) + (n : ℝ≥0∞) * δ) := by
      apply expectedValue_mono
      intro σ
      split_ifs <;> simp [δ]
    _ = Pr[fun σ => decode σ t = some x | unifSet W] +
        expectedValue (unifSet W) (fun _ => (n : ℝ≥0∞) * δ) := by
      rw [expectedValue_add, expectedValue_ite_one]
    _ ≤ δ + (n : ℝ≥0∞) * δ :=
      add_le_add hp (expectedValue_le_of_le _ fun _ => le_rfl)
    _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

theorem expect_decode_fresh_le [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] (left right : α)
    (W : Finset (α ↪ β)) (hW : W.Nonempty) (used : Finset β) (hs : Symmetric W used)
    (hl : Fresh W used left) (hr : Fresh W used right)
    (t : β) (R n : ℕ) (hR : 0 < R) (hsize : R ≤ Fintype.card β - used.card) :
    expectedValue (unifSet W) (fun σ =>
      potential (R : ℝ≥0∞)⁻¹ n (advance left right .fresh (.decode t) (decode σ t))) ≤
        potential (R : ℝ≥0∞)⁻¹ (n + 1) .fresh := by
  classical
  let δ : ℝ≥0∞ := (R : ℝ≥0∞)⁻¹
  let hit : (α ↪ β) → Prop := fun σ => decode σ t = some left ∨ decode σ t = some right
  have hp : Pr[hit | unifSet W] ≤ 2 * δ := by
    have hpl : Pr[fun σ => decode σ t = some left | unifSet W] ≤ δ := by
      simpa only [decode_some_iff] using point_le W hW used hs left hl t R hR hsize
    have hpr : Pr[fun σ => decode σ t = some right | unifSet W] ≤ δ := by
      simpa only [decode_some_iff] using point_le W hW used hs right hr t R hR hsize
    exact (probEvent_or_le _ _ _).trans ((add_le_add hpl hpr).trans_eq (two_mul δ).symm)
  calc
    _ ≤ expectedValue (unifSet W) (fun σ =>
        (if hit σ then 1 else 0) * ((n : ℝ≥0∞) * δ) + (n : ℝ≥0∞)^2 * δ^2) := by
      apply expectedValue_mono
      intro σ
      by_cases h1 : decode σ t = some left
      · simp [advance, h1, potential, hit, δ]
      · by_cases h2 : decode σ t = some right
        · by_cases he : right = left
          · exact False.elim (h1 (by simpa [he] using h2))
          · simp [advance, h2, he, potential, hit, δ]
        · simp [advance, h1, h2, potential, hit, δ]
    _ = Pr[hit | unifSet W] * ((n : ℝ≥0∞) * δ) +
        expectedValue (unifSet W) (fun _ => (n : ℝ≥0∞)^2 * δ^2) := by
      rw [expectedValue_add, expectedValue_mul_const, expectedValue_ite_one]
    _ ≤ (2 * δ) * ((n : ℝ≥0∞) * δ) + (n : ℝ≥0∞)^2 * δ^2 :=
      add_le_add (mul_le_mul' hp le_rfl) (expectedValue_le_of_le _ fun _ => le_rfl)
    _ = ((n : ℝ≥0∞)^2 + 2 * n) * δ^2 := by ring
    _ ≤ ((n : ℝ≥0∞) + 1)^2 * δ^2 := by
      gcongr
      exact_mod_cast (show n^2 + 2*n ≤ (n+1)^2 by nlinarith)
    _ = _ := by simp only [potential, Nat.cast_add, Nat.cast_one, δ]

theorem step_potential_le [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] (left right : α)
    (W : Finset (α ↪ β)) (hW : W.Nonempty) (used : Finset β) (hs : Symmetric W used)
    (p : Phase) (hu : Unseen left right W used p) (q : Query α β)
    (R n : ℕ) (hR : 0 < R) (hsize : R ≤ Fintype.card β - used.card) :
    expectedValue (unifSet W) (fun σ =>
      potential (R : ℝ≥0∞)⁻¹ n (advance left right p q (observe q σ))) ≤
        potential (R : ℝ≥0∞)⁻¹ (n + 1) p := by
  classical
  cases q with
  | encode x =>
    exact (expectedValue_le_of_le _ fun σ => advance_encode_potential_le left right x p _ _ n).trans
      (potential_mono _ p (Nat.le_succ n))
  | decode t =>
    cases p with
    | fresh => exact expect_decode_fresh_le left right W hW used hs hu.1 hu.2 t R n hR hsize
    | seenLeft =>
      have he : (fun σ => potential (R : ℝ≥0∞)⁻¹ n
          (advance left right .seenLeft (.decode t) (observe (.decode t) σ))) =
          (fun σ => if decode σ t = some right then 1 else (n : ℝ≥0∞) * (R : ℝ≥0∞)⁻¹) := by
        funext σ
        by_cases h : decode σ t = some right <;> simp [advance, observe, h, potential]
      rw [he]
      exact expect_decode_one_le W hW used hs right hu t R n hR hsize
    | seenRight =>
      have he : (fun σ => potential (R : ℝ≥0∞)⁻¹ n
          (advance left right .seenRight (.decode t) (observe (.decode t) σ))) =
          (fun σ => if decode σ t = some left then 1 else (n : ℝ≥0∞) * (R : ℝ≥0∞)⁻¹) := by
        funext σ
        by_cases h : decode σ t = some left <;> simp [advance, observe, h, potential]
      rw [he]
      exact expect_decode_one_le W hW used hs left hu t R n hR hsize
    | success => exact expectedValue_le_of_le _ fun _ => le_rfl
    | dead => exact expectedValue_le_of_le _ fun _ => le_rfl

@[reducible] def probeModel (α β : Type) : OracleSpec (Query α β) := Query.Answer

@[reducible] def Definitions (α β : Type) := unifSpec + probeModel α β

def isProbe : (Definitions α β).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (@isProbe α β) := fun i => match i with
  | .inl _ => isFalse not_false
  | .inr _ => isTrue trivial

noncomputable def impl [DecidableEq α] (left right : α) (σ : α ↪ β) :
    QueryImpl (Definitions α β) (StateT Phase ProbComp) := by
  let probes : QueryImpl (probeModel α β) (StateT Phase ProbComp) :=
    fun q => StateT.mk fun p => pure (observe q σ, advance left right p q (observe q σ))
  exact ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Phase ProbComp)) + probes

noncomputable def run [DecidableEq α] (left right : α) (σ : α ↪ β)
    {γ : Type} (oa : OracleComp (Definitions α β) γ) (p : Phase) : ProbComp (γ × Phase) :=
  (simulateQ (impl left right σ) oa).run p

@[simp] theorem run_pure [DecidableEq α] (left right : α) (σ : α ↪ β)
    {γ : Type} (a : γ) (p : Phase) : run left right σ (pure a) p = pure (a, p) := rfl

theorem run_coin [DecidableEq α] (left right : α) (σ : α ↪ β)
    {γ : Type} (n : ℕ) (k : Fin (n+1) → OracleComp (Definitions α β) γ) (p : Phase) :
    run left right σ ((liftM ((Definitions α β).query (.inl n)) : OracleComp (Definitions α β) _) >>= k) p =
      ($[0..n] >>= fun u => run left right σ (k u) p) := by
  simp [run, impl, simulateQ_bind, simulateQ_query, StateT.run_bind,
    QueryImpl.liftTarget, monad_norm]
  rfl

theorem run_probe [DecidableEq α] (left right : α) (σ : α ↪ β)
    {γ : Type} (q : Query α β) (k : q.Answer → OracleComp (Definitions α β) γ) (p : Phase) :
    run left right σ ((liftM ((Definitions α β).query (.inr q)) : OracleComp (Definitions α β) _) >>= k) p =
      run left right σ (k (observe q σ)) (advance left right p q (observe q σ)) := by
  simp [run, impl, simulateQ_bind, simulateQ_query, StateT.run_bind, monad_norm]

theorem run_bound [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] (left right : α) (hne : left ≠ right)
    {γ : Type} (oa : OracleComp (Definitions α β) γ) (n : ℕ)
    (hb : IsQueryBoundP oa isProbe n) (W : Finset (α ↪ β)) (hW : W.Nonempty)
    (used : Finset β) (hs : Symmetric W used) (p : Phase) (hu : Unseen left right W used p)
    (R : ℕ) (hR : 0 < R) (hbudget : used.card + n + R ≤ Fintype.card β) :
    Pr[fun z => z.2 = .success | unifSet W >>= fun σ => run left right σ oa p] ≤
      potential (R : ℝ≥0∞)⁻¹ n p := by
  classical
  induction oa using OracleComp.inductionOn generalizing n W used p with
  | pure a =>
    cases p <;> simp [potential, Function.comp_def]
  | query_bind i k ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    rcases i with coin | q
    · have hk (o : Fin (coin+1)) : IsQueryBoundP (k o) isProbe n := by
        simpa [isProbe] using hb.2 o
      simp_rw [run_coin]
      rw [probEvent_bind_bind_swap]
      exact probEvent_bind_le_of_forall_le fun o _ =>
        ih o n (hk o) W hW used hs p hu hbudget
    · have hn : 0 < n := hb.1.resolve_left (by simp [isProbe])
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      have hk (o : q.Answer) : IsQueryBoundP (k o) isProbe m := by
        simpa [isProbe] using hb.2 o
      simp_rw [run_probe]
      have he := unifSet_disintegrate W (observe q)
        (fun o σ => run left right σ (k o) (advance left right p q o))
      rw [probEvent_congr' (fun _ _ => Iff.rfl) he.symm, probEvent_bind_eq_expectedValue]
      calc
        _ ≤ expectedValue (unifSet W) (fun σ =>
            potential (R : ℝ≥0∞)⁻¹ m (advance left right p q (observe q σ))) := by
          apply expectedValue_mono_of_support
          intro σ hσ
          have hw := mem_unifSet_support W hW σ hσ
          have hf : (W.filter fun τ => observe q τ = observe q σ).Nonempty :=
            ⟨σ, by simp [hw]⟩
          have hcard := Finset.card_insert_le (touched q (observe q σ)) used
          exact ih (observe q σ) m (hk _) _ hf _ (symmetric_fibre W used hs q _)
            _ (unseen_fibre left right hne W used p hu q _) (by omega)
        _ ≤ _ := step_potential_le left right W hW used hs p hu q R m hR (by omega)

theorem uniform_run_bound [Fintype α] [Fintype β] [Nonempty (α ↪ β)]
    [DecidableEq α] [DecidableEq β] [SampleableType (α ↪ β)]
    (left right : α) (hne : left ≠ right) {γ : Type} (oa : OracleComp (Definitions α β) γ)
    (n R : ℕ) (hb : IsQueryBoundP oa isProbe n) (hR : 0 < R)
    (hbudget : n + R ≤ Fintype.card β) :
    Pr[fun z => z.2 = .success | ($ᵗ (α ↪ β)) >>= fun σ => run left right σ oa .fresh] ≤
      (n : ℝ≥0∞)^2 * (R : ℝ≥0∞)⁻¹^2 := by
  classical
  have he : evalSPMF ($ᵗ (α ↪ β)) = evalSPMF (unifSet (Finset.univ : Finset (α ↪ β))) := by
    apply evalSPMF_ext_iff.mpr
    intro σ
    simp [probOutput_unifSet _ Finset.univ_nonempty]
  have he' : evalSPMF (($ᵗ (α ↪ β)) >>= fun σ => run left right σ oa .fresh) =
      evalSPMF (unifSet (Finset.univ : Finset (α ↪ β)) >>= fun σ => run left right σ oa .fresh) := by
    simp only [evalSPMF_bind, he]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) he']
  exact run_bound left right hne oa n hb Finset.univ Finset.univ_nonempty ∅
    (by intro e _ σ; simp) .fresh (by simp [Unseen, Fresh]) R hR (by simpa using hbudget)

end Praxis.Proofs.Names.Reservoir
