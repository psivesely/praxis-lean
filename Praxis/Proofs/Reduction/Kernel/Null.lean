import Praxis.Proofs.Injectivity.Rref
import Praxis.Reduction
import Mathlib.Data.List.GetD

namespace Praxis.Proofs.Reduction

open Praxis.Proofs.Injectivity

section

variable {K : Type*} [Field K] [DecidableEq K] {n : ℕ}

lemma rrefK_eq_rowFull (rs : List (Fin n → K)) :
    rrefK rs = ((List.finRange n).foldl rowStep (rs, [])).2 := rfl

lemma rrefK_span (rs : List (Fin n → K)) :
    rowSpan ((rrefK rs).map Prod.snd) = rowSpan rs := by
  rw [rrefK_eq_rowFull]
  exact rowFull_span rs

lemma rrefK_inv (rs : List (Fin n → K)) :
    (rrefK rs).Pairwise (fun b c => b.1 < c.1) ∧
      (∀ b ∈ rrefK rs, ∀ c ∈ rrefK rs,
        b.2 c.1 = if b.1 = c.1 then 1 else 0) := by
  have h := rowFull_inv rs
  rw [rrefK_eq_rowFull]
  exact ⟨h.ordered, h.reduced⟩

lemma firstNull_some_data (R : List (Fin n × (Fin n → K))) (c : Fin n → K)
    (h : firstNull R = some c) :
    ∃ f : Fin n, (∀ b ∈ R, b.1 ≠ f) ∧
      c = fun i => if i = f then 1 else
        match R.find? (fun b => decide (b.1 = i)) with
        | some b => -(b.2 f)
        | none => 0 := by
  unfold firstNull at h
  split at h
  · contradiction
  next f hf =>
    have hfree : ∀ b ∈ R, b.1 ≠ f := by
      have hh := List.find?_some (p := fun f : Fin n =>
        !(R.any fun b => decide (b.1 = f))) hf
      simpa using hh
    exact ⟨f, hfree, Option.some.inj h.symm⟩

lemma firstNull_some_nonzero (R : List (Fin n × (Fin n → K))) (c : Fin n → K)
    (h : firstNull R = some c) : c ≠ 0 := by
  obtain ⟨f, _, rfl⟩ := firstNull_some_data R c h
  intro hz
  have hh := congrFun hz f
  simpa using hh

lemma ordered_pivot_unique (R : List (Fin n × (Fin n → K)))
    (ho : R.Pairwise (fun b c => b.1 < c.1))
    (b d : Fin n × (Fin n → K)) (hb : b ∈ R) (hd : d ∈ R)
    (he : b.1 = d.1) : b = d := by
  induction R generalizing b d with
  | nil => simp at hb
  | cons a rs ih =>
    have hh := List.pairwise_cons.mp ho
    rcases List.mem_cons.mp hb with hb | hb
    · subst b
      rcases List.mem_cons.mp hd with hd | hd
      · exact hd.symm
      · have ht := hh.1 d hd
        rw [he] at ht
        exact (lt_irrefl _ ht).elim
    · rcases List.mem_cons.mp hd with hd | hd
      · subst d
        have ht := hh.1 b hb
        rw [he] at ht
        exact (lt_irrefl _ ht).elim
      · exact ih hh.2 b d hb hd he

lemma firstNull_kills_rows (R : List (Fin n × (Fin n → K))) (c : Fin n → K)
    (ho : R.Pairwise (fun b c => b.1 < c.1))
    (hr : ∀ b ∈ R, ∀ d ∈ R, b.2 d.1 = if b.1 = d.1 then 1 else 0)
    (h : firstNull R = some c) (b : Fin n × (Fin n → K)) (hb : b ∈ R) :
    ∑ i, b.2 i * c i = 0 := by
  obtain ⟨f, hf, hc⟩ := firstNull_some_data R c h
  have hbf : b.1 ≠ f := hf b hb
  have term (i : Fin n) : b.2 i * c i =
      (if i = f then b.2 f else 0) - (if i = b.1 then b.2 f else 0) := by
    rw [hc]
    by_cases hif : i = f
    · subst i
      simp [Ne.symm hbf]
    · simp only [hif, if_false]
      cases hd : R.find? (fun d => decide (d.1 = i)) with
      | none =>
        have hn : ∀ d ∈ R, d.1 ≠ i := by
          have hh := List.find?_eq_none.mp hd
          simpa using hh
        have hbi : i ≠ b.1 := Ne.symm (hn b hb)
        simp [hbi]
      | some d =>
        have hdm : d ∈ R := List.mem_of_find?_eq_some hd
        have hdi : d.1 = i := of_decide_eq_true
          (List.find?_some (p := fun d : Fin n × (Fin n → K) => decide (d.1 = i)) hd)
        have hri := hr b hb d hdm
        rw [hdi] at hri
        by_cases hbi : i = b.1
        · have hdb : d = b := ordered_pivot_unique R ho d b hdm hb (hdi.trans hbi)
          subst d
          have hbb := hr b hb b hb
          simp [hbi, hbb]
        · have hne : b.1 ≠ i := Ne.symm hbi
          simp [hri, hne, hbi]
  simp_rw [term]
  simp [Finset.sum_sub_distrib]

lemma firstNull_none_zero (R : List (Fin n × (Fin n → K))) (c : Fin n → K)
    (hr : ∀ b ∈ R, ∀ d ∈ R, b.2 d.1 = if b.1 = d.1 then 1 else 0)
    (h : firstNull R = none) (hc : ∀ b ∈ R, ∑ i, b.2 i * c i = 0) : c = 0 := by
  have hall : ∀ i : Fin n, ∃ b ∈ R, b.1 = i := by
    unfold firstNull at h
    split at h
    next hf =>
      intro i
      have hh := List.find?_eq_none.mp hf i (List.mem_finRange i)
      simpa using hh
    next f hf => contradiction
  funext i
  obtain ⟨b, hb, hbi⟩ := hall i
  have hrow (j : Fin n) : b.2 j = if i = j then 1 else 0 := by
    obtain ⟨d, hd, hdj⟩ := hall j
    have hh := hr b hb d hd
    simpa [hbi, hdj] using hh
  have hh := hc b hb
  simpa [hrow, eq_comm] using hh

lemma rowSpan_kills (rs : List (Fin n → K)) (c : Fin n → K)
    (h : ∀ r ∈ rs, ∑ i, r i * c i = 0) (r : Fin n → K)
    (hr : r ∈ rowSpan rs) : ∑ i, r i * c i = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr => exact h r hr
  | zero => simp
  | add x y _ _ hx hy =>
    simpa [add_mul, Finset.sum_add_distrib, hx, hy]
  | smul a x _ hx =>
    simpa [mul_assoc, ← Finset.mul_sum, hx]

lemma firstNull_spec (rs : List (Fin n → K)) :
    ((∃ c, firstNull (rrefK rs) = some c) ↔
      ∃ c : Fin n → K, c ≠ 0 ∧ ∀ r ∈ rs, ∑ i, r i * c i = 0) ∧
    ∀ c, firstNull (rrefK rs) = some c →
      c ≠ 0 ∧ ∀ r ∈ rs, ∑ i, r i * c i = 0 := by
  have hinv := (rrefK_inv rs).2
  have sound : ∀ c, firstNull (rrefK rs) = some c →
      c ≠ 0 ∧ ∀ r ∈ rs, ∑ i, r i * c i = 0 := by
    intro c hc
    refine ⟨firstNull_some_nonzero _ _ hc, ?_⟩
    intro r hr
    refine rowSpan_kills ((rrefK rs).map Prod.snd) c ?_ r ?_
    · intro q hq
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
      exact firstNull_kills_rows _ c (rrefK_inv rs).1 hinv hc b hb
    · rw [rrefK_span]
      exact mem_rowSpan hr
  refine ⟨?_, sound⟩
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, sound c hc⟩
  · rintro ⟨c, hne, hc⟩
    cases hn : firstNull (rrefK rs) with
    | some d => exact ⟨d, rfl⟩
    | none =>
      exfalso
      apply hne
      apply firstNull_none_zero _ c hinv hn
      intro b hb
      apply rowSpan_kills rs c hc b.2
      rw [← rrefK_span]
      exact mem_rowSpan (List.mem_map.mpr ⟨b, hb, rfl⟩)

lemma reduced_indexed_independent (R : List (Fin n × (Fin n → K)))
    (ho : R.Pairwise (fun b c => b.1 < c.1))
    (hr : ∀ b ∈ R, ∀ d ∈ R, b.2 d.1 = if b.1 = d.1 then 1 else 0) :
    LinearIndependent K (fun i : Fin R.length => (R.get i).2) := by
  have hpinj : Function.Injective (fun i : Fin R.length => (R.get i).1) := by
    intro i j hij
    change (R.get i).1 = (R.get j).1 at hij
    rcases lt_trichotomy i j with h | h | h
    · have hh := ho.rel_get_of_lt h
      rw [hij] at hh
      exact (lt_irrefl _ hh).elim
    · exact h
    · have hh := ho.rel_get_of_lt h
      rw [hij] at hh
      exact (lt_irrefl _ hh).elim
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hh := congrFun hc (R.get i).1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh
  have hp (j : Fin R.length) : (R.get j).2 (R.get i).1 = if j = i then 1 else 0 := by
    have ht := hr (R.get j) (List.get_mem _ _) (R.get i) (List.get_mem _ _)
    by_cases hji : j = i
    · subst j
      simpa using ht
    · have hne : (R.get j).1 ≠ (R.get i).1 := fun h => hji (hpinj h)
      rw [if_neg hne] at ht
      simpa [hji] using ht
  simp only [hp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hi, if_true] at hh
  exact hh

lemma indexed_rows_eq (R : List (Fin n × (Fin n → K)))
    (i : Fin (R.map Prod.snd).length) :
    (R.map Prod.snd).getD i.val 0 = (R.get ⟨i.val, by simpa using i.isLt⟩).2 := by
  rw [List.getD_eq_getElem _ _ i.isLt]
  simp

lemma reduced_basis_independent (R : List (Fin n × (Fin n → K)))
    (ho : R.Pairwise (fun b c => b.1 < c.1))
    (hr : ∀ b ∈ R, ∀ d ∈ R, b.2 d.1 = if b.1 = d.1 then 1 else 0) :
    LinearIndependent K (fun i : Fin (R.map Prod.snd).length =>
      (R.map Prod.snd).getD i.val 0) := by
  have hh := (reduced_indexed_independent R ho hr).comp
    (fun i : Fin (R.map Prod.snd).length => (⟨i.val, by simpa using i.isLt⟩ : Fin R.length))
    (by
      intro i j h
      apply Fin.ext
      exact congrArg (fun x : Fin R.length => x.val) h)
  simpa only [Function.comp_def, indexed_rows_eq] using hh

lemma indexed_rows_span (R : List (Fin n × (Fin n → K))) :
    Submodule.span K (Set.range fun i : Fin (R.map Prod.snd).length =>
      (R.map Prod.snd).getD i.val 0) = rowSpan (R.map Prod.snd) := by
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    dsimp only
    rw [indexed_rows_eq]
    exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
  · intro hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
    obtain ⟨i, hi⟩ := List.get_of_mem hb
    refine ⟨⟨i.val, by simpa using i.isLt⟩, ?_⟩
    simpa [indexed_rows_eq] using congrArg Prod.snd hi

end

section Combination

variable {K V : Type*} [Field K] [DecidableEq K] [AddCommGroup V] [Module K V] {k : ℕ}

def combine (B : Fin k → V) (c : Fin k → K) : V := ∑ i, c i • B i

lemma combine_eq_zero (B : Fin k → V) (hB : LinearIndependent K B) (c : Fin k → K)
    (h : combine B c = 0) : c = 0 := by
  funext i
  exact (linearIndependent_iff'.mp hB) Finset.univ c h i (Finset.mem_univ i)

lemma combine_mem (B : Fin k → V) (c : Fin k → K) :
    combine B c ∈ Submodule.span K (Set.range B) := by
  exact (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨c, rfl⟩

lemma combine_map (B : Fin k → V) (c : Fin k → K) (t : V →ₗ[K] K) :
    t (combine B c) = ∑ i, t (B i) * c i := by
  simp [combine, map_sum, map_smul, smul_eq_mul, mul_comm]

theorem combine_null_spec (B : Fin k → V) (hB : LinearIndependent K B)
    (ts : List (V →ₗ[K] K)) :
    let eqs := ts.map (fun t i => t (B i))
    ((∃ v, (firstNull (rrefK eqs)).map (combine B) = some v) ↔
      ∃ v ≠ 0, v ∈ Submodule.span K (Set.range B) ∧ ∀ t ∈ ts, t v = 0) ∧
    ∀ v, (firstNull (rrefK eqs)).map (combine B) = some v →
      v ≠ 0 ∧ v ∈ Submodule.span K (Set.range B) ∧ ∀ t ∈ ts, t v = 0 := by
  dsimp only
  let eqs := ts.map (fun t i => t (B i))
  have hnull := firstNull_spec eqs
  have equiv (c : Fin k → K) :
      (∀ r ∈ eqs, ∑ i, r i * c i = 0) ↔ ∀ t ∈ ts, t (combine B c) = 0 := by
    constructor
    · intro h t ht
      rw [combine_map]
      exact h _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
    · intro h r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      rw [← combine_map]
      exact h t ht
  have sound : ∀ v, (firstNull (rrefK eqs)).map (combine B) = some v →
      v ≠ 0 ∧ v ∈ Submodule.span K (Set.range B) ∧ ∀ t ∈ ts, t v = 0 := by
    intro v hv
    cases hc : firstNull (rrefK eqs) with
    | none => simp [hc] at hv
    | some c =>
      have hv' : combine B c = v := by simpa [hc] using hv
      subst v
      have hh := hnull.2 c hc
      exact ⟨fun hz => hh.1 (combine_eq_zero B hB c hz), combine_mem B c,
        (equiv c).mp hh.2⟩
  refine ⟨?_, sound⟩
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, sound v hv⟩
  · rintro ⟨v, hv, hm, ht⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
    have hcn : c ≠ 0 := by
      intro hz
      subst c
      simp [combine] at hc
      exact hv hc.symm
    have hk : ∀ r ∈ eqs, ∑ i, r i * c i = 0 := (equiv c).mpr (by
      intro t h
      rw [show combine B c = v from hc]
      exact ht t h)
    obtain ⟨d, hd⟩ := hnull.1.mpr ⟨c, hcn, hk⟩
    refine ⟨combine B d, ?_⟩
    change (firstNull (rrefK eqs)).map (combine B) = some (combine B d)
    rw [hd]
    rfl

end Combination

end Praxis.Proofs.Reduction
