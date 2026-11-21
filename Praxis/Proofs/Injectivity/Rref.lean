import Praxis.Proofs.Basic
import Praxis.Extractor
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

section RowReduction

variable {K : Type*} [Field K] [DecidableEq K] {n : ℕ}

def rowSpan (rs : List (Fin n → K)) : Submodule K (Fin n → K) :=
  Submodule.span K {v | v ∈ rs}

lemma mem_rowSpan {rs : List (Fin n → K)} {v : Fin n → K} (h : v ∈ rs) :
    v ∈ rowSpan rs := Submodule.subset_span h

lemma rowSpan_cons (r : Fin n → K) (rs : List (Fin n → K)) :
    rowSpan (r :: rs) = K ∙ r ⊔ rowSpan rs := by
  simp only [rowSpan, List.mem_cons, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
    Submodule.span_union]

lemma rowSpan_append (rs ss : List (Fin n → K)) :
    rowSpan (rs ++ ss) = rowSpan rs ⊔ rowSpan ss := by
  simp only [rowSpan, List.mem_append, Set.ofPred_or, Submodule.span_union]

lemma rowSpan_nil : rowSpan ([] : List (Fin n → K)) = ⊥ := by
  simp [rowSpan]

lemma rowSpan_perm {rs ss : List (Fin n → K)} (h : rs.Perm ss) :
    rowSpan rs = rowSpan ss := by
  unfold rowSpan
  congr 1
  exact Set.ext (fun v => h.mem_iff)

lemma rowSpan_pivot (r : Fin n → K) (rs : List (Fin n → K)) (col : Fin n)
    (hr : r col ≠ 0) :
    rowSpan (r :: rs) =
      rowSpan (((r col)⁻¹ • r) :: rs.map (fun w => w - w col • ((r col)⁻¹ • r))) := by
  let p := (r col)⁻¹ • r
  let e := fun w : Fin n → K => w - w col • p
  change rowSpan (r :: rs) = rowSpan (p :: rs.map e)
  have hp : p ∈ rowSpan (r :: rs) :=
    Submodule.smul_mem _ _ (mem_rowSpan (by simp))
  have he (w) (hw : w ∈ rs) : e w ∈ rowSpan (r :: rs) :=
    Submodule.sub_mem _ (mem_rowSpan (List.mem_cons_of_mem _ hw)) (Submodule.smul_mem _ _ hp)
  have hnorm : (r col) • p = r := by
    dsimp [p]
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · have hm : w col • p ∈ rowSpan (p :: rs.map e) :=
        Submodule.smul_mem _ _ (mem_rowSpan (List.mem_cons_self ..))
      rwa [hnorm] at hm
    · have hw' : e w ∈ rowSpan (p :: rs.map e) := mem_rowSpan (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, hw, rfl⟩))
      have hp' : p ∈ rowSpan (p :: rs.map e) := mem_rowSpan (by simp)
      have h : w = e w + w col • p := by dsimp [e]; module
      rw [h]
      exact Submodule.add_mem _ hw' (Submodule.smul_mem _ _ hp')
  · apply Submodule.span_le.mpr
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hp
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact he v hv

def rowStep (st : List (Fin n → K) × List (Fin n × (Fin n → K))) (col : Fin n) :
    List (Fin n → K) × List (Fin n × (Fin n → K)) :=
  match st.1.find? (fun r => decide (r col ≠ 0)) with
  | none => st
  | some r =>
    let p := (r col)⁻¹ • r
    let e := fun w : Fin n → K => w - w col • p
    ((st.1.erase r).map e, (st.2.map fun b => (b.1, e b.2)) ++ [(col, p)])

lemma rowStep_span (st : List (Fin n → K) × List (Fin n × (Fin n → K)))
    (col : Fin n) :
    rowSpan ((rowStep st col).1 ++ (rowStep st col).2.map Prod.snd) =
      rowSpan (st.1 ++ st.2.map Prod.snd) := by
  unfold rowStep
  split
  · rfl
  next r h =>
    have hrmem := List.mem_of_find?_eq_some h
    have hr : r col ≠ 0 := of_decide_eq_true (List.find?_some (p := fun r : Fin n → K => decide (r col ≠ 0)) h)
    rw [rowSpan_perm ((List.perm_cons_erase hrmem).append_right (st.2.map Prod.snd))]
    rw [List.cons_append, rowSpan_pivot r _ col hr]
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil]
    simp only [rowSpan_cons, rowSpan_append, rowSpan_nil, sup_bot_eq, bot_sup_eq]
    ac_rfl

structure RowInv (k : ℕ) (st : List (Fin n → K) × List (Fin n × (Fin n → K))) : Prop where
  remaining : ∀ r ∈ st.1, ∀ i : Fin n, i.val < k → r i = 0
  pivots : ∀ b ∈ st.2, b.1.val < k
  ordered : st.2.Pairwise (fun b c => b.1 < c.1)
  leading : ∀ b ∈ st.2, ∀ i : Fin n, i < b.1 → b.2 i = 0
  reduced : ∀ b ∈ st.2, ∀ c ∈ st.2, b.2 c.1 = if b.1 = c.1 then 1 else 0

lemma rowStep_inv (k : ℕ) (st : List (Fin n → K) × List (Fin n × (Fin n → K)))
    (col : Fin n) (hcol : col.val = k) (h : RowInv k st) : RowInv (k + 1) (rowStep st col) := by
  unfold rowStep
  split
  next hf =>
    refine ⟨?_, ?_, h.ordered, h.leading, h.reduced⟩
    · intro r hr i hi
      by_cases hik : i.val < k
      · exact h.remaining r hr i hik
      · have hic : i = col := Fin.ext (by omega)
        subst i
        have hz := List.find?_eq_none.mp hf r hr
        simpa using hz
    · intro b hb
      exact Nat.lt_succ_of_lt (h.pivots b hb)
  next r hf =>
    have hrmem : r ∈ st.1 := List.mem_of_find?_eq_some hf
    have hr : r col ≠ 0 := of_decide_eq_true
      (List.find?_some (p := fun r : Fin n → K => decide (r col ≠ 0)) hf)
    let p := (r col)⁻¹ • r
    let e := fun w : Fin n → K => w - w col • p
    have hpc : p col = 1 := by simp [p, hr]
    have hpi (i : Fin n) (hi : i.val < k) : p i = 0 := by
      simp [p, h.remaining r hrmem i hi]
    have hei (w : Fin n → K) (i : Fin n) (hi : i.val < k) : e w i = w i := by
      simp [e, hpi i hi]
    have hec (w : Fin n → K) : e w col = 0 := by simp [e, hpc]
    change RowInv (k + 1) ((st.1.erase r).map e,
      (st.2.map fun b => (b.1, e b.2)) ++ [(col, p)])
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro w hw i hi
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      by_cases hik : i.val < k
      · rw [hei v i hik]
        exact h.remaining v (List.mem_of_mem_erase hv) i hik
      · have hic : i = col := Fin.ext (by omega)
        subst i
        exact hec v
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        exact Nat.lt_succ_of_lt (h.pivots a ha)
      · simp only [List.mem_singleton] at hb
        subst b
        dsimp
        omega
    · apply List.pairwise_append.mpr
      refine ⟨?_, by simp, ?_⟩
      · exact List.pairwise_map.mpr h.ordered
      · intro b hb c hc
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        simp only [List.mem_singleton] at hc
        subst c
        exact show a.1.val < col.val by rw [hcol]; exact h.pivots a ha
    · intro b hb i hi
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        change e a.2 i = 0
        rw [hei a.2 i (lt_trans hi (h.pivots a ha))]
        exact h.leading a ha i hi
      · simp only [List.mem_singleton] at hb
        subst b
        exact hpi i (by simpa [← hcol] using hi)
    · intro b hb c hc
      rcases List.mem_append.mp hb with hb | hb <;>
        rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        change e a.2 d.1 = if a.1 = d.1 then 1 else 0
        rw [hei a.2 d.1 (h.pivots d hd)]
        exact h.reduced a ha d hd
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        simp only [List.mem_singleton] at hc
        subst c
        have hne : a.1 ≠ col := by intro hh; have := h.pivots a ha; rw [hh, hcol] at this; omega
        simpa [hne] using hec a.2
      · simp only [List.mem_singleton] at hb
        subst b
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
        have hne : col ≠ a.1 := by intro hh; have := h.pivots a ha; rw [← hh, hcol] at this; omega
        simpa [hne] using hpi a.1 (h.pivots a ha)
      · simp only [List.mem_singleton] at hb hc
        subst b
        subst c
        simpa using hpc

lemma rowFold_span (cols : List (Fin n))
    (st : List (Fin n → K) × List (Fin n × (Fin n → K))) :
    rowSpan ((cols.foldl rowStep st).1 ++ (cols.foldl rowStep st).2.map Prod.snd) =
      rowSpan (st.1 ++ st.2.map Prod.snd) := by
  induction cols generalizing st with
  | nil => rfl
  | cons c cs ih => exact (ih (rowStep st c)).trans (rowStep_span st c)

lemma rowFold_inv (cols : List (Fin n)) (k : ℕ)
    (hc : ∀ j (hj : j < cols.length), (cols[j]).val = k + j)
    (st : List (Fin n → K) × List (Fin n × (Fin n → K))) (h : RowInv k st) :
    RowInv (k + cols.length) (cols.foldl rowStep st) := by
  induction cols generalizing k st with
  | nil => simpa using h
  | cons c cs ih =>
    have hhead : c.val = k := by
      have hh := hc 0 (by simp)
      change c.val = k + 0 at hh
      simpa using hh
    have htail : ∀ j (hj : j < cs.length), (cs[j]).val = (k + 1) + j := by
      intro j hj
      have hh := hc (j + 1) (by simpa using Nat.succ_lt_succ hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (k + 1) htail (rowStep st c) (rowStep_inv k st c hhead h)

def reconstruct (bs : List (Fin n × (Fin n → K))) (x : Fin n → K) : Fin n → K :=
  (bs.map fun b => x b.1 • b.2).sum

lemma reconstruct_cons (b : Fin n × (Fin n → K)) (bs : List (Fin n × (Fin n → K)))
    (x : Fin n → K) : reconstruct (b :: bs) x = x b.1 • b.2 + reconstruct bs x := rfl

lemma reconstruct_zero (bs : List (Fin n × (Fin n → K))) : reconstruct bs 0 = 0 := by
  simp [reconstruct]

lemma reconstruct_add (bs : List (Fin n × (Fin n → K))) (x y : Fin n → K) :
    reconstruct bs (x + y) = reconstruct bs x + reconstruct bs y := by
  induction bs with
  | nil => simp [reconstruct]
  | cons b bs ih =>
    simp only [reconstruct_cons, Pi.add_apply, add_smul, ih]
    abel

lemma reconstruct_smul (bs : List (Fin n × (Fin n → K))) (a : K) (x : Fin n → K) :
    reconstruct bs (a • x) = a • reconstruct bs x := by
  induction bs with
  | nil => simp [reconstruct]
  | cons b bs ih => simp only [reconstruct_cons, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul, ih]

lemma reconstruct_row (bs : List (Fin n × (Fin n → K)))
    (ho : bs.Pairwise (fun b c => b.1 < c.1))
    (hr : ∀ b ∈ bs, ∀ c ∈ bs, b.2 c.1 = if b.1 = c.1 then 1 else 0)
    (b) (hb : b ∈ bs) : reconstruct bs b.2 = b.2 := by
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
    have ho' := List.pairwise_cons.mp ho
    have ht : ∀ b ∈ bs, ∀ c ∈ bs, b.2 c.1 = if b.1 = c.1 then 1 else 0 := by
      intro b hb c hc
      exact hr b (by simp [hb]) c (by simp [hc])
    rcases List.mem_cons.mp hb with rfl | hb
    · have hz : reconstruct bs b.2 = 0 := by
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
        have hne : b.1 ≠ c.1 := ne_of_lt (ho'.1 c hc)
        simp [hr b (by simp) c (by simp [hc]), hne]
      simp [reconstruct_cons, hr b (by simp) b (by simp), hz]
    · have hne : b.1 ≠ a.1 := ne_of_gt (ho'.1 b hb)
      simp only [reconstruct_cons, hr b (by simp [hb]) a (by simp), if_neg hne, zero_smul,
        zero_add, ih ho'.2 ht hb]

lemma reconstruct_of_mem (bs : List (Fin n × (Fin n → K)))
    (ho : bs.Pairwise (fun b c => b.1 < c.1))
    (hr : ∀ b ∈ bs, ∀ c ∈ bs, b.2 c.1 = if b.1 = c.1 then 1 else 0)
    (x : Fin n → K) (hx : x ∈ rowSpan (bs.map Prod.snd)) : reconstruct bs x = x := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
    exact reconstruct_row bs ho hr b hb
  | zero => exact reconstruct_zero bs
  | add x y _ _ hx hy => rw [reconstruct_add, hx, hy]
  | smul a x _ hx => rw [reconstruct_smul, hx]

lemma rowSpan_coord_zero (rs : List (Fin n → K)) (i : Fin n)
    (hz : ∀ r ∈ rs, r i = 0) (x : Fin n → K) (hx : x ∈ rowSpan rs) : x i = 0 := by
  induction hx using Submodule.span_induction with
  | mem v hv => exact hz v hv
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

lemma reconstruct_boolean (bs : List (Fin n × (Fin n → K))) (x : Fin n → K)
    (hx : ∀ b ∈ bs, x b.1 = 0 ∨ x b.1 = 1) :
    reconstruct bs x = ((bs.filter fun b => decide (x b.1 = 1)).map Prod.snd).sum := by
  induction bs with
  | nil => simp [reconstruct]
  | cons b bs ih =>
    have ht : ∀ b ∈ bs, x b.1 = 0 ∨ x b.1 = 1 := fun b hb => hx b (by simp [hb])
    rcases hx b (by simp) with hb | hb
    · simp [reconstruct_cons, hb, ih ht]
    · simp [reconstruct_cons, hb, ih ht]

lemma rowFull_inv (rs : List (Fin n → K)) :
    RowInv n ((List.finRange n).foldl rowStep (rs, [])) := by
  have hinit : RowInv 0 (rs, ([] : List (Fin n × (Fin n → K)))) := by
    refine ⟨?_, by simp, by simp, by simp, by simp⟩
    intro r hr i hi
    omega
  have hf := rowFold_inv (List.finRange n) 0 (by
    intro j hj
    simp at hj
    simp) (rs, []) hinit
  simpa using hf

lemma rowFull_span (rs : List (Fin n → K)) :
    rowSpan (((List.finRange n).foldl rowStep (rs, [])).2.map Prod.snd) = rowSpan rs := by
  let st := (List.finRange n).foldl rowStep (rs, ([] : List (Fin n × (Fin n → K))))
  have hi : RowInv n st := rowFull_inv rs
  have hz : rowSpan st.1 = ⊥ := by
    apply le_antisymm ?_ bot_le
    apply Submodule.span_le.mpr
    intro r hr
    change r = 0
    funext i
    exact hi.remaining r hr i i.isLt
  have hs := rowFold_span (List.finRange n) (rs, ([] : List (Fin n × (Fin n → K))))
  change rowSpan (st.1 ++ st.2.map Prod.snd) = rowSpan (rs ++ []) at hs
  simpa [rowSpan_append, hz] using hs

end RowReduction

section Completeness

variable {P : Params} [Fact (Nat.Prime P.q)]

lemma rref_eq_rowFull (rs : List (Algebra.Vec (Fq P) P.N)) :
    rref rs = ((List.finRange (P.N + 1)).foldl rowStep (rs, [])).2 := by
  unfold rref
  congr 2
  funext st col
  unfold rowStep
  split <;> rename_i hf <;> rw [hf]

lemma rref_span (rs : List (Algebra.Vec (Fq P) P.N)) :
    rowSpan ((rref rs).map Prod.snd) = rowSpan rs := by
  rw [rref_eq_rowFull]
  exact rowFull_span rs

lemma rref_invariants (rs : List (Algebra.Vec (Fq P) P.N)) :
    (rref rs).Pairwise (fun b c => b.1 < c.1) ∧
      (∀ b ∈ rref rs, ∀ i, i < b.1 → b.2 i = 0) ∧
      (∀ b ∈ rref rs, ∀ c ∈ rref rs, b.2 c.1 = if b.1 = c.1 then 1 else 0) := by
  have h := rowFull_inv rs
  rw [rref_eq_rowFull]
  exact ⟨h.ordered, h.leading, h.reduced⟩

lemma mem_candidates_rref (rs : List (Algebra.Vec (Fq P) P.N)) (x : Algebra.Vec (Fq P) P.N)
    (hx : x ∈ rowSpan rs) (hx0 : x 0 = 1) (hbool : ∀ i, x i = 0 ∨ x i = 1) :
    x ∈ candidates (rref rs) := by
  have hm : x ∈ rowSpan ((rref rs).map Prod.snd) := by rwa [rref_span]
  obtain ⟨ho, hl, hr⟩ := rref_invariants rs
  have he := reconstruct_of_mem (rref rs) ho hr x hm
  generalize hb : rref rs = bs at hm ho hl hr he ⊢
  cases bs with
  | nil =>
    have hxz : x = 0 := by simpa [reconstruct] using he.symm
    simp [hxz] at hx0
  | cons b bs =>
    have hp : b.1 = 0 := by
      by_contra hp
      have hz : x 0 = 0 := by
        apply rowSpan_coord_zero _ 0 ?_ x hm
        intro r hrmem
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrmem
        apply hl c hc 0
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Fin.pos_iff_ne_zero.mpr hp
        · exact lt_trans (Fin.pos_iff_ne_zero.mpr hp) ((List.pairwise_cons.mp ho).1 c hc)
      rw [hx0] at hz
      exact one_ne_zero hz
    have hsum := reconstruct_boolean bs x (fun b _ => hbool b.1)
    have hxrep : x = b.2 + ((bs.filter fun c => decide (x c.1 = 1)).map Prod.snd).sum := by
      simpa only [reconstruct_cons, hp, hx0, one_smul, hsum] using he.symm
    rw [candidates, if_pos hp, hxrep]
    exact List.mem_map.mpr ⟨_, List.mem_sublists.mpr List.filter_sublist, rfl⟩

end Completeness

end Praxis.Proofs.Injectivity
