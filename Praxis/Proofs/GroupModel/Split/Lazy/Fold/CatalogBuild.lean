import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Catalog
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.CatalogAllocation
import Praxis.Proofs.GroupModel.Init.World
import Praxis.Proofs.GroupModel.Init.Counts
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Catalog

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (pp : PublicParams P0)

def checked (r : Record pp) (e : Collision pp) : Option (Collision pp) :=
  if e.diff.vars ⊆ r.order.toFinset then some e else none

def rawFires {Q : ℕ} : CandidateSlot Q → Record pp → Option (Collision pp)
  | .operation t j, r =>
    match r.pending with
    | some (.inl (.inl (.inr q))) =>
      if groupCount pp r.steps = t.val then
        ((labels pp r ++ operands q)[j.val]?).bind fun v =>
          if v.1 = (newPoly pp r.shadow q).1 then
            checked pp r ⟨v.1,v.2,(newPoly pp r.shadow q).2,oldPoly pp r.shadow v⟩
          else none
      else none
    | _ => none
  | .key j sign, r =>
    ((labels pp r)[j.val]?).bind fun v =>
      if v.1 = .gₜ then
        (r.shadow.dict .gₜ v.2).bind fun P =>
          checked pp r ⟨.gₜ,v.2,if sign.val = 0 then P else scalar pp (-1) * P,key pp⟩
      else none

def cmp (Q : ℕ) (i : Kind) (hi : i = .light ∨ i = .field ∨ i = .guess)
    (j : Fin (quota (simBudget Q) i)) (r : Record pp) : Option (Collision pp) :=
  if h : ∃ a : CandidateSlot Q, a.encode = j.val then rawFires pp h.choose r else none

lemma cmp_at (Q : ℕ) (i : Kind) (hi : i = .light ∨ i = .field ∨ i = .guess)
    (a : CandidateSlot Q) (r : Record pp) :
    cmp pp Q i hi (CandidateSlot.embedding Q i hi a) r = rawFires pp a r := by
  have h : ∃ b : CandidateSlot Q, b.encode = a.encode := ⟨a,rfl⟩
  change (if h : ∃ b : CandidateSlot Q, b.encode = a.encode then rawFires pp h.choose r else none) = _
  rw [dif_pos h]
  exact congrArg (fun b => rawFires pp b r) (CandidateSlot.encode_injective Q h.choose_spec)

lemma labels_cut_prefix (ω : World pp) (n b : ℕ) (h : n ≤ b) :
    labels pp ((fullRecord ω).cut n) <+: labels pp ((fullRecord ω).cut b) := by
  change (keys pp (initialise pp ω.1.out.forms ω.1.out.pv)).toList ++
      laterLabels pp (initialise pp ω.1.out.forms ω.1.out.pv) (ω.2.steps.take n) <+: _
  have hp : ω.2.steps.take n <+: ω.2.steps.take b := List.take_prefix_take_left h
  obtain ⟨zs,hzs⟩ := hp
  change _ <+: (keys pp (initialise pp ω.1.out.forms ω.1.out.pv)).toList ++
      laterLabels pp (initialise pp ω.1.out.forms ω.1.out.pv) (ω.2.steps.take b)
  rw [← hzs,later_append]
  refine ⟨laterLabels pp (lastShadow pp (initialise pp ω.1.out.forms ω.1.out.pv)
    (ω.2.steps.take n)) zs, ?_⟩
  simp only [List.append_assoc]

lemma labels_cut_get (ω : World pp) (n b j : ℕ) (h : n ≤ b) (v : GuessVar)
    (hv : (labels pp ((fullRecord ω).cut n))[j]? = some v) :
    (labels pp ((fullRecord ω).cut b))[j]? = some v := by
  obtain ⟨zs,hzs⟩ := labels_cut_prefix pp ω n b h
  rw [← hzs,List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]
  exact hv

lemma shadows_cut_mono (ω : World pp) (n b : ℕ) (h : n ≤ b)
    (hh : History pp ω.1.enc (initialise pp ω.1.out.forms ω.1.out.pv) ω.2.steps ω.2.shadow)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hp : (((fullRecord ω).cut n).shadow).dict s l = some P) :
    (((fullRecord ω).cut b).shadow).dict s l = some P := by
  have hb := history_take pp hh b
  have ht : (ω.2.steps.take b).take n = ω.2.steps.take n := by
    simp only [List.take_take,Nat.min_eq_left h]
  apply history_mono pp hb n s l P
  simpa only [ht,Record.shadow,FullRecord.cut,fullRecord,lastShadow] using hp

lemma checked_some (r : Record pp) (e f : Collision pp) :
    checked pp r e = some f ↔ e = f ∧ e.diff.vars ⊆ r.order.toFinset := by
  unfold checked
  split_ifs with h <;> simp_all

lemma key_stable (ω : World pp) (n b : ℕ) (h : n ≤ b)
    (hh : History pp ω.1.enc (initialise pp ω.1.out.forms ω.1.out.pv) ω.2.steps ω.2.shadow)
    {Q : ℕ} (j : Fin (Constants.L + 3*Q)) (sign : Fin 2)
    (e e' : Collision pp)
    (he : rawFires pp (.key j sign) ((fullRecord ω).cut n) = some e)
    (he' : rawFires pp (.key j sign) ((fullRecord ω).cut b) = some e') :
    e.sort = e'.sort ∧ e.diff = e'.diff ∧
      e.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset := by
  simp only [rawFires] at he he'
  obtain ⟨v,hv,he⟩ := Option.bind_eq_some_iff.mp he
  have hs : v.1 = .gₜ := by
    by_contra hn
    rw [if_neg hn] at he
    cases he
  rw [if_pos hs] at he
  obtain ⟨P,hP,he⟩ := Option.bind_eq_some_iff.mp he
  obtain ⟨rfl,hvars⟩ := (checked_some pp _ _ _).mp he
  have hv' := labels_cut_get pp ω n b j.val h v hv
  have hP' := shadows_cut_mono pp ω n b h hh .gₜ v.2 P hP
  rw [hv',Option.bind_some,if_pos hs,hP',Option.bind_some] at he'
  obtain ⟨rfl,hvars'⟩ := (checked_some pp _ _ _).mp he'
  exact ⟨rfl,rfl,hvars⟩

lemma initial_length (ch : AdmissibleChoice P0) (S : Relation P0)
    (m : Msg P0) (A : Adversary P0) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A)) :
    (initialEntries (ppOf ch S) ω.1.out.forms ω.1.out.pv).length = Constants.L := by
  unfold observedRun at hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨σ,hσ,hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨e,he,hω⟩ := hω
  rw [mem_support_bind_iff] at hω
  obtain ⟨z,hz,hω⟩ := hω
  simp only [support_pure,Set.mem_singleton_iff] at hω
  cases hω
  have hv := Praxis.Proofs.GroupModel.encGame_view σ (ppOf ch S) m e he
  simp only [initialEntries,List.length_append,List.length_map,hv,
    Praxis.Proofs.GroupModel.pubView_g1_length_main,Praxis.Proofs.GroupModel.pubView_g2_length_main,
    Praxis.Proofs.GroupModel.pubView_gt_length_main]
  norm_num [Constants.L1,Constants.L2,Constants.LT,Constants.L]

lemma labels_bound (ω : World pp) (b : ℕ)
    (hh : History pp ω.1.enc (initialise pp ω.1.out.forms ω.1.out.pv) ω.2.steps ω.2.shadow)
    (hl : (initialEntries pp ω.1.out.forms ω.1.out.pv).length = Constants.L) :
    (labels pp ((fullRecord ω).cut b)).length ≤ Constants.L + 3 * groupCount pp (ω.2.steps.take b) := by
  have hk := initial_keys pp ω.1.out.forms ω.1.out.pv
  rw [hl] at hk
  have hb := history_labels_length pp (history_take pp hh b)
  change ((keys pp (initialise pp ω.1.out.forms ω.1.out.pv)).toList ++
      laterLabels pp (initialise pp ω.1.out.forms ω.1.out.pv) (ω.2.steps.take b)).length ≤ _
  simp only [List.length_append,Finset.length_toList]
  omega

lemma labels_contains (ω : World pp) (b : ℕ)
    (hh : History pp ω.1.enc (initialise pp ω.1.out.forms ω.1.out.pv) ω.2.steps ω.2.shadow)
    (v : GuessVar) (hv : ((((fullRecord ω).cut b).shadow).dict v.1 v.2).isSome) :
    v ∈ labels pp ((fullRecord ω).cut b) := by
  exact history_labels_mem pp (history_take pp hh b) v ((mem_keys pp _ _).mpr hv)

lemma before_clean (ω : World pp) (b : ℕ) (hb : ω.2.stop = some b)
    (hclean : Clean b ω) (hstop : StopCorrect pp ω.2) (hlen : b < ω.2.steps.length) :
    (((fullRecord ω).cut b).shadow).first = none := by
  cases b with
  | zero => exact hclean.1
  | succ n =>
    have hn : n < ω.2.steps.length := by omega
    let s := ω.2.steps[n]
    have hs : ω.2.steps[n]? = some s := List.getElem?_eq_getElem hn
    have ht : ω.2.steps.take (n+1) = ω.2.steps.take n ++ [s] := by
      simpa [hs] using (List.take_add_one (l := ω.2.steps) (i := n))
    change (lastShadow pp (initialise pp ω.1.out.forms ω.1.out.pv) (ω.2.steps.take (n+1))).first = none
    rw [ht]
    simp only [lastShadow,List.getLast?_append,List.getLast?_singleton,Option.or_some,
      Option.map_some,Option.getD_some]
    by_contra hf
    have hi : s.shadow.first.isSome := Option.isSome_iff_ne_none.mpr hf
    obtain ⟨b',hb',hle⟩ := hstop.2 n s hs hi
    have he : b' = n+1 := Option.some.inj (hb'.symm.trans hb)
    omega

lemma key_parts (z : WorldOut P0) (sh : State pp) (e : Collision pp)
    (he : keyCmp pp z sh = some e) :
    ∃ (l : Label P0) (P : Poly pp) (sign : Fin 2),
      sh.dict .gₜ l = some P ∧ e.sort = .gₜ ∧
      e.new = (if sign.val = 0 then P else scalar pp (-1) * P) ∧ e.old = key pp := by
  unfold keyCmp at he
  cases hp : sh.dict .gₜ (z.enc .gₜ (kappa pp z.out.coins)) with
  | some P =>
    simp only [hp,Option.some.injEq] at he
    cases he
    exact ⟨_,P,0,hp,rfl,rfl,rfl⟩
  | none =>
    rw [hp] at he
    cases hn : sh.dict .gₜ (z.enc .gₜ (-kappa pp z.out.coins)) with
    | none => simp [hn] at he
    | some P =>
      simp only [hn,Option.some.injEq] at he
      cases he
      exact ⟨_,P,1,hn,rfl,rfl,rfl⟩

lemma operation_first {Q : ℕ} (ω : World pp) (b : ℕ) (t : Fin Q)
    (j : Fin (Constants.L + 3*t.val + 2))
    (ht : t.val = groupCount pp (ω.2.steps.take b)) :
    ∀ n < b, rawFires pp (.operation t j) ((fullRecord ω).cut n) = none := by
  intro n hn
  cases hs : ω.2.steps[n]? with
  | none => simp [rawFires,FullRecord.cut,fullRecord,hs]
  | some s =>
    rcases hq : s.entry.1 with ((u | q) | i) | k
    · simp [rawFires,FullRecord.cut,fullRecord,hs,hq]
    · have hs' : (ω.2.steps.take b)[n]? = some s := by
        rw [List.getElem?_take_of_lt hn]
        exact hs
      have hlt := groupCount_before_lt pp (ω.2.steps.take b) n s hs' q hq
      have htake : (ω.2.steps.take b).take n = ω.2.steps.take n := by
        simp only [List.take_take,Nat.min_eq_left hn.le]
      rw [htake,← ht] at hlt
      simp [rawFires,FullRecord.cut,fullRecord,hs,hq,ne_of_lt hlt]
    · simp [rawFires,FullRecord.cut,fullRecord,hs,hq]
    · simp [rawFires,FullRecord.cut,fullRecord,hs,hq]

lemma catches_operation {Q : ℕ} (ω : World pp) (b : ℕ) (e : Collision pp)
    (hclean : Clean b ω) (t : Fin Q) (j : Fin (Constants.L + 3*t.val + 2))
    (ht : t.val = groupCount pp (ω.2.steps.take b))
    (he : rawFires pp (.operation t j) ((fullRecord ω).cut b) = some e)
    (hvars : e.diff.vars ⊆ ((fullRecord ω).cut b).order.toFinset) :
    Catches (rawFires pp) (.operation t j) ω e := by
  exact ⟨b,hclean,operation_first pp ω b t j ht,e,he,rfl,rfl,hvars⟩

lemma catches_key {Q : ℕ} (ω : World pp) (b : ℕ) (e : Collision pp)
    (hclean : Clean b ω)
    (hh : History pp ω.1.enc (initialise pp ω.1.out.forms ω.1.out.pv) ω.2.steps ω.2.shadow)
    (j : Fin (Constants.L + 3*Q)) (sign : Fin 2)
    (e' : Collision pp) (he' : rawFires pp (.key j sign) ((fullRecord ω).cut b) = some e')
    (hs : e'.sort = e.sort) (hd : e'.diff = e.diff) :
    Catches (rawFires pp) (.key j sign) ω e := by
  have hex : ∃ n, n ≤ b ∧ (rawFires pp (.key j sign) ((fullRecord ω).cut n)).isSome :=
    ⟨b,le_rfl,by rw [he']; rfl⟩
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  obtain ⟨f,hf⟩ := Option.isSome_iff_exists.mp hn.2
  obtain ⟨hsf,hdf,hvars⟩ := key_stable pp ω n b hn.1 hh j sign f e' hf he'
  refine ⟨n,⟨hclean.1,fun b' hb' => hn.1.trans (hclean.2 b' hb')⟩,?_,
    f,hf,hsf.trans hs,hdf.trans hd,hvars⟩
  intro n' hn'
  by_contra hne
  have hi : (rawFires pp (.key j sign) ((fullRecord ω).cut n')).isSome :=
    Option.isSome_iff_ne_none.mpr hne
  exact Nat.find_min hex hn' ⟨hn'.le.trans hn.1,hi⟩

lemma catches_cmp {Q : ℕ} (i : Kind) (hi : i = .light ∨ i = .field ∨ i = .guess)
    (a : CandidateSlot Q) (ω : World pp) (e : Collision pp)
    (h : Catches (rawFires pp) a ω e) :
    Catches (cmp pp Q i hi) (CandidateSlot.embedding Q i hi a) ω e := by
  simpa only [Catches,cmp_at] using h

theorem catalog (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)
    (Q QH : ℕ) (hA : InClass A Q QH)
    (hpvars : ∀ ω ∈ support (observedRun (ppOf ch S) m A),
      ∀ (e : Collision (ppOf ch S)) (b : ℕ), ω.2.stop = some b → badCmp ω = some e →
        e.diff.vars ⊆ ((fullRecord ω).cut b).order.toFinset)
    (i : Kind) (hi : i = .light ∨ i = .field ∨ i = .guess) :
    ∃ cmp : Fin (quota (simBudget Q) i) → Record (ppOf ch S) → Option (Collision (ppOf ch S)),
      ∀ ω ∈ support (observedRun (ppOf ch S) m A), ∀ e, BadAt ω e →
        ∃ j, Catches cmp j ω e := by
  have hhist := observed_history (ppOf ch S) m A
  have hcount := observed_count (ppOf ch S) m A Q hA.group
  have hlength := initial_length ch S m A
  generalize observedRun (ppOf ch S) m A = obs at hpvars hhist hcount hlength ⊢
  refine ⟨cmp (ppOf ch S) Q i hi, ?_⟩
  intro ω hω e he
  obtain ⟨hh,hstop⟩ := hhist ω hω
  have hc := hcount ω hω
  have hl := hlength ω hω
  obtain ⟨b,hb,hclean,hbad⟩ := he
  have hvars := hpvars ω hω e b hb hbad
  unfold badCmp at hbad
  simp only [hb] at hbad
  cases hst : ω.2.steps[b]? with
  | none => simp [hst] at hbad
  | some st =>
    simp only [hst] at hbad
    have hblen := (List.getElem?_eq_some_iff.mp hst).1
    have hf := before_clean (ppOf ch S) ω b hb hclean hstop hblen
    have hnext := history_next (ppOf ch S) hh hst
    change StepRel (ppOf ch S) ω.1.enc (((fullRecord ω).cut b).shadow) st at hnext
    have hlabelbound := labels_bound (ppOf ch S) ω b hh hl
    rcases hq : st.entry.1 with ((u | q) | idx) | kq
    · simp [hq] at hbad
    · simp only [hq] at hbad
      obtain ⟨a,ha⟩ := (show ∃ a, st.shadow = observeGroup (ppOf ch S) ω.1.enc
        (((fullRecord ω).cut b).shadow) q a from by simpa [StepRel,hq] using hnext)
      rw [ha] at hbad
      obtain ⟨hsort,hnew,hold,horigin⟩ := observe_collision (ppOf ch S) ω.1.enc
        (((fullRecord ω).cut b).shadow) q a e hf hbad
      have htlt : groupCount (ppOf ch S) (ω.2.steps.take b) < Q :=
        (groupCount_before_lt (ppOf ch S) ω.2.steps b st hst q hq).trans_le hc
      let t : Fin Q := ⟨groupCount (ppOf ch S) (ω.2.steps.take b),htlt⟩
      let ls := labels (ppOf ch S) ((fullRecord ω).cut b) ++ operands q
      have hmem : (e.sort,e.label) ∈ ls := by
        rcases horigin with ho | ho
        · exact List.mem_append_left _ (labels_contains (ppOf ch S) ω b hh (e.sort,e.label) ho)
        · exact List.mem_append_right _ ho
      have hop : (operands q).length ≤ 2 := by cases q <;> simp [operands]
      have hls : ls.length ≤ Constants.L + 3*t.val + 2 := by
        dsimp only [ls]
        rw [List.length_append]
        dsimp only [t]
        omega
      let j : Fin (Constants.L + 3*t.val + 2) :=
        ⟨ls.idxOf (e.sort,e.label),(List.idxOf_lt_length_iff.mpr hmem).trans_le hls⟩
      have hget : ls[j.val]? = some (e.sort,e.label) := List.getElem?_idxOf hmem
      have hpend : ((fullRecord ω).cut b).pending = some (.inl (.inl (.inr q))) := by
        simp [FullRecord.cut,fullRecord,hst,hq]
      have hfire : rawFires (ppOf ch S) (.operation t j) ((fullRecord ω).cut b) = some e := by
        simp only [rawFires,hpend]
        have hteq : groupCount (ppOf ch S) ((fullRecord ω).cut b).steps = t.val := rfl
        rw [if_pos hteq]
        change (ls[j.val]?).bind _ = _
        rw [hget,Option.bind_some,if_pos hsort]
        have heq : (⟨e.sort,e.label,(newPoly (ppOf ch S) (((fullRecord ω).cut b).shadow) q).2,
            oldPoly (ppOf ch S) (((fullRecord ω).cut b).shadow) (e.sort,e.label)⟩ :
            Collision (ppOf ch S)) = e := by
          rw [← hnew,← hold]
        rw [heq]
        exact (checked_some (ppOf ch S) _ _ _).mpr ⟨rfl,hvars⟩
      refine ⟨CandidateSlot.embedding Q i hi (.operation t j), ?_⟩
      exact catches_cmp (ppOf ch S) i hi _ ω e
        (catches_operation (ppOf ch S) ω b e hclean t j rfl hfire hvars)
    · simp [hq] at hbad
    · simp only [hq] at hbad
      have hshadow : st.shadow = ((fullRecord ω).cut b).shadow := by
        simpa [StepRel,hq] using hnext
      rw [hshadow] at hbad
      obtain ⟨l,P,sign,hP,hsort,hnew,hold⟩ := key_parts (ppOf ch S) ω.1 _ e hbad
      have hmem := labels_contains (ppOf ch S) ω b hh (.gₜ,l)
        (by simp [hP])
      have hle : groupCount (ppOf ch S) (ω.2.steps.take b) ≤ Q :=
        (groupCount_take_le (ppOf ch S) ω.2.steps b).trans hc
      have hls : (labels (ppOf ch S) ((fullRecord ω).cut b)).length ≤ Constants.L + 3*Q := by omega
      let j : Fin (Constants.L + 3*Q) :=
        ⟨(labels (ppOf ch S) ((fullRecord ω).cut b)).idxOf (.gₜ,l),
          (List.idxOf_lt_length_iff.mpr hmem).trans_le hls⟩
      have hget : (labels (ppOf ch S) ((fullRecord ω).cut b))[j.val]? = some (.gₜ,l) :=
        List.getElem?_idxOf hmem
      let e' : Collision (ppOf ch S) := ⟨.gₜ,l,
        if sign.val = 0 then P else scalar (ppOf ch S) (-1)*P,key (ppOf ch S)⟩
      have hd : e'.diff = e.diff := by simp only [Collision.diff,e',hnew,hold]
      have hvars' : e'.diff.vars ⊆ ((fullRecord ω).cut b).order.toFinset := by rw [hd]; exact hvars
      have hfire : rawFires (ppOf ch S) (.key j sign) ((fullRecord ω).cut b) = some e' := by
        rw [rawFires,hget,Option.bind_some,if_pos rfl,hP,Option.bind_some]
        exact (checked_some (ppOf ch S) _ _ _).mpr ⟨rfl,hvars'⟩
      refine ⟨CandidateSlot.embedding Q i hi (.key j sign), ?_⟩
      exact catches_cmp (ppOf ch S) i hi _ ω e
        (catches_key (ppOf ch S) ω b e hclean hh j sign e' hfire hsort.symm hd)

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Catalog
