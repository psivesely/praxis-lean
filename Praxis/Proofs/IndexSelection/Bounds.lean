import Praxis.Proofs.IndexSelection.Setup
import Praxis.Constants
import Praxis.ExtractorCounted
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.IndexSelection

open Praxis.Algebra (Vec)

open OracleComp

private theorem bound_bind {q : ℕ} {α β : Type} {c : UnitComp q α}
    {f : α → UnitComp q β} {n m : ℕ}
    (hc : WithinUnits c n) (hf : ∀ x, WithinUnits (f x) m) :
    WithinUnits (c >>= f) (n + m) :=
  isQueryBoundP_bind hc (fun x _ => hf x)

private theorem bound_mapM {q : ℕ} {α β : Type} (xs : List α)
    (f : α → UnitComp q β) (k : ℕ) (hf : ∀ x ∈ xs, WithinUnits (f x) k) :
    WithinUnits (xs.mapM f) (xs.length * k) := by
  induction xs with
  | nil => simp [WithinUnits]
  | cons x xs ih =>
    simp only [List.mapM_cons, List.length_cons]
    have h : WithinUnits (do let y ← f x; let ys ← xs.mapM f; pure (y :: ys))
        (k + xs.length * k) := by
      simpa using bound_bind (hf x (by simp)) (fun y =>
        bound_bind (ih (fun z hz => hf z (by simp [hz]))) (fun ys =>
          show WithinUnits (pure (y :: ys)) 0 by simp [WithinUnits]))
    simpa [Nat.succ_mul, Nat.add_comm] using h

private theorem bound_foldlM {q : ℕ} {α β : Type} (xs : List α)
    (f : β → α → UnitComp q β) (k : ℕ)
    (hf : ∀ x ∈ xs, ∀ a, WithinUnits (f a x) k) (init : β) :
    WithinUnits (xs.foldlM f init) (xs.length * k) := by
  induction xs generalizing init with
  | nil => simp [WithinUnits]
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.length_cons]
    have h := bound_bind (hf x (by simp) init) (fun a =>
      ih (fun y hy => hf y (by simp [hy])) a)
    simpa [Nat.succ_mul, Nat.add_comm] using h

private theorem bound_vecOfM {q n : ℕ} (f : Fin n → UnitComp q (ZMod q))
    (k : ℕ) (hf : ∀ i, WithinUnits (f i) k) :
    WithinUnits (vecOfM f) (n * k) := by
  unfold vecOfM
  have h : WithinUnits (do
      let l ← (List.finRange n).mapM f
      pure fun (i : Fin n) => l.getD i.val 0) (n * k) := by
    simpa using bound_bind (bound_mapM (List.finRange n) f k (by simp [hf]))
      (fun l => show WithinUnits (pure (fun (i : Fin n) => l.getD i.val 0)) 0 by simp [WithinUnits])
  simpa using h

private theorem bound_addV {P : Params} (a b : Vec (Fq P) P.N) :
    WithinUnits (addV a b) (P.N + 1) := by
  unfold addV
  simpa using bound_vecOfM _ 1 (fun i => by simp [WithinUnits, fadd, fstep, isUnit])

private theorem bound_smulV {P : Params} (a : Fq P) (b : Vec (Fq P) P.N) :
    WithinUnits (smulV a b) (P.N + 1) := by
  unfold smulV
  simpa using bound_vecOfM _ 1 (fun i => by simp [WithinUnits, fmul, fstep, isUnit])

private theorem bound_elimC {P : Params} (col : Fin (P.N + 1))
    (r w : Vec (Fq P) P.N) : WithinUnits (elimC col r w) (2 * (P.N + 1)) := by
  unfold elimC
  have h := bound_vecOfM (fun i => do
    let t ← fmul (w col) (r i)
    fsub (w i) t) 2 (fun i => by
      have h := bound_bind (show WithinUnits (fmul (w col) (r i)) 1 by
        simp [WithinUnits, fmul, fstep, isUnit]) (fun t =>
          show WithinUnits (fsub (w i) t) 1 by simp [WithinUnits, fsub, fstep, isUnit])
      simpa using h)
  simpa [Nat.mul_comm] using h

private theorem bound_findPivotC {P : Params} (col : Fin (P.N + 1))
    (rows : List (Vec (Fq P) P.N)) (k : ℕ) :
    WithinUnits (findPivotC col rows k) rows.length := by
  induction rows generalizing k with
  | nil => simp [findPivotC, WithinUnits]
  | cons r rs ih =>
    simp only [findPivotC, List.length_cons]
    have h : WithinUnits (do let z ← feq (r col) 0
                             if z then findPivotC col rs (k + 1) else pure (some k))
        (1 + rs.length) := bound_bind (show WithinUnits (feq (r col) 0) 1 by
      simp [WithinUnits, feq, fstep, isUnit]) (fun z => by
        cases z with
        | false => simp [WithinUnits]
        | true => exact ih (k + 1))
    simpa [Nat.add_comm] using h

private theorem bound_allC {q : ℕ} {α : Type} (xs : List α)
    (f : α → UnitComp q Bool) (k : ℕ) (hf : ∀ x ∈ xs, WithinUnits (f x) k) :
    WithinUnits (allC xs f) (xs.length * k) := by
  induction xs with
  | nil => simp [allC, WithinUnits]
  | cons x xs ih =>
    simp only [allC, List.length_cons]
    have h : WithinUnits (do let b ← f x; if b then allC xs f else pure false)
        (k + xs.length * k) := bound_bind (hf x (by simp)) (fun b => by
      cases b with
      | false => simp [WithinUnits]
      | true => exact ih (fun y hy => hf y (by simp [hy])))
    simpa [Nat.succ_mul, Nat.add_mul, Nat.add_comm] using h

private theorem bound_sumC {q : ℕ} (xs : List (ZMod q)) :
    WithinUnits (sumC xs) (xs.length + 1) := by
  cases xs with
  | nil => simp [sumC, WithinUnits, fwrite, fstep, isUnit]
  | cons x xs =>
    simp only [sumC, List.length_cons]
    apply IsQueryBoundP.mono (bound_foldlM xs fadd 1 (by
      intro y hy a
      simp [WithinUnits, fadd, fstep, isUnit]) x)
    omega

private theorem bound_sumMulC {q : ℕ} (xs : List (ZMod q × ZMod q)) :
    WithinUnits (sumMulC xs) (2 * xs.length + 1) := by
  cases xs with
  | nil => simp [sumMulC, WithinUnits, fwrite, fstep, isUnit]
  | cons x xs =>
    simp only [sumMulC, List.length_cons]
    have h := bound_bind (show WithinUnits (fmul x.1 x.2) 1 by
      simp [WithinUnits, fmul, fstep, isUnit]) (fun a =>
        bound_foldlM xs (fun acc e => do
          let t ← fmul e.1 e.2
          fadd acc t) 2 (by
            intro y hy acc
            have h := bound_bind (show WithinUnits (fmul y.1 y.2) 1 by
              simp [WithinUnits, fmul, fstep, isUnit]) (fun t =>
                show WithinUnits (fadd acc t) 1 by
                  simp [WithinUnits, fadd, fstep, isUnit])
            simpa using h) a)
    apply IsQueryBoundP.mono h
    omega

private theorem bound_dotC {P : Params} (a : SparseForm P) (x : Vec (Fq P) P.N) :
    WithinUnits (dotC a x) (2 * a.length + 1) := by
  simpa [dotC] using bound_sumMulC (a.map fun e => (e.2, x e.1))

private theorem bound_mapM_sum {q : ℕ} {α β : Type} (xs : List α)
    (f : α → UnitComp q β) (cost : α → ℕ)
    (hf : ∀ x ∈ xs, WithinUnits (f x) (cost x)) :
    WithinUnits (xs.mapM f) ((xs.map cost).sum) := by
  induction xs with
  | nil => simp [WithinUnits]
  | cons x xs ih =>
    simp only [List.mapM_cons, List.map_cons, List.sum_cons]
    have h : WithinUnits (do let y ← f x; let ys ← xs.mapM f; pure (y :: ys))
        (cost x + (xs.map cost).sum) := by
      simpa using bound_bind (hf x (by simp)) (fun y =>
        bound_bind (ih (fun z hz => hf z (by simp [hz]))) (fun ys =>
          show WithinUnits (pure (y :: ys)) 0 by simp [WithinUnits]))
    simpa [Nat.add_assoc] using h

private theorem bound_allC_sum {q : ℕ} {α : Type} (xs : List α)
    (f : α → UnitComp q Bool) (cost : α → ℕ)
    (hf : ∀ x ∈ xs, WithinUnits (f x) (cost x)) :
    WithinUnits (allC xs f) ((xs.map cost).sum) := by
  induction xs with
  | nil => simp [allC, WithinUnits]
  | cons x xs ih =>
    simp only [allC, List.map_cons, List.sum_cons]
    have h : WithinUnits (do let b ← f x; if b then allC xs f else pure false)
        (cost x + (xs.map cost).sum) := bound_bind (hf x (by simp)) (fun b => by
      cases b with
      | false => simp [WithinUnits]
      | true => exact ih (fun y hy => hf y (by simp [hy])))
    exact h

private theorem support_mapM_length {q : ℕ} {α β : Type} (xs : List α)
    (f : α → UnitComp q β) (ys : List β) (h : ys ∈ support (xs.mapM f)) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa using h
  | cons x xs ih =>
    simp only [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨zs, hz, h⟩ := h
    have heq := eq_of_mem_support_pure (y :: zs) h
    subst ys
    simp [ih zs hz]

private theorem support_findPivotC {P : Params} (col : Fin (P.N + 1))
    (rows : List (Vec (Fq P) P.N)) (k j : ℕ)
    (h : some j ∈ support (findPivotC col rows k)) :
    k ≤ j ∧ j < k + rows.length := by
  induction rows generalizing k with
  | nil => simp [findPivotC] at h
  | cons r rs ih =>
    simp only [findPivotC, mem_support_bind_iff] at h
    obtain ⟨b, _, hb⟩ := h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff,
        Option.some.injEq] at hb
      subst j
      simp
    | true =>
      simp only [↓reduceIte] at hb
      have h' := ih (k + 1) hb
      simp only [List.length_cons]
      omega

private theorem sublists_length_le_four {α : Type} (xs : List α) (h : xs.length ≤ 2) :
    xs.sublists.length ≤ 4 := by
  rw [List.length_sublists]
  interval_cases xs.length <;> decide

private theorem bound_candidatesC {P : Params}
    (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N)) (h : basis.length ≤ 3) :
    WithinUnits (candidatesC basis) (8 * (P.N + 1)) := by
  cases basis with
  | nil => simp [candidatesC, WithinUnits]
  | cons b rest =>
    have hr : rest.length ≤ 2 := by simp only [List.length_cons] at h; omega
    simp only [candidatesC]
    split
    · have hc := bound_mapM rest.sublists
        (fun T => T.foldlM (fun acc r => addV acc r.2) b.2) (2 * (P.N + 1)) (by
          intro T hT
          have hTlen : T.length ≤ 2 := le_trans (List.Sublist.length_le (List.mem_sublists.mp hT)) hr
          apply IsQueryBoundP.mono (bound_foldlM T (fun acc r => addV acc r.2)
            (P.N + 1) (by intro r hr a; exact bound_addV a r.2) b.2)
          exact Nat.mul_le_mul_right _ hTlen)
      apply IsQueryBoundP.mono hc
      have hs := sublists_length_le_four rest hr
      nlinarith
    · simp [WithinUnits]

private theorem support_candidatesC {P : Params}
    (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N)) (h : basis.length ≤ 3)
    (ys : List (Vec (Fq P) P.N)) (hy : ys ∈ support (candidatesC basis)) :
    ys.length ≤ 4 := by
  cases basis with
  | nil =>
    have : ys = [] := by simpa [candidatesC] using hy
    simp [this]
  | cons b rest =>
    have hr : rest.length ≤ 2 := by simp only [List.length_cons] at h; omega
    simp only [candidatesC] at hy
    split at hy
    · rw [support_mapM_length _ _ _ hy]
      exact sublists_length_le_four rest hr
    · have : ys = [] := by simpa using hy
      simp [this]

private def testRrefStep {P : Params}
    (st : List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N))
    (col : Fin (P.N + 1)) :
    UnitComp P.q (List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N)) := do
  match ← findPivotC col st.1 0 with
  | none => pure st
  | some k =>
    let r := st.1.getD k 0
    let piv ← finv (r col)
    let r' ← smulV piv r
    let rest ← (st.1.eraseIdx k).mapM (elimC col r')
    let basis ← st.2.mapM fun b => do
      let v ← elimC col r' b.2
      pure (b.1, v)
    pure (rest, basis ++ [(col, r')])

private theorem bound_firstC {P : Params} (S : SparseRelation P)
    (xs : List (Vec (Fq P) P.N)) (k : ℕ)
    (hs : ∀ x, WithinUnits (satC S x) k) :
    WithinUnits (firstC S xs) (xs.length * k) := by
  induction xs with
  | nil => simp [firstC, WithinUnits]
  | cons x xs ih =>
    simp only [firstC, List.length_cons]
    have h : WithinUnits (do let b ← satC S x
                             if b then pure (some x) else firstC S xs)
        (k + xs.length * k) := bound_bind (hs x) (fun b => by
      cases b with
      | false => exact ih
      | true => simp [WithinUnits])
    simpa [Nat.succ_mul, Nat.add_mul, Nat.add_comm] using h

private theorem support_testRrefStep {P : Params}
    (rows : List (Vec (Fq P) P.N))
    (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N))
    (col : Fin (P.N + 1)) (out) (h : out ∈ support (testRrefStep (rows, basis) col)) :
    out.1.length + out.2.length ≤ rows.length + basis.length := by
  simp only [testRrefStep, mem_support_bind_iff] at h
  obtain ⟨pivot, hp, h⟩ := h
  cases pivot with
  | none =>
    have := eq_of_mem_support_pure (rows, basis) h
    subst out
    simp
  | some k =>
    have hk : k < rows.length := by
      have := support_findPivotC col rows 0 k hp
      simpa using this.2
    simp only [mem_support_bind_iff] at h
    obtain ⟨piv, _, r', _, rest, hrest, bs, hbs, hout⟩ := h
    have hout' := eq_of_mem_support_pure (rest, bs ++ [(col, r')]) hout
    subst out
    have hr := support_mapM_length (rows.eraseIdx k) (elimC col r') rest hrest
    have hb := support_mapM_length basis (fun b => do
      let v ← elimC col r' b.2
      pure (b.1, v)) bs hbs
    have he := List.length_eraseIdx_add_one hk
    simp only [List.length_append, List.length_cons, List.length_nil, Prod.fst, Prod.snd]
    omega

private theorem support_testRrefFold {P : Params}
    (cols : List (Fin (P.N + 1)))
    (st : List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N))
    (out) (h : out ∈ support (cols.foldlM testRrefStep st)) :
    out.1.length + out.2.length ≤ st.1.length + st.2.length := by
  induction cols generalizing st with
  | nil =>
    simp only [List.foldlM_nil] at h
    have := eq_of_mem_support_pure st h
    subst out
    exact le_rfl
  | cons col cols ih =>
    simp only [List.foldlM_cons, mem_support_bind_iff] at h
    obtain ⟨st', hst', hout⟩ := h
    exact le_trans (ih st' hout) (support_testRrefStep st.1 st.2 col st' hst')

private theorem bound_testRrefFold {P : Params} (cols : List (Fin (P.N + 1)))
    (st : List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N))
    (hs : st.1.length + st.2.length ≤ 3) :
    WithinUnits (cols.foldlM testRrefStep st)
      (3 * cols.length + st.1.length * (1 + 5 * (P.N + 1))) := by
  induction cols generalizing st with
  | nil => simp [WithinUnits]
  | cons col cols ih =>
    rcases st with ⟨rows, basis⟩
    simp only [Prod.fst, Prod.snd] at hs ⊢
    have hrows : rows.length ≤ 3 := by omega
    have hpivot : WithinUnits (findPivotC col rows 0) 3 :=
      IsQueryBoundP.mono (bound_findPivotC col rows 0) hrows
    simp only [List.foldlM_cons, testRrefStep, bind_assoc, List.length_cons]
    apply IsQueryBoundP.mono (n := 3 + (3 * cols.length + rows.length * (1 + 5 * (P.N + 1))))
      ?_ (by simp only [Nat.mul_succ]; omega)
    apply isQueryBoundP_bind hpivot
    intro p hp
    cases p with
    | none =>
        simpa only [pure_bind, WithinUnits] using ih (rows, basis) hs
    | some k =>
        simp only [bind_assoc, pure_bind]
        have hk : k < rows.length := by
          have hk := support_findPivotC col rows 0 k hp
          simpa using hk.2
        have he := List.length_eraseIdx_add_one hk
        let r := rows.getD k 0
        have hinv : WithinUnits (finv (r col)) 1 := by
          simp [WithinUnits, finv, fstep, isUnit]
        apply IsQueryBoundP.mono
          (n := 1 + ((P.N + 1) + ((rows.eraseIdx k).length * (2 * (P.N + 1)) +
            (basis.length * (2 * (P.N + 1)) +
              (3 * cols.length + (rows.eraseIdx k).length * (1 + 5 * (P.N + 1)))))))
          ?_ (by nlinarith)
        apply isQueryBoundP_bind hinv
        intro piv hpiv
        apply isQueryBoundP_bind (bound_smulV piv r)
        intro r' hr'
        apply isQueryBoundP_bind (bound_mapM (rows.eraseIdx k) (elimC col r')
          (2 * (P.N + 1)) (by intro w hw; exact bound_elimC col r' w))
        intro rest hrest
        apply isQueryBoundP_bind (bound_mapM basis (fun b => do
          let v ← elimC col r' b.2
          pure (b.1, v)) (2 * (P.N + 1)) (by
            intro b hb
            have h : WithinUnits (do let v ← elimC col r' b.2; pure (b.1, v))
                (2 * (P.N + 1)) := by
              simpa using bound_bind (bound_elimC col r' b.2)
                (fun v => show WithinUnits (pure (b.1, v)) 0 by simp [WithinUnits])
            exact h))
        intro bs hbs
        have hr := support_mapM_length (rows.eraseIdx k) (elimC col r') rest hrest
        have hb := support_mapM_length basis (fun b => do
          let v ← elimC col r' b.2
          pure (b.1, v)) bs hbs
        have hs' : rest.length + (bs ++ [(col, r')]).length ≤ 3 := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        simpa only [pure_bind, hr, WithinUnits] using ih (rest, bs ++ [(col, r')]) hs'

private theorem bound_rrefC {P : Params} (s : Fin 3 → Vec (Fq P) P.N) :
    WithinUnits (rrefC [s 0, s 1, s 2]) (18 * (P.N + 1) + 3) := by
  change WithinUnits
    ((List.finRange (P.N + 1)).foldlM testRrefStep ([s 0, s 1, s 2], []) >>= fun st =>
      pure st.2) _
  have h : WithinUnits
      ((List.finRange (P.N + 1)).foldlM testRrefStep ([s 0, s 1, s 2], []) >>= fun st =>
        pure st.2) (3 * (P.N + 1) + 3 * (1 + 5 * (P.N + 1))) := by
    simpa using bound_bind (bound_testRrefFold (List.finRange (P.N + 1))
      ([s 0, s 1, s 2], []) (by simp))
      (fun st => show WithinUnits (pure st.2) 0 by simp [WithinUnits])
  apply IsQueryBoundP.mono h
  omega

private theorem support_rrefC {P : Params} (s : Fin 3 → Vec (Fq P) P.N)
    (basis) (h : basis ∈ support (rrefC [s 0, s 1, s 2])) : basis.length ≤ 3 := by
  change basis ∈ support ((List.finRange (P.N + 1)).foldlM testRrefStep
    ([s 0, s 1, s 2], []) >>= fun st => pure st.2) at h
  obtain ⟨st, hst, heq⟩ := mem_support_bind_peel _ _ h
  have heq' := eq_of_mem_support_pure st.2 heq
  subst basis
  have hs := support_testRrefFold (List.finRange (P.N + 1)) ([s 0, s 1, s 2], []) st hst
  simp only [Prod.fst, Prod.snd, List.length_cons, List.length_nil, Nat.add_zero] at hs
  omega

private def testGateCost {P : Params} (g : SparseGate P) : ℕ :=
  ((List.finRange g.products).map fun f =>
    (2 * (g.left f).length + 1) + (2 * (g.right f).length + 1) + 1).sum +
    (g.products + 1) + (2 * g.linear.length + 1) + 2

private theorem bound_testGate {P : Params} (g : SparseGate P) (x : Vec (Fq P) P.N) :
    WithinUnits (do
      let prods ← (List.finRange g.products).mapM fun f => do
        let a ← dotC (g.left f) x
        let b ← dotC (g.right f) x
        fmul a b
      let lhs ← sumC prods
      let c ← dotC g.linear x
      let rhs ← fmul (x 0) c
      feq lhs rhs) (testGateCost g) := by
  let f : Fin g.products → UnitComp P.q (Fq P) := fun i => do
    let a ← dotC (g.left i) x
    let b ← dotC (g.right i) x
    fmul a b
  have hf : ∀ i, WithinUnits (f i)
      ((2 * (g.left i).length + 1) + (2 * (g.right i).length + 1) + 1) := by
    intro i
    have h := bound_bind (bound_dotC (g.left i) x) (fun a =>
      bound_bind (bound_dotC (g.right i) x) (fun b =>
        show WithinUnits (fmul a b) 1 by simp [WithinUnits, fmul, fstep, isUnit]))
    simpa [f, Nat.add_assoc] using h
  have h := isQueryBoundP_bind
    (bound_mapM_sum (List.finRange g.products) f _ (by intro i hi; exact hf i))
    (fun prods hp => by
      have hl := support_mapM_length (List.finRange g.products) f prods hp
      simp only [List.length_finRange] at hl
      have hsum : WithinUnits (sumC prods) (g.products + 1) := by
        simpa [hl] using bound_sumC prods
      have hrest := bound_bind hsum (fun lhs =>
        bound_bind (bound_dotC g.linear x) (fun c =>
          bound_bind (show WithinUnits (fmul (x 0) c) 1 by
            simp [WithinUnits, fmul, fstep, isUnit]) (fun rhs =>
              show WithinUnits (feq lhs rhs) 1 by simp [WithinUnits, feq, fstep, isUnit])))
      simpa only [WithinUnits, Nat.add_assoc] using hrest)
  simpa only [testGateCost, f, WithinUnits, Nat.add_assoc] using h

private theorem bound_satC {P : Params} (S : SparseRelation P) (x : Vec (Fq P) P.N) :
    WithinUnits (satC S x)
      (1 + 2 * P.N + ((List.finRange P.gatesMax).map fun t => testGateCost (S t)).sum) := by
  have hb : WithinUnits (allC (List.finRange P.N) fun i => do
      let z ← feq (x i.succ) 0
      if z then pure true else feq (x i.succ) 1) (2 * P.N) := by
    have h := bound_allC (List.finRange P.N) (fun i => do
      let z ← feq (x i.succ) 0
      if z then pure true else feq (x i.succ) 1) 2 (by
        intro i hi
        have h : WithinUnits (do let z ← feq (x i.succ) 0
                                 if z then pure true else feq (x i.succ) 1) (1 + 1) :=
          bound_bind (show WithinUnits (feq (x i.succ) 0) 1 by
          simp [WithinUnits, feq, fstep, isUnit]) (fun z => by
            cases z <;> simp [WithinUnits, feq, fstep, isUnit])
        simpa using h)
    simpa [Nat.mul_comm] using h
  have hg := bound_allC_sum (List.finRange P.gatesMax) (fun t => do
    let prods ← (List.finRange (S t).products).mapM fun f => do
      let a ← dotC ((S t).left f) x
      let b ← dotC ((S t).right f) x
      fmul a b
    let lhs ← sumC prods
    let c ← dotC (S t).linear x
    let rhs ← fmul (x 0) c
    feq lhs rhs) (fun t => testGateCost (S t)) (by
      intro t ht
      exact bound_testGate (S t) x)
  unfold satC
  apply IsQueryBoundP.mono
    (n := 1 + (2 * P.N + ((List.finRange P.gatesMax).map fun t => testGateCost (S t)).sum))
    ?_ (by omega)
  apply isQueryBoundP_bind (show WithinUnits (feq (x 0) 1) 1 by
    simp [WithinUnits, feq, fstep, isUnit])
  intro h0 hh0
  cases h0 with
  | false => simp [WithinUnits]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply isQueryBoundP_bind hb
    intro b hb'
    cases b with
    | false => simp [WithinUnits]
    | true => simpa [WithinUnits] using hg

private theorem length_sparseForm {P : Params} (a : Vec (Fq P) P.N) :
    (sparseForm a).length = formNonzeros a := by
  classical
  have h (xs : List (Fin (P.N + 1))) :
      (xs.filterMap fun i => if a i = 0 then none else some (i, a i)).length =
        (xs.filter fun i => decide (a i ≠ 0)).length := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      by_cases hi : a i = 0 <;> simp [hi, ih]
  rw [sparseForm, h, formNonzeros]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  simp [List.toFinset_filter]

private theorem sum_finRange {n : ℕ} (f : Fin n → ℕ) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n), List.toFinset_finRange]

private theorem gateCost_sparseOf {P : Params} (S : Relation P) (t : Fin P.gatesMax) :
    testGateCost (sparseOf S t) ≤
      2 * (((∑ f, (formNonzeros ((S t).left f) + formNonzeros ((S t).right f))) +
        formNonzeros (S t).linear) + (2 * (S t).products + 1) + (S t).products + 1) := by
  simp only [testGateCost, sparseOf, length_sparseForm, sum_finRange]
  simp only [Finset.sum_add_distrib, Finset.sum_const_zero, Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  simp only [Nat.cast_id, Nat.mul_one]
  omega

private theorem gateCosts_le_size {P : Params} (S : Relation P) :
    ((List.finRange P.gatesMax).map fun t => testGateCost (sparseOf S t)).sum ≤
      2 * size S := by
  rw [sum_finRange]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun t _ => gateCost_sparseOf S t)
  rw [← Finset.mul_sum] at h
  unfold size
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul] at h ⊢
  nlinarith

theorem jset_test (P : Params) (hP : P = P0) (S : Relation P) (hS : InShape P S)
    (s : Fin dimMax → Vec (Fq P) P.N) :
    WithinUnits (testSketchesC (sparseOf S) s)
      (Constants.running_time_extractor_per_sector_test +
        Constants.running_time_extractor_per_sector_test_per_S * size S) := by
  have hs (x : Vec (Fq P) P.N) : WithinUnits (satC (sparseOf S) x)
      (2 * (P.N + 1) + 2 * size S) := by
    apply IsQueryBoundP.mono (bound_satC (sparseOf S) x)
    have h := gateCosts_le_size S
    omega
  have h := isQueryBoundP_bind (bound_rrefC s) (fun basis hb =>
    isQueryBoundP_bind (bound_candidatesC basis (support_rrefC s basis hb)) (fun cs hc => by
      have hcs := support_candidatesC basis (support_rrefC s basis hb) cs hc
      apply IsQueryBoundP.mono (bound_firstC (sparseOf S) cs _ hs)
      exact Nat.mul_le_mul_right _ hcs))
  apply IsQueryBoundP.mono h
  have hN : P.N + 1 = 391694 := by rw [hP]; rfl
  simp only [Constants.running_time_extractor_per_sector_test,
    Constants.running_time_extractor_per_sector_test_per_S]
  omega

end Praxis.Proofs.IndexSelection
