import Praxis.ExtractorCounted
import Praxis.Extractor
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.IndexSelection

open OracleComp OracleSpec

section NS

variable {q : ℕ} {α β : Type}

def NS (c : UnitComp q α) : Prop := SmallSamples c

theorem ns_pure (a : α) : NS (pure a : UnitComp q α) := trivial

theorem ns_bind {oa : UnitComp q α} {ob : α → UnitComp q β} (h : NS oa) (h' : ∀ x, NS (ob x)) :
    NS (oa >>= ob) := by
  have := isQueryBoundP_bind (p := isLargeSample) (n := 0) (m := 0) h (fun x _ => h' x)
  change IsQueryBoundP (oa >>= ob) isLargeSample 0
  simpa using this

theorem ns_fstep (s : FieldStep q) : NS (fstep s) := by
  unfold NS SmallSamples fstep
  rw [isQueryBoundP_query_iff]
  intro h
  exact absurd h (by simp [isLargeSample])

theorem ns_charge (c : Charge) : NS (charge (q := q) c) := by
  unfold NS SmallSamples charge
  rw [isQueryBoundP_query_iff]
  intro h
  exact absurd h (by simp [isLargeSample])

theorem ns_sampleFin (n : ℕ) (h : n + 1 ≤ 2 ^ unitWordBits) : NS (sampleFin (q := q) n) := by
  unfold NS SmallSamples sampleFin
  rw [isQueryBoundP_query_iff]
  intro h'
  simp only [isLargeSample] at h'
  omega

theorem ns_sampleF (h : q ≤ 2 ^ unitWordBits) : NS (sampleF (q := q)) := by
  unfold sampleF
  refine ns_bind (ns_sampleFin _ ?_) (fun x => ns_pure _)
  have : 1 ≤ 2 ^ unitWordBits := Nat.one_le_two_pow
  omega

theorem ns_mapM {f : α → UnitComp q β} (h : ∀ a, NS (f a)) (l : List α) : NS (l.mapM f) := by
  induction l with
  | nil => exact ns_pure _
  | cons a l ih =>
    rw [List.mapM_cons]
    exact ns_bind (h a) fun b => ns_bind ih fun bs => ns_pure _

theorem ns_foldlM {f : β → α → UnitComp q β} (h : ∀ b a, NS (f b a)) (l : List α) (b : β) :
    NS (l.foldlM f b) := by
  induction l generalizing b with
  | nil => exact ns_pure _
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact ns_bind (h b a) fun b' => ih b'

end NS

section Extractor

variable {P : Params}

theorem ns_vec {q n : ℕ} (f : Fin n → UnitComp q (ZMod q))
    (h : ∀ i, NS (f i)) : NS (vecOfM f) := by
  unfold vecOfM
  exact ns_bind (ns_mapM h _) fun _ => ns_pure _

theorem ns_fun {q : ℕ} {ι β : Type} [DecidableEq ι] (idx : List ι) (d : β)
    (f : ι → UnitComp q β) (h : ∀ i, NS (f i)) : NS (funOfM idx d f) := by
  unfold funOfM
  exact ns_bind (ns_mapM (fun i => ns_bind (h i) fun _ => ns_pure _) _) fun _ => ns_pure _

theorem ns_sum {q : ℕ} (l : List (ZMod q)) : NS (sumC l) := by
  cases l with
  | nil => exact ns_fstep _
  | cons a l => exact ns_foldlM (fun x y => ns_fstep (.add x y)) l a

theorem ns_sumMul {q : ℕ} (l : List (ZMod q × ZMod q)) : NS (sumMulC l) := by
  cases l with
  | nil => exact ns_fstep _
  | cons a l =>
    cases a with
    | mk a b =>
      exact ns_bind (ns_fstep (.mul a b)) fun p => ns_foldlM
        (f := fun (acc : ZMod q) (e : ZMod q × ZMod q) => do
          let t ← fmul e.1 e.2
          fadd acc t) (fun acc e =>
        ns_bind (ns_fstep (.mul e.1 e.2)) fun t => ns_fstep (.add acc t)) l p

theorem ns_linV (a b : Fq P) (A B : Algebra.Vec (Fq P) P.N) : NS (linV a b A B) := by
  exact ns_vec _ fun _ => ns_bind (ns_fstep _) fun _ =>
    ns_bind (ns_fstep _) fun _ => ns_fstep _

theorem ns_addV (A B : Algebra.Vec (Fq P) P.N) : NS (addV A B) := ns_vec _ fun _ => ns_fstep _

theorem ns_subV (A B : Algebra.Vec (Fq P) P.N) : NS (subV A B) := ns_vec _ fun _ => ns_fstep _

theorem ns_negV (A : Algebra.Vec (Fq P) P.N) : NS (negV A) := ns_vec _ fun _ => ns_fstep _

theorem ns_smulV (a : Fq P) (A : Algebra.Vec (Fq P) P.N) : NS (smulV a A) := ns_vec _ fun _ => ns_fstep _

theorem ns_lookup {α : Type} (t : Label P → Option α) (l : Label P) : NS (lookupC t l) :=
  ns_bind (ns_charge _) fun _ => ns_pure _

theorem ns_insert {α : Type} (t : Label P → Option α) (l : Label P) (a : α) : NS (insertC t l a) :=
  ns_bind (ns_charge _) fun _ => ns_pure _

theorem ns_linG1 (a b : Fq P) (A B : Fin P.K1 → Algebra.Vec (Fq P) P.N) : NS (linG1 a b A B) :=
  ns_fun _ _ _ fun _ => ns_linV _ _ _ _

theorem ns_linG2 (a b : Fq P) (A B : Cell P → Fin 3 → Sector → Fq P) : NS (linG2 a b A B) := by
  unfold linG2
  exact ns_bind (ns_fun _ _ _ fun _ => ns_bind (ns_fstep _) fun _ =>
    ns_bind (ns_fstep _) fun _ => ns_fstep _) fun _ => ns_pure _

theorem ns_mapGT (f : Algebra.Vec (Fq P) P.N → UnitComp P.q (Algebra.Vec (Fq P) P.N))
    (h : ∀ x, NS (f x)) (F : Fin 3 → Sector → Algebra.Vec (Fq P) P.N) : NS (mapGT f F) := by
  unfold mapGT
  exact ns_bind (ns_fun _ _ _ fun _ => h _) fun _ => ns_pure _

theorem ns_mapGT2 (f : Algebra.Vec (Fq P) P.N → Algebra.Vec (Fq P) P.N → UnitComp P.q (Algebra.Vec (Fq P) P.N))
    (h : ∀ x y, NS (f x y)) (F G : Fin 3 → Sector → Algebra.Vec (Fq P) P.N) : NS (mapGT2 f F G) := by
  unfold mapGT2
  exact ns_bind (ns_fun _ _ _ fun _ => h _ _) fun _ => ns_pure _

theorem ns_pair (A : Fin P.K1 → Algebra.Vec (Fq P) P.N) (B : Cell P → Fin 3 → Sector → Fq P) : NS (pairC A B) := by
  unfold pairC
  exact ns_bind (ns_fun _ _ _ fun _ => ns_bind (ns_fun _ _ _ fun _ => ns_sum _) fun _ =>
    ns_vec _ fun _ => ns_sumMul _) fun _ => ns_pure _

theorem ns_findPivot (col : Fin (P.N + 1)) (rows : List (Algebra.Vec (Fq P) P.N)) (k : ℕ) :
    NS (findPivotC col rows k) := by
  induction rows generalizing k with
  | nil => exact ns_pure _
  | cons r rs ih =>
    unfold findPivotC
    apply ns_bind (ns_fstep _)
    intro z
    split <;> first | exact ih _ | exact ns_pure _

theorem ns_elim (col : Fin (P.N + 1)) (r w : Algebra.Vec (Fq P) P.N) : NS (elimC col r w) :=
  ns_vec _ fun _ => ns_bind (ns_fstep _) fun _ => ns_fstep _

theorem ns_rref (rows : List (Algebra.Vec (Fq P) P.N)) : NS (rrefC rows) := by
  unfold rrefC
  apply ns_bind (ns_foldlM (fun st col => ?_) _ _) fun _ => ns_pure _
  apply ns_bind (ns_findPivot _ _ _)
  intro opt
  cases opt with
  | none => exact ns_pure _
  | some k =>
    exact ns_bind (ns_fstep _) fun _ => ns_bind (ns_smulV _ _) fun _ =>
      ns_bind (ns_mapM (fun _ => ns_elim _ _ _) _) fun _ =>
      ns_bind (ns_mapM (fun _ => ns_bind (ns_elim _ _ _) fun _ => ns_pure _) _) fun _ => ns_pure _

theorem ns_candidates (basis : List (Fin (P.N + 1) × Algebra.Vec (Fq P) P.N)) : NS (candidatesC basis) := by
  cases basis with
  | nil => exact ns_pure _
  | cons b rest =>
    change NS (if b.1 = 0 then rest.sublists.mapM (fun T => T.foldlM (fun acc r => addV acc r.2) b.2) else pure [])
    split
    · exact ns_mapM (fun _ => ns_foldlM (fun _ _ => ns_addV _ _) _ _) _
    · exact ns_pure _

theorem ns_all {ι : Type} (l : List ι) (f : ι → UnitComp P.q Bool) (h : ∀ i, NS (f i)) : NS (allC l f) := by
  induction l with
  | nil => exact ns_pure _
  | cons a l ih =>
    unfold allC
    apply ns_bind (h a)
    intro b
    split <;> first | exact ih | exact ns_pure _

theorem ns_dot (a : SparseForm P) (x : Algebra.Vec (Fq P) P.N) : NS (dotC a x) := ns_sumMul _

theorem ns_sat (S : SparseRelation P) (x : Algebra.Vec (Fq P) P.N) : NS (satC S x) := by
  unfold satC
  apply ns_bind (ns_fstep _)
  intro h0
  split
  · exact ns_pure _
  · have hall : ∀ i : Fin P.N, NS (do
        let z ← feq (x i.succ) 0
        if z then pure true else feq (x i.succ) 1) := by
      intro i
      apply ns_bind (ns_fstep _)
      intro z
      split <;> first | exact ns_pure _ | exact ns_fstep _
    apply ns_bind (ns_all _ _ hall)
    intro hb
    split
    · exact ns_pure _
    · apply ns_all
      intro t
      exact ns_bind (ns_mapM (f := fun f => do
        let a ← dotC ((S t).left f) x
        let b ← dotC ((S t).right f) x
        fmul a b) (fun f => ns_bind (ns_dot _ _) fun a =>
        ns_bind (ns_dot _ _) fun b => ns_fstep (.mul a b)) _) fun _ =>
        ns_bind (ns_sum _) fun _ => ns_bind (ns_dot _ _) fun _ =>
        ns_bind (ns_fstep _) fun _ => ns_fstep _

theorem ns_first (S : SparseRelation P) (xs : List (Algebra.Vec (Fq P) P.N)) : NS (firstC S xs) := by
  induction xs with
  | nil => exact ns_pure _
  | cons x xs ih =>
    unfold firstC
    apply ns_bind (ns_sat _ _)
    intro b
    split <;> first | exact ns_pure _ | exact ih

theorem ns_testSketches (S : SparseRelation P) (s : Fin 3 → Algebra.Vec (Fq P) P.N) : NS (testSketchesC S s) :=
  ns_bind (ns_rref _) fun _ => ns_bind (ns_candidates _) fun _ => ns_first _ _

theorem ns_testExpr (S : SparseRelation P) (F : Fin 3 → Sector → Algebra.Vec (Fq P) P.N) : NS (testExprC S F) := by
  unfold testExprC
  apply ns_bind (ns_testSketches _ _)
  intro o
  cases o <;> first | exact ns_pure _ | exact ns_testSketches _ _

theorem ns_gtStep (S : SparseRelation P) (st : ExState P) (F : Fin 3 → Sector → Algebra.Vec (Fq P) P.N)
    (res : Label P) : NS (gtStepC S st F res) := by
  unfold gtStepC
  apply ns_bind (ns_lookup _ _)
  intro old
  apply ns_bind (ns_insert _ _ _)
  intro dt
  apply ns_bind (ns_testExpr _ _)
  intro o
  cases o with
  | some x => exact ns_pure _
  | none =>
    cases old with
    | none => exact ns_pure _
    | some E =>
      exact ns_bind (ns_mapGT2 subV (fun _ _ => ns_subV _ _) _ _) fun _ =>
        ns_bind (ns_testExpr _ _) fun _ => ns_pure _

theorem ns_exStep (S : SparseRelation P) (st : ExState P) (op : TrOp P) : NS (exStepC S st op) := by
  unfold exStepC
  split
  · exact ns_pure _
  · cases op with
    | lin sort a b u v res =>
      cases sort <;> simp only
      · exact ns_bind (ns_lookup _ _) fun _ => ns_bind (ns_lookup _ _) fun _ =>
          ns_bind (ns_linG1 _ _ _ _) fun _ => ns_bind (ns_insert _ _ _) fun _ => ns_pure _
      · exact ns_bind (ns_lookup _ _) fun _ => ns_bind (ns_lookup _ _) fun _ =>
          ns_bind (ns_linG2 _ _ _ _) fun _ => ns_bind (ns_insert _ _ _) fun _ => ns_pure _
      · exact ns_bind (ns_lookup _ _) fun _ => ns_bind (ns_lookup _ _) fun _ =>
          ns_bind (ns_mapGT2 (linV _ _) (fun _ _ => ns_linV _ _ _ _) _ _) fun _ => ns_gtStep _ _ _ _
    | pair u v res =>
      exact ns_bind (ns_lookup _ _) fun _ => ns_bind (ns_lookup _ _) fun _ =>
        ns_bind (ns_pair _ _) fun _ => ns_gtStep _ _ _ _
    | name v res =>
      apply ns_bind (ns_charge _)
      intro _
      split
      · exact ns_pure _
      · exact ns_bind (ns_charge _) fun _ => ns_bind (ns_lookup _ _) fun _ =>
          ns_bind (ns_mapGT negV (fun _ => ns_negV _) _) fun _ => ns_gtStep _ _ _ _

theorem ns_draw (hq : P.q ≤ 2 ^ unitWordBits) : NS (drawSketchesC (P := P)) := by
  unfold drawSketchesC
  exact ns_bind (ns_fun _ _ _ fun _ => ns_vec _ fun _ => ns_sampleF hq) fun _ => ns_pure _

theorem ns_initG2 (sk : Sketches P) (i : Option (G2Idx P)) : NS (initG2C sk i) := by
  cases i with
  | none => exact ns_pure _
  | some i =>
    cases i <;> try exact ns_pure _
    unfold initG2C
    exact ns_bind (ns_fun _ _ _ fun _ => ns_sum _) fun _ => ns_pure _

theorem ns_initState (pub : PubView P) (sk : Sketches P) : NS (initStateC pub sk) := by
  unfold initStateC
  exact ns_bind (ns_foldlM (fun _ _ => ns_insert _ _ _) _ _) fun _ =>
    ns_bind (ns_foldlM (fun _ _ => ns_bind (ns_initG2 _ _) fun _ => ns_insert _ _ _) _ _) fun _ =>
    ns_bind (ns_foldlM (fun _ _ => ns_insert _ _ _) _ _) fun _ => ns_pure _

theorem ns_extractor [Fact (Nat.Prime P.q)] (hq : P.q ≤ 2 ^ unitWordBits)
    (S : SparseRelation P) (pub : PubView P) (tr : List (TrOp P)) : NS (extractorC S pub tr) := by
  unfold extractorC
  exact ns_bind (ns_draw hq) fun _ => ns_bind (ns_initState _ _) fun _ =>
    ns_bind (ns_foldlM (fun _ _ => ns_exStep _ _ _) _ _) fun _ => ns_pure _

end Extractor

end Praxis.Proofs.IndexSelection
