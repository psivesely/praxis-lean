import Praxis.Proofs.Injectivity.Erasure
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec Praxis.Algebra

variable {P : Params}

theorem run_findPivot (col : Fin (P.N + 1)) (rows : List (Vec (Fq P) P.N)) (k : ℕ) :
    runUnits (findPivotC col rows k) =
      pure (List.findIdx?.go (fun r => decide (r col ≠ 0)) rows k) := by
  induction rows generalizing k with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r col = 0 <;> simp [findPivotC, List.findIdx?.go, h, ih]

theorem erase_of_find {α : Type} [DecidableEq α] (xs : List α) (p : α → Bool) (r : α)
    (h : xs.find? p = some r) : xs.erase r = xs.eraseP p := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : p x = true
    · have hr : x = r := by simpa [List.find?_cons, hx] using h
      subst r
      simp [List.eraseP_cons, hx]
    · have ht : xs.find? p = some r := by simpa [List.find?_cons, hx] using h
      have hne : x ≠ r := by
        intro hr
        subst r
        exact hx (List.find?_some ht)
      simp [List.eraseP_cons, hx, hne, ih ht]

theorem pivot_bridge {α : Type} [DecidableEq α] (xs : List α) (p : α → Bool) (d : α) :
    match xs.findIdx? p with
    | none => xs.find? p = none
    | some k => xs.find? p = some (xs.getD k d) ∧ xs.erase (xs.getD k d) = xs.eraseIdx k := by
  split
  · rename_i h
    simp [List.find?_eq_bind_findIdx?_getElem?, h]
  · rename_i k h
    obtain ⟨hk, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    have hf : xs.find? p = some (xs.getD k d) := by
      simp [List.find?_eq_bind_findIdx?_getElem?, h, List.getD_eq_getElem?_getD, hk]
    exact ⟨hf, by rw [erase_of_find xs p _ hf, List.eraseP_eq_eraseIdx, h]⟩

@[simp] theorem run_elim (col : Fin (P.N + 1)) (r w : Vec (Fq P) P.N) :
    runUnits (elimC col r w) = pure (w - w col • r) := by
  apply run_vecOfM
  intro i; simp

variable [Fact (Nat.Prime P.q)]

def refColumn (st : List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N))
    (col : Fin (P.N + 1)) :
    List (Vec (Fq P) P.N) × List (Fin (P.N + 1) × Vec (Fq P) P.N) :=
  match st.1.find? (fun r => decide (r col ≠ 0)) with
  | none => st
  | some r =>
    let r' := (r col)⁻¹ • r
    let elim := fun w : Vec (Fq P) P.N => w - w col • r'
    ((st.1.erase r).map elim, (st.2.map fun b => (b.1, elim b.2)) ++ [(col, r')])

@[simp] theorem run_rref (rows : List (Vec (Fq P) P.N)) :
    runUnits (rrefC rows) = pure (rref rows) := by
  unfold rrefC rref
  rw [run_bind, run_foldlM _ _ refColumn ?_]
  · simp only [pure_bind, run_pure]; rfl
  · intro col _ st
    unfold refColumn
    rw [run_bind, run_findPivot]
    change (pure (st.1.findIdx? (fun r => decide (r col ≠ 0))) >>= _) = _
    simp only [pure_bind]
    have hb := pivot_bridge st.1 (fun r => decide (r col ≠ 0)) 0
    cases hp : st.1.findIdx? (fun r => decide (r col ≠ 0)) with
    | none => simp only [hp] at hb; rw [hb]; rfl
    | some k =>
      simp only [hp] at hb
      simp only [hb.1]
      simp only [run_bind, run_finv, pure_bind, run_smulV]
      rw [run_mapM _ _ (fun w => w - w col • ((st.1.getD k 0 col)⁻¹ • st.1.getD k 0))
        (by intros; simp)]
      simp only [pure_bind]
      rw [run_mapM _ _ (fun b => (b.1, b.2 - b.2 col • ((st.1.getD k 0 col)⁻¹ • st.1.getD k 0)))
        (by intros; simp)]
      rw [hb.2]
      simp only [pure_bind, run_pure]

@[simp] theorem run_candidates (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N)) :
    runUnits (candidatesC basis) = pure (candidates basis) := by
  cases basis with
  | nil => rfl
  | cons b bs =>
    simp only [candidatesC, candidates]
    split
    · rw [run_mapM _ _ (fun T => b.2 + (T.map Prod.snd).sum) ?_]
      intro T _
      rw [run_foldlM _ _ (fun acc r => acc + r.2) (by intros; simp)]
      congr 1
      simpa [← List.foldl_map] using fold_add (T.map Prod.snd) b.2
    · rfl

@[simp] theorem run_first (S : Relation P) (xs : List (Vec (Fq P) P.N)) :
    runUnits (firstC (sparseOf S) xs) = pure (xs.find? fun x => decide (Sat S x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : Sat S x <;> simp [firstC, List.find?_cons, h, ih]

@[simp] theorem run_testSketches (S : Relation P) (F : Fin 3 → Vec (Fq P) P.N) :
    runUnits (testSketchesC (sparseOf S) F) = pure (testSketches S F) := by
  simp [testSketchesC, testSketches]

@[simp] theorem run_testExpr (S : Relation P) (F : Fin 3 → Sector → Vec (Fq P) P.N) :
    runUnits (testExprC (sparseOf S) F) = pure (testExpr S F) := by
  unfold testExprC testExpr
  simp only [run_bind, run_testSketches, pure_bind]
  cases testSketches S (fun l => F l .plain) <;> simp

@[simp] theorem run_GT_sub (F G : Fin 3 → Sector → Vec (Fq P) P.N) :
    runUnits (mapGT2 subV F G) = pure (F - G) :=
  run_mapGT2 _ (· - ·) run_subV _ _

@[simp] theorem run_GT_lin (a b : Fq P) (F G : Fin 3 → Sector → Vec (Fq P) P.N) :
    runUnits (mapGT2 (linV a b) F G) = pure (a • F + b • G) :=
  run_mapGT2 _ (fun v w => a • v + b • w) (run_linV a b) _ _

@[simp] theorem run_GT_neg (F : Fin 3 → Sector → Vec (Fq P) P.N) :
    runUnits (mapGT negV F) = pure (-F) := run_mapGT _ Neg.neg run_negV _

@[simp] theorem run_gtStep (S : Relation P) (st : ExState P)
    (F : Fin 3 → Sector → Vec (Fq P) P.N) (l : Label P) :
    runUnits (gtStepC (sparseOf S) st F l) = pure (gtStep S st F l) := by
  unfold gtStepC gtStep
  simp only [run_bind, run_lookup, pure_bind, run_insert, run_testExpr]
  cases testExpr S F <;> cases st.dT l <;> simp

@[simp] theorem run_exStep (S : Relation P) (st : ExState P) (op : TrOp P) :
    runUnits (exStepC (sparseOf S) st op) = pure (exStep S st op) := by
  cases hf : st.found with
  | some x => simp [exStepC, exStep, hf]
  | none =>
    cases op with
    | lin sort a b u v l => cases sort <;> simp [exStepC, exStep, hf]
    | pair u v l => simp [exStepC, exStep, hf]
    | name v l => cases hn : st.named v <;> simp [exStepC, exStep, hf, hn]

@[simp] theorem run_initG2 (sk : Sketches P) (i : Option (G2Idx P)) :
    runUnits (initG2C sk i) = pure (initG2 sk i) := by
  cases i with
  | none => rfl
  | some i =>
    cases i with
    | totR1 s leg =>
      unfold initG2C
      rw [run_bind, run_funOfM _ _ _
        (fun e => ((List.finRange (P.N + 1)).map fun j => sk e.1 e.2 s j).sum)
        (by intros; simp)]
      simp only [pure_bind, run_pure]
      congr 1
      funext c l s'
      by_cases hs : s' = s ∧ c.2 = leg
      · have hc : (c, l) ∈ (((cellList P).filter fun c => decide (c.2 = leg)).flatMap fun c =>
            (List.finRange 3).map fun l => (c, l)) := by
          apply List.mem_flatMap.mpr
          exact ⟨c, by simp [hs.2], by simp⟩
        simp only [initG2, hs, ↓reduceIte]
        rw [find_pairs _ _ _ hc]
        simp
      · simp [initG2, hs]
    | _ => rfl

@[simp] theorem run_initState (pub : PubView P) (sk : Sketches P) :
    runUnits (initStateC pub sk) = pure (initState pub sk) := by
  unfold initStateC
  rw [run_bind, run_foldlM _ _ (fun t e => keepEarliest t e.2 (initG1 e.1)) (by intros; simp)]
  simp only [pure_bind]
  rw [run_bind, run_foldlM _ _ (fun t e => keepEarliest t e.2 (initG2 sk e.1)) (by intros; simp)]
  simp only [pure_bind]
  rw [run_bind, run_foldlM _ _ (fun t e => keepEarliest t e.2 0) (by intros; simp)]
  rfl

@[simp] theorem run_transcript (S : Relation P) (tr : List (TrOp P)) (st : ExState P) :
    runUnits (tr.foldlM (exStepC (sparseOf S)) st) = pure (tr.foldl (exStep S) st) :=
  run_foldlM tr _ _ (by intros; simp) st

theorem run_extractor (S : Relation P) (pub : PubView P) (tr : List (TrOp P)) :
    runUnits (extractorC (sparseOf S) pub tr) =
      (do let sk ← runUnits (drawSketchesC : UnitComp P.q (Sketches P)); pure (extractWith S pub tr sk)) := by
  simp [extractorC, extractWith]

end Praxis.Proofs.Injectivity
