import Praxis.Proofs.Injectivity.Deterministic
import Praxis.Extractor
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem neg_pivot (r : Vec (Fq P) P.N) (col : Fin (P.N + 1)) :
    ((-r) col)⁻¹ • (-r) = (r col)⁻¹ • r := by
  simp

theorem neg_elim (r w : Vec (Fq P) P.N) (col : Fin (P.N + 1)) :
    (-w) - (-w) col • r = -(w - w col • r) := by
  ext i
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem refColumn_neg (rows : List (Vec (Fq P) P.N))
    (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N)) (col : Fin (P.N + 1)) :
    refColumn (rows.map Neg.neg, basis) col =
      let st := refColumn (rows, basis) col
      (st.1.map Neg.neg, st.2) := by
  have hp : (rows.map Neg.neg).find? (fun r => decide (r col ≠ 0)) =
      (rows.find? fun r => decide (r col ≠ 0)).map Neg.neg := by
    rw [List.find?_map]
    congr 2
    funext r
    simp
  unfold refColumn
  dsimp only
  rw [hp]
  cases hr : rows.find? (fun r => decide (r col ≠ 0)) with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    rw [neg_pivot]
    rw [← List.map_erase (f := Neg.neg) neg_injective]
    simp only [List.map_map, Function.comp_def, neg_elim]

theorem fold_columns_neg (cols : List (Fin (P.N + 1))) (rows : List (Vec (Fq P) P.N))
    (basis : List (Fin (P.N + 1) × Vec (Fq P) P.N)) :
    cols.foldl refColumn (rows.map Neg.neg, basis) =
      let st := cols.foldl refColumn (rows, basis)
      (st.1.map Neg.neg, st.2) := by
  induction cols generalizing rows basis with
  | nil => rfl
  | cons col cols ih =>
    simp only [List.foldl_cons, refColumn_neg]
    exact ih _ _

theorem rref_neg (rows : List (Vec (Fq P) P.N)) : rref (rows.map Neg.neg) = rref rows := by
  change ((List.finRange (P.N + 1)).foldl refColumn (rows.map Neg.neg, [])).2 =
    ((List.finRange (P.N + 1)).foldl refColumn (rows, [])).2
  rw [fold_columns_neg]

theorem refColumn_zero (rows : List (Vec (Fq P) P.N)) (h : ∀ r ∈ rows, r = 0)
    (col : Fin (P.N + 1)) : refColumn (rows, []) col = (rows, []) := by
  unfold refColumn
  have hf : rows.find? (fun r => decide (r col ≠ 0)) = none := by
    apply List.find?_eq_none.mpr
    intro r hr
    simp [h r hr]
  rw [hf]

theorem rref_zero : rref ([0, 0, 0] : List (Vec (Fq P) P.N)) = [] := by
  have h (cols : List (Fin (P.N + 1))) :
      cols.foldl refColumn ([0, 0, 0], []) = ([0, 0, 0], []) := by
    induction cols with
    | nil => rfl
    | cons col cols ih =>
      rw [List.foldl_cons, refColumn_zero _ (by simp) col]
      exact ih
  exact congrArg Prod.snd (h (List.finRange (P.N + 1)))

@[simp] theorem testExpr_zero (S : Relation P) :
    testExpr S (0 : Fin 3 → Sector → Vec (Fq P) P.N) = none := by
  simp [testExpr, testSketches, rref_zero, candidates]

theorem testSketches_neg (S : Relation P) (F : Fin 3 → Vec (Fq P) P.N) :
    testSketches S (fun l => -F l) = testSketches S F := by
  unfold testSketches
  rw [show [-F 0, -F 1, -F 2] = [F 0, F 1, F 2].map Neg.neg from rfl, rref_neg]

@[simp] theorem testExpr_neg (S : Relation P) (F : Fin 3 → Sector → Vec (Fq P) P.N) :
    testExpr S (-F) = testExpr S F := by
  unfold testExpr
  simp only [Pi.neg_apply, testSketches_neg]

theorem exStep_absorb (S : Relation P) (st : ExState P) (op : TrOp P) (x : Vec (Fq P) P.N)
    (h : st.found = some x) : exStep S st op = st := by simp [exStep, h]

theorem fold_absorb (S : Relation P) (st : ExState P) (ops : List (TrOp P))
    (x : Vec (Fq P) P.N) (h : st.found = some x) : ops.foldl (exStep S) st = st := by
  induction ops with
  | nil => rfl
  | cons op ops ih => rw [List.foldl_cons, exStep_absorb S st op x h, ih]

theorem fold_none (S : Relation P) (st : ExState P) (ops : List (TrOp P))
    (h : (ops.foldl (exStep S) st).found = none) : st.found = none := by
  cases hf : st.found with
  | none => rfl
  | some x => rw [fold_absorb S st ops x hf, hf] at h; cases h

theorem gtStep_failed (S : Relation P) (st : ExState P)
    (F : Fin 3 → Sector → Vec (Fq P) P.N) (l : Label P)
    (h : (gtStep S st F l).found = none) :
    testExpr S F = none ∧ ∀ E, st.dT l = some E → testExpr S (F - E) = none := by
  unfold gtStep at h
  dsimp only at h
  cases ht : testExpr S F with
  | some x => simp [ht] at h
  | none =>
    refine ⟨rfl, ?_⟩
    intro E he
    simpa [ht, he] using h

end Praxis.Proofs.Injectivity
