import Praxis.Proofs.Injectivity.Invariants
import Praxis.Extractor
import Praxis.Keys
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra

variable {P : Params}

def eventOp : MonEvent P → Option (TrOp P)
  | .op op => some op
  | .kdf _ => none

theorem range_entries {α : Type*} (xs : List α) (n : ℕ) :
    (List.range n).flatMap (fun k => xs[k]?.toList) = xs.take n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih, List.take_succ]

theorem monEvents_ops (tr : List (TrOp P)) (kl : List (ℕ × ClassName P)) :
    (monEvents tr kl).filterMap eventOp = tr := by
  unfold monEvents
  simp only [List.filterMap_flatMap, List.filterMap_append, List.filterMap_map,
    Function.comp_def, eventOp]
  have hk (xs : List (ℕ × ClassName P)) : xs.filterMap (fun _ => (none : Option (TrOp P))) = [] := by simp
  simp only [hk, List.nil_append]
  have ho (o : Option (TrOp P)) : o.toList.filterMap (fun op => some op) = o.toList := by
    cases o <;> rfl
  simp only [ho]
  rw [range_entries, List.take_of_length_le (by omega)]

variable [Fact (Nat.Prime P.q)]

def exEvent (S : Relation P) (st : ExState P) : MonEvent P → ExState P
  | .op op => exStep S st op
  | .kdf _ => st

theorem fold_exEvents (S : Relation P) (events : List (MonEvent P)) (st : ExState P) :
    events.foldl (exEvent S) st = (events.filterMap eventOp).foldl (exStep S) st := by
  rw [List.foldl_filterMap]
  congr 1
  funext st e
  cases e <;> rfl

theorem monEvents_fold (S : Relation P) (tr : List (TrOp P)) (kl : List (ℕ × ClassName P))
    (st : ExState P) : (monEvents tr kl).foldl (exEvent S) st = tr.foldl (exStep S) st := by
  rw [fold_exEvents, monEvents_ops]

theorem event_fold_none (S : Relation P) (st : ExState P) (events : List (MonEvent P))
    (h : (events.foldl (exEvent S) st).found = none) : st.found = none := by
  rw [fold_exEvents] at h
  exact fold_none S st _ h

end Praxis.Proofs.Injectivity
