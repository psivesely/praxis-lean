import Praxis.Proofs.IndexSelection.Setup.Bounds
import Praxis.ExtractorCounted
import Praxis.Grid
import Praxis.Params
import Praxis.Published

namespace Praxis.Proofs.IndexSelection

set_option maxRecDepth 4096

theorem legs_nodup (P : Params) : (legList P).Nodup := by
  have hinj (X : LegKind) : Function.Injective (fun k : Fin P.K2 => (X, k)) := by
    intro a b h
    exact congrArg Prod.snd h
  simp only [legList, List.flatMap_cons, List.flatMap_nil, List.nil_append,
    List.nodup_append, List.nodup_map_iff (hinj _), List.nodup_finRange, true_and,
    List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
  simp [List.mem_append, List.mem_map]
  intro k a h
  cases a <;> simp_all

theorem filter_cells (P : Params) (leg : Leg P) :
    ((cellList P).filter fun c => decide (c.2 = leg)).length ≤ P.K1 := by
  have h := List.nodup_iff_count_le_one.mp (legs_nodup P) leg
  simp only [cellList, List.filter_flatMap, List.filter_map, List.length_flatMap, List.length_map]
  simp only [Function.comp_def]
  have heq : ((legList P).filter fun x => decide (x = leg)).length ≤ 1 := by
    have hh : (fun x : Leg P => decide (x = leg)) = (fun x => x == leg) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp
    rw [hh, ← List.count_eq_length_filter]
    exact h
  change ((List.finRange P.K1).map (Function.const _
    ((legList P).filter fun x => decide (x = leg)).length)).sum ≤ P.K1
  rw [List.map_const, List.sum_replicate, List.length_finRange]
  simpa using Nat.mul_le_mul_left P.K1 heq

theorem g1_length_bound (P : Params) : (g1Order P).length ≤
    2 * P.K1 * (P.N + 1) + 2 * P.K1 + P.E1 + P.U * P.E1p + (P.N + 1) := by
  have h := List.length_filterMap_le (fun s : Fin (P.U * P.E1p) =>
    if h : P.U ∣ s.val then none else some (G1Idx.RP ⟨s, h⟩)) (List.finRange (P.U * P.E1p))
  simp only [List.length_finRange] at h
  simp only [g1Order, List.length_append, List.length_map, List.length_flatMap,
    List.length_finRange, List.map_const', List.sum_replicate, nsmul_eq_mul]
  nlinarith

theorem sum_map_const {α : Type} (xs : List α) (k : ℕ) :
    (xs.map fun _ => k).sum = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem leg_length (P : Params) : (legList P).length = 3 * P.K2 := by
  simp only [legList, List.length_flatMap, List.length_map, List.length_finRange,
    sum_map_const, List.length_cons, List.length_nil]

theorem cell_length (P : Params) : (cellList P).length = P.K1 * (3 * P.K2) := by
  simp only [cellList, List.length_flatMap, List.length_map, sum_map_const,
    List.length_finRange, leg_length]

theorem keys_length (P : Params) : (g2Keys P).length = 6 * (P.K1 * (3 * P.K2)) := by
  simp only [g2Keys, List.length_flatMap, List.length_map, List.length_cons, List.length_nil,
    sum_map_const, List.length_finRange, cell_length]
  ring

theorem g2_weight (P : Params) :
    ((g2Order P).map fun i => initCost (some i) + 1).sum =
      2 * (2 * (3 * P.K2) * (P.N + 1) + 2 * (3 * P.K2) +
        (P.K1 * (3 * P.K2)) * P.Mq + (P.K1 * (3 * P.K2)) * P.Wr +
        3 * P.K2 + 5 * (2 * P.n - 1) + 3 * (P.n - 1) +
        (3 * P.K2) * (3 * P.K1 * P.N)) := by
  simp only [g2Order, g2OrderSector, List.map_append, List.sum_append, sum_flatMap_map,
    List.map_map, Function.comp_def, initCost, sum_map_const, List.length_finRange,
    leg_length, cell_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

end Praxis.Proofs.IndexSelection
