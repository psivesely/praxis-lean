import Praxis.Proofs.Basic
import Praxis.Constants
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Grid
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.GroupModel

open GroupModel.Sorted

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem legList_length : (legList P).length = 3 * P.K2 := by
  simp [legList]
  omega

theorem cellList_length : (cellList P).length = P.K1 * (3 * P.K2) := by
  simp [cellList, List.length_flatMap, legList_length]

theorem g2OrderSector_length (σ : Sector) :
    (g2OrderSector P σ).length =
      2 * (3 * P.K2) * (P.N + 1) + 3 * (3 * P.K2) +
        (P.K1 * (3 * P.K2)) * P.Mq + (P.K1 * (3 * P.K2)) * P.Wr +
        5 * (2 * P.n - 1) + 3 * (P.n - 1) := by
  simp [g2OrderSector, List.length_flatMap, legList_length, cellList_length]
  ring

theorem g2Order_length : (g2Order P).length = countG2 P := by
  have h1 : Fintype.card LegKind = 3 := by decide
  have h2 : Fintype.card CrossIdx = 5 := by decide
  have h3 : Fintype.card TieIdx = 3 := by decide
  simp [g2Order, g2OrderSector_length, countG2, legCount, cellCount,
    h1, h2, h3]
  ring

private theorem rp_filterMap_length (xs : List (Fin (P.U * P.E1p))) :
    (xs.filterMap fun s =>
      if h : P.U ∣ s.val then none else some (G1Idx.RP (P := P) ⟨s, h⟩)).length =
      (xs.filter fun s => ! decide (P.U ∣ s.val)).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : P.U ∣ a.val <;> simp [h, ih]

private def multiplesEquiv (hU : 0 < P.U) :
    Fin P.E1p ≃ {s : Fin (P.U * P.E1p) // P.U ∣ s.val} where
  toFun k := ⟨⟨P.U * k.val, Nat.mul_lt_mul_of_pos_left k.isLt hU⟩, dvd_mul_right _ _⟩
  invFun s := ⟨s.1.val / P.U, by
    apply (Nat.div_lt_iff_lt_mul hU).2
    simpa [Nat.mul_comm] using s.1.isLt⟩
  left_inv k := by
    apply Fin.ext
    exact Nat.mul_div_cancel_left _ hU
  right_inv s := by
    apply Subtype.ext
    apply Fin.ext
    simpa [Nat.mul_comm] using Nat.div_mul_cancel s.2

private theorem multiples_count (hU : 0 < P.U) :
    Fintype.card {s : Fin (P.U * P.E1p) // P.U ∣ s.val} = P.E1p := by
  rw [← Fintype.card_congr (multiplesEquiv hU)]
  simp

private theorem rp_length (hU : 0 < P.U) :
    ((List.finRange (P.U * P.E1p)).filterMap fun s =>
      if h : P.U ∣ s.val then none else some (G1Idx.RP (P := P) ⟨s, h⟩)).length =
      (P.U - 1) * P.E1p := by
  rw [rp_filterMap_length]
  let xs := List.finRange (P.U * P.E1p)
  have hcount : (xs.filter fun s => decide (P.U ∣ s.val)).length = P.E1p := by
    have hn := List.toFinset_card_of_nodup
      ((List.nodup_finRange (P.U * P.E1p)).filter (fun s => decide (P.U ∣ s.val)))
    have hc := multiples_count (P := P) hU
    rw [Fintype.card_subtype] at hc
    have hs : ((List.finRange (P.U * P.E1p)).filter
        (fun s => decide (P.U ∣ s.val))).toFinset =
        Finset.univ.filter (fun s : Fin (P.U * P.E1p) => P.U ∣ s.val) := by
      ext s
      simp
    rw [hs] at hn
    simpa [xs] using hn.symm.trans hc
  have hsplit := List.length_eq_length_filter_add (l := xs) (fun s => decide (P.U ∣ s.val))
  simp only [xs, List.length_finRange] at hsplit
  rw [hcount] at hsplit
  have hmul : (P.U - 1) * P.E1p + P.E1p = P.U * P.E1p := by
    have : P.U - 1 + 1 = P.U := by omega
    nlinarith
  omega

theorem g1Order_length (hU : 0 < P.U) : (g1Order P).length = countG1 P := by
  simp [g1Order, List.length_flatMap, rp_length hU, countG1]
  ring

theorem pubView_g1_length (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (pubView σ pp v c).g1.length = (g1Order P).length + 1 := by
  simp [pubView]

theorem pubView_g2_length (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (pubView σ pp v c).g2.length = (g2Order P).length + 1 := by
  simp [pubView]

theorem pubView_gt_length (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (pubView σ pp v c).gT.length = 2 := by
  rfl

theorem pubView_g2_length_main (σ : LabelEncoding P0) (pp : PublicParams P0)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (c : Coins P0) :
    (pubView σ pp v c).g2.length = Constants.L2 := by
  rw [pubView_g2_length, g2Order_length]
  have h1 : Fintype.card LegKind = 3 := rfl
  have h2 : Fintype.card CrossIdx = 5 := rfl
  have h3 : Fintype.card TieIdx = 3 := rfl
  simp only [countG2, cellCount, legCount, h1, h2, h3]
  norm_num [Params.main, Constants.K1, Constants.K2, Constants.N, Constants.M_q,
    Constants.W_r, Constants.n, Constants.L2]

theorem pubView_g1_length_main (σ : LabelEncoding P0) (pp : PublicParams P0)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (c : Coins P0) :
    (pubView σ pp v c).g1.length = Constants.L1 := by
  have hU : 0 < P0.U := by norm_num [Params.main, Constants.U]
  rw [pubView_g1_length, g1Order_length hU]
  norm_num [countG1, Params.main, Constants.K1, Constants.N, Constants.E1, Constants.U,
    Constants.E1p, Constants.L1]

theorem pubView_gt_length_main (σ : LabelEncoding P0) (pp : PublicParams P0)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (c : Coins P0) :
    (pubView σ pp v c).gT.length = Constants.LT := by
  simp [pubView_gt_length, Constants.LT]

end Praxis.Proofs.GroupModel
