import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Relation
import Praxis.Search

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.FieldMarginal

open Classical

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

lemma resample_marginal (pp : PublicParams P0) [Nonempty (CoinDomain pp)]
    (hK2 : ∀ (s : SearchSample P0) (c' : CoinDomain pp),
      (∑' c : CoinDomain pp, if c.val.2.1 = s then
        Pr[= c | coinLaw pp] * Pr[= c' | resample pp c] else 0) =
      Pr[= s | searchLaw] * Pr[= c' | coinLaw pp])
    (r : Record pp) (p : SearchSample P0 → Prop) (y : CoinDomain pp) :
    (∑' s, if p s then (∑' c : CoinDomain pp,
      (if c.val.2.1 = s then Pr[= c | coinLaw pp] else 0) *
        ∑' x, Pr[= x | guessDraw pp r c] * Pr[= y | resample pp c]) else 0) ≤
      (∑' s, if p s then Pr[= s | searchLaw] else 0) * Pr[= y | coinLaw pp] := by
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro s
  by_cases hs : p s
  · simp only [if_pos hs]
    calc
      _ ≤ ∑' c : CoinDomain pp,
          (if c.val.2.1 = s then Pr[= c | coinLaw pp] else 0) *
            Pr[= y | resample pp c] := by
        apply ENNReal.tsum_le_tsum
        intro c
        apply mul_le_mul' le_rfl
        exact tsum_probOutput_mul_le_of_le (guessDraw pp r c) (fun _ => le_rfl)
      _ = Pr[= s | searchLaw] * Pr[= y | coinLaw pp] := by
        convert hK2 s y using 1
        apply tsum_congr
        intro c
        split_ifs <;> simp only [zero_mul]
  · simp only [if_neg hs, zero_mul, le_refl]

lemma fieldSlot_marginal (ch : AdmissibleChoice P0) (S : Relation P0)
    (hK2 : ∀ (s : SearchSample P0) (c' : CoinDomain (ppOf ch S)),
      (∑' c : CoinDomain (ppOf ch S), if c.val.2.1 = s then
        Pr[= c | coinLaw (ppOf ch S)] * Pr[= c' | resample (ppOf ch S) c] else 0) =
      Pr[= s | searchLaw] * Pr[= c' | coinLaw (ppOf ch S)])
    (pad : Bounds ch S .field)
    (fires : Record (ppOf ch S) → Option (SearchSample P0 → Bounds ch S .field)) :
    (fieldSlot pad fires).Marginal := by
  intro r f _ a y
  cases a <;> exact resample_marginal (ppOf ch S) hK2 r _ y

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.FieldMarginal
