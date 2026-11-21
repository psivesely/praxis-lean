import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Domain
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

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.LightMarginal

open Classical

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

private lemma searchLaw_mass : (∑' s : SearchSample P0, Pr[= s | searchLaw]) = 1 := by
  let _ := SampleableType.ofFintype (SearchSample P0)
  apply tsum_probOutput_eq_one'
  exact probFailure_uniformSample (SearchSample P0)

variable (ch : AdmissibleChoice P0) (S : Relation P0)

lemma lightSlot_marginal
    (hK1 : ∀ s : SearchSample P0, (∑' c : CoinDomain (ppOf ch S),
      if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) = Pr[= s | searchLaw])
    (pad : Bounds ch S .light) (fires : Record (ppOf ch S) → Option (Bounds ch S .light)) :
    (lightSlot pad fires).Marginal := by
  intro r f hf a y
  change Bounds ch S .light at a
  change (fires r).map (fun t _ => t) = some f at hf
  cases hfire : fires r with
  | none => simp [hfire] at hf
  | some t =>
    simp only [hfire, Option.map_some] at hf
    have hf' : (fun _ : SearchSample P0 => t) = f := Option.some.inj hf
    subst f
    dsimp only [lightSlot]
    by_cases hta : t = a
    · subst a
      cases t with
      | light forms D ι hlight =>
        change SearchSample P0 at y
        simp only
        change (∑' s, ∑' c : CoinDomain (ppOf ch S),
          (if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) *
            ∑' x, Pr[= x | guessDraw (ppOf ch S) r c] *
              Pr[= y | (pure c.val.2.1 : ProbComp (SearchSample P0))]) ≤
            (∑' s, Pr[= s | searchLaw]) * Pr[= y | searchLaw]
        calc
          _ ≤ ∑' s, ∑' c : CoinDomain (ppOf ch S),
              (if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) *
                Pr[= y | (pure c.val.2.1 : ProbComp (SearchSample P0))] := by
            apply ENNReal.tsum_le_tsum
            intro s
            apply ENNReal.tsum_le_tsum
            intro c
            apply mul_le_mul' le_rfl
            rw [ENNReal.tsum_mul_right]
            exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)
          _ = Pr[= y | searchLaw] := by
            have hs (s : SearchSample P0) :
                (∑' c : CoinDomain (ppOf ch S),
                  (if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) *
                    Pr[= y | (pure c.val.2.1 : ProbComp (SearchSample P0))]) =
                  if y = s then Pr[= s | searchLaw] else 0 := by
              calc
                _ = (∑' c : CoinDomain (ppOf ch S),
                    if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) *
                      (if y = s then 1 else 0) := by
                  rw [← ENNReal.tsum_mul_right]
                  apply tsum_congr
                  intro c
                  by_cases hc : c.val.2.1 = s
                  · simp only [hc, if_true, probOutput_pure]
                  · simp only [hc, if_false, zero_mul]
                _ = _ := by rw [hK1]; split_ifs <;> simp
            simp_rw [hs]
            exact tsum_ite_eq' y (fun s => Pr[= s | searchLaw])
          _ ≤ _ := by
            rw [searchLaw_mass, one_mul]
    · refine le_trans (b := 0) ?_ zero_le
      apply le_of_eq
      exact ENNReal.tsum_eq_zero.mpr (fun _ => if_neg hta)

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.LightMarginal
