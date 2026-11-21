import Praxis.Proofs.View.SZ.Roots
import Praxis.Enc
import Praxis.Proofs.View.SZ.Grid
import Praxis.Proofs.View.SZ.Law
import Praxis.Params
import Praxis.Setting

namespace Praxis.Proofs.View

open OracleComp OracleSpec Classical

theorem coinLaw_root_bound {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (p : MvPolynomial (CoinVar P) (Fq P)) (hp : p ≠ 0)
    (m d : ℕ) (hm : 0 < m) (hd : p.totalDegree ≤ d)
    (hS : ∀ i, m ≤ (sampleSet pp.qap i).card) :
    (letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
     Pr[fun c => MvPolynomial.eval (coinVar c.1) p = 0 |
       $ᵗ {c : Coins P // ValidCoins pp.qap c}]).toReal ≤ (d : ℝ) / m := by
  have h := grid_root_bound (sampleSet pp.qap) m hm hS p hp
  have hd' : (p.totalDegree : ENNReal) ≤ d := by exact_mod_cast hd
  have h' := h.trans (ENNReal.div_le_div_right hd' _)
  have h'' := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast (Nat.ne_of_gt hm))) h'
  rw [coinLaw_grid pp (fun x => MvPolynomial.eval x p = 0)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at h'' ⊢
  refine (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)).trans h''
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    simpa only [Finset.mem_filter] using hx)

end Praxis.Proofs.View
