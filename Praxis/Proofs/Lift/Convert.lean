import Praxis.Proofs.Lift.Bridge
import Praxis.Proofs.Sampling.Row
import Praxis.Bounds.Rank
import Praxis.Combinatorics.Mass
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Praxis.Constants
import Praxis.Lift.Parameters
import Praxis.Lift.Record
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Reduction
import Praxis.Scheme
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Stmt.Short
import Praxis.Algebra.Inverse.Definitions

namespace Praxis.Proofs.Lift

open Praxis.Algebra (Vec)

instance main_prime_q : Fact (Nat.Prime Constants.q) := main_prime

theorem gridBudget_main :
    Algebra.Inverse.Definitions.GridBudget Praxis.Lift.Parameters.mainRecord.toVITData
      (fun _ : Fin P0.N => P0.g) := by
  change (∀ i : Fin P0.N, P0.g ≤ P0.g) ∧
    (∑ _ : Fin P0.N, (P0.g : ℝ)^2) ≤ (P0.g : ℝ)^2 * (Constants.N : ℝ) ∧
    (∀ _ : Fin P0.N, (P0.g : ℝ)^2 < Praxis.Lift.Parameters.mainData.T2)
  refine ⟨fun _ => le_rfl, ?_, fun _ => ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (mul_comm _ _)
  · rw [Praxis.Lift.Parameters.main_T2]
    norm_num [P0, Params.main, Constants.g, Constants.lift_exact_values_T_squared]

theorem convert_complete (W : Stack P0) (hsym : ∀ c, (W c).IsSymm) (hW : Heavy W)
    (v : Vec (Fq P0) P0.N) (hv : v ∈ jointSpace W) (hv0 : v ≠ 0) (hv00 : v 0 = 0) :
    (convertLIFT v).isSome := by
  have hm : Praxis.Lift.Parameters.mainRecord.theta0 <
      Algebra.Inverse.Definitions.mass (fun _ : Fin P0.N => P0.g)
        (Algebra.Inverse.Definitions.scalar (fun _ : Fin P0.N => P0.g) (fun i => v i.succ)) := by
    rw [← lift_bridge v hv00]
    exact lt_of_lt_of_le (lt_of_not_ge hW) (Sampling.row_heavy W hsym v hv)
  obtain ⟨a, w, ha, hw, hw0, hc, hb⟩ :=
    Praxis.Lift.Parameters.lift_main P0.N (fun _ => P0.g) v gridBudget_main hv0 hv00 hm
  change Fq P0 at a
  change ∀ i, (w i : Fq P0) = a * v i at hc
  change Algebra.Inverse.Definitions.maxAbs w ≤ P0.eta at hb
  have hs : Algebra.Short.ShortMultiple P0.q P0.eta v := by
    refine ⟨w, ?_, ⟨a, ha, hc⟩, ?_⟩
    · intro he
      apply hv0
      funext i
      have hi := congrFun he i
      change (w i : Fq P0) = 0 at hi
      rw [hc i] at hi
      exact (mul_eq_zero.mp hi).resolve_left ha
    · intro i
      have hi := (Combinatorics.UnequalChain.natAbs_le_maxNorm w i).trans hb
      have hi' : ((w i).natAbs : ℤ) ≤ (P0.eta : ℤ) := by exact_mod_cast hi
      simpa only [Int.natCast_natAbs] using hi'
  have hn : convertLIFT v ≠ none := by
    intro h
    exact (Algebra.Short.bruteForce_none_iff v).mp h hs
  exact Option.isSome_iff_ne_none.mpr hn

end Praxis.Proofs.Lift
