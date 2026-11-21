import Praxis.Proofs.Monitor.Recover.Helpers
import Praxis.Proofs.Monitor.Recover.Sampling
import Praxis.Enc
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

theorem sampleGradients_bound {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (D : ExprT P) (σ : Sector) (W : Stack P) (ε : ℝ) (hε : 0 ≤ ε) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (ValidDraw pp)
    letI := SampleableType.ofFintype (Fin 3 → ValidDraw pp)
    (∀ a : ValidDraw pp, rGrad pp (drawAssign a) D σ ∈ jointSpace W) →
    Module.finrank (Fq P) (jointSpace W) ≤ 3 →
    (∀ U : Submodule (Fq P) (Vec (Fq P) P.N), U < jointSpace W →
      (Pr[fun a : ValidDraw pp => rGrad pp (drawAssign a) D σ ∈ U | $ᵗ (ValidDraw pp)]).toReal ≤ ε) →
    (Pr[fun as : Fin 3 → Assign P => Submodule.span (Fq P)
      (Set.range (fun l => rGrad pp (as l) D σ)) ≠ jointSpace W | sampleAssigns pp 3]).toReal ≤ 3 * ε := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (ValidDraw pp)
  letI := SampleableType.ofFintype (Fin 3 → ValidDraw pp)
  intro hmem hrank hbound
  rw [sampleAssigns_event]
  exact threeGradients_bound pp D σ drawAssign W ε hε hmem hrank hbound

end Praxis.Proofs.Monitor
