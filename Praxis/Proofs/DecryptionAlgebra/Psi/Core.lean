import Praxis.Dec
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.DecryptionAlgebra

open Praxis.Algebra (Vec)

theorem psi_exp {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P) (m : Msg P)
    (name : (expGroups P.q).GT → ClassName P) (seed : Seed P) (c : Coins P) (x : Vec (Fq P) P.N) (σ : Sector) :
    psi (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c)
        (formsOf HF seed) x σ =
      (expGroups P.q).encT (sectorScale c σ *
        ∑ cl : Cell P, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) := by
  change (∑ cl : Cell P, weight (formsOf HF seed) x cl *
    ∑ i, x i * ((piAt c cl.1.val * c.1 i * 1) *
      (sectorScale c σ * legScale c cl.2 * 1))) =
    (sectorScale c σ * ∑ cl : Cell P,
      weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) * (1 * 1)
  simp only [mul_one, gamma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun cl _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Praxis.Proofs.DecryptionAlgebra
