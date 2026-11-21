import Praxis.Proofs.Basic
import Praxis.Proofs.DecryptionAlgebra.Psi.Core
import Praxis.Dec
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Scheme
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.DecryptionAlgebra

open Praxis.Algebra (Vec)

theorem decryption_psi (pp : PublicParams P0) (HF : FormOracle P0) (kdf : KDF P0) (m : Msg P0)
    (seed : Seed P0) (c : Coins P0) (x : Vec (Fq P0) P0.N) :
    psi (expGroups P0.q) (encrypt (expGroups P0.q) HF kdf canonName pp m seed c)
        (formsOf HF seed) x .plain =
      (expGroups P0.q).encT
        (∑ cl : Cell P0, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) ∧
    psi (expGroups P0.q) (encrypt (expGroups P0.q) HF kdf canonName pp m seed c)
        (formsOf HF seed) x .alpha =
      (expGroups P0.q).encT (coin c .alpha *
        ∑ cl : Cell P0, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i) := by
  constructor
  · simpa [sectorScale] using psi_exp pp HF kdf m canonName seed c x .plain
  · simpa [sectorScale] using psi_exp pp HF kdf m canonName seed c x .alpha

end Praxis.Proofs.DecryptionAlgebra
