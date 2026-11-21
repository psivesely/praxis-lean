import Praxis.Proofs.GroupModel.Init.Keys
import Praxis.Proofs.GroupModel.Init.Values
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.GroupModel

open GroupModel.Sorted

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem pubView_g1_keys (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (pubView σ pp v c).g1 = (keys1 P).map fun a =>
      (a, σ .g₁ (e1At pp (Assign.ofCoins c) a)) := by
  simp [pubView, keys1, e1At, Assign.ofCoins, List.map_map, Function.comp_def]

theorem pubView_g2_keys (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (pubView σ pp v c).g2 = (keys2 P).map fun a =>
      (a, σ .g₂ (e2At pp v (Assign.ofCoins c) a)) := by
  simp only [pubView, keys2, List.map_cons, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [e2At_ofCoins]

theorem pubView_gt_keys (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (pubView σ pp v c).gT = [none, some ()].map fun a =>
      (a, σ .gₜ (if a = none then 1 else gtExp pp c)) := by
  rfl

end Praxis.Proofs.GroupModel
