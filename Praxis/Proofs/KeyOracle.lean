import Praxis.Proofs.KeyOracle.Independence
import Praxis.Proofs.Basic
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.KeyOracle

open OracleComp OracleSpec

theorem enc_target_cache (σ : LabelEncoding P0) (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0) :
    ∀ r ∈ support ((encGame σ pp m).run OracleState.empty),
      r.2.kdf = Function.update (fun _ => none) (labelName (σ .gₜ) (kappa pp r.1.coins))
          (some (r.1.header.cm ^^^ m)) ∧
        r.2.kdfLog = [] ∧ r.2.tr = [] := by
  intro r hr
  have hr' : r ∈ support (do
      let z ← (encPrefix pp).run OracleState.empty
      let p ← $ᵗ (Msg P0)
      pure (finish σ pp m z.1 z.2 p)) :=
    (mem_support_iff_of_evalSPMF_eq (enc_split σ pp m) r).mp hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr'
  obtain ⟨z, hz, p, hp, he⟩ := hr'
  subst r
  obtain ⟨hk, hl, ht⟩ := prefix_clean pp z hz
  simp [finish, hk, hl, ht, BitVec.xor_assoc, BitVec.xor_comm m]

theorem enc_public_indep (σ : LabelEncoding P0) (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m m' : Msg P0) :
    evalSPMF ((fun r : EncOut P0 × OracleState P0 =>
        (r.1.pv, r.1.header.seed, r.1.header.cm, r.1.forms, r.1.coins, r.2.hf, r.2.issuedT)) <$>
        (encGame σ pp m).run OracleState.empty) =
      evalSPMF ((fun r : EncOut P0 × OracleState P0 =>
        (r.1.pv, r.1.header.seed, r.1.header.cm, r.1.forms, r.1.coins, r.2.hf, r.2.issuedT)) <$>
        (encGame σ pp m').run OracleState.empty) := by
  let publicPart := fun r : EncOut P0 × OracleState P0 =>
    (r.1.pv, r.1.header.seed, r.1.header.cm, r.1.forms, r.1.coins, r.2.hf, r.2.issuedT)
  change evalSPMF (publicPart <$> (encGame σ pp m).run OracleState.empty) =
    evalSPMF (publicPart <$> (encGame σ pp m').run OracleState.empty)
  have h (x : Msg P0) := evalSPMF_map_eq_of_evalSPMF_eq (enc_common_header σ pp x) publicPart
  rw [h m, h m']
  simp only [map_bind, map_pure]
  apply evalSPMF_bind_congr
  intro z hz
  apply evalSPMF_bind_congr
  intro c hc
  have cancel (x : Msg P0) : x ^^^ (c ^^^ x) = c := by
    rw [BitVec.xor_comm c x, ← BitVec.xor_assoc]
    simp
  simp [publicPart, finish, cancel]

end Praxis.Proofs.KeyOracle
