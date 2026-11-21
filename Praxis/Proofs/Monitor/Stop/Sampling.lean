import Praxis.Proofs.Basic
import Praxis.Enc
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

open Classical

variable {P : Params} [Fact (Nat.Prime P.q)]

abbrev ValidCoin (pp : PublicParams P) := {c : Coins P // ValidCoins pp.qap c}

abbrev AssignSample (pp : PublicParams P) := ValidCoin pp × Algebra.Vec (Fq P) P.N

def sampleToAssign {pp : PublicParams P} (z : AssignSample pp) : Assign P := ⟨z.1.1, z.2⟩

def splitSamples (pp : PublicParams P) (k : ℕ) :
    (Fin k → AssignSample pp) ≃ ((Fin k → ValidCoin pp) × (Fin k → Algebra.Vec (Fq P) P.N)) where
  toFun z := (fun i => (z i).1, fun i => (z i).2)
  invFun z i := (z.1 i, z.2 i)
  left_inv := by intro z; funext i; exact Prod.eta (z i)
  right_inv := by intro z; cases z; rfl

theorem sampleAssigns_law (pp : PublicParams P) [Nonempty (ValidCoin pp)] (k : ℕ) :
    letI := SampleableType.ofFintype (ValidCoin pp)
    letI := SampleableType.ofFintype (AssignSample pp)
    𝒮[sampleAssigns pp k] =
      𝒮[(fun z : Fin k → AssignSample pp => fun i => sampleToAssign (z i)) <$> ($ᵗ (Fin k → AssignSample pp))] := by
  letI := SampleableType.ofFintype (ValidCoin pp)
  letI := SampleableType.ofFintype (AssignSample pp)
  let e := splitSamples pp k
  have he := evalSPMF_map_bijective_uniform_cross (α := Fin k → AssignSample pp) e e.bijective
  let f : ((Fin k → ValidCoin pp) × (Fin k → Algebra.Vec (Fq P) P.N)) → Fin k → Assign P :=
    fun z i => ⟨(z.1 i).1, z.2 i⟩
  calc
    𝒮[sampleAssigns pp k] = 𝒮[f <$> ($ᵗ ((Fin k → ValidCoin pp) × (Fin k → Algebra.Vec (Fq P) P.N)))] := by
      change 𝒮[sampleAssigns pp k] =
        𝒮[f <$> ((Prod.mk <$> ($ᵗ (Fin k → ValidCoin pp))) <*> ($ᵗ (Fin k → Algebra.Vec (Fq P) P.N)))]
      simp [sampleAssigns, f, monad_norm]
    _ = 𝒮[f <$> (e <$> ($ᵗ (Fin k → AssignSample pp)))] := by
      simp only [evalSPMF_map, he]
    _ = 𝒮[(fun z : Fin k → AssignSample pp => fun i => sampleToAssign (z i)) <$> ($ᵗ (Fin k → AssignSample pp))] := by
      congr 1
      simp [f, e, splitSamples, sampleToAssign, Functor.map_map, Function.comp_def]

end Praxis.Proofs.Monitor
