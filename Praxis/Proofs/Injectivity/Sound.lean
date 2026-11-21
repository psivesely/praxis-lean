import Praxis.Proofs.Injectivity.SoundAux
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Proofs.Injectivity.Deterministic
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec

theorem jse_sound {P : Params} [Fact (Nat.Prime P.q)] (S : Relation P) (pub : PubView P)
    (tr : List (TrOp P)) (x : Algebra.Vec (Fq P) P.N)
    (h : some x ∈ support (runUnits (extractorC (sparseOf S) pub tr))) : IsWitness S x := by
  rw [run_extractor] at h
  obtain ⟨sk, _, hx⟩ := (mem_support_bind_iff _ _ _).mp h
  simp only [support_pure, Set.mem_singleton_iff] at hx
  exact extractWith_sound S pub tr sk x hx.symm

end Praxis.Proofs.Injectivity
