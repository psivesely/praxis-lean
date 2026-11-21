import Praxis.Proofs.IndexSelection.Step
import Praxis.ExtractorCounted
import Praxis.Proofs.IndexSelection.Trace.Small
import Praxis.Proofs.Query.Ops
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Relation
import Praxis.Scheme
import Praxis.Units

namespace Praxis.Proofs.IndexSelection

open OracleComp OracleSpec

private theorem trace_from_world {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m0 m1 : Msg P) (A : Adversary P) (Q : ℕ)
    (h : ∀ m, ∀ w ∈ support (worldRun pp m A), w.st.tr.length ≤ Q) :
    ∀ input ∈ support (do
      let b ← $ᵗ Bool
      let σ ← (sampleEncoding : ProbComp (LabelEncoding P))
      let r ← runWith σ A (encGame σ pp (if b then m1 else m0)) OracleState.empty
      pure (r.1.1.pv, r.2.tr)), input.2.length ≤ Q := by
  intro input hi
  obtain ⟨b, hb, hi⟩ := mem_support_bind_peel _ _ hi
  obtain ⟨σ, hσ, hi⟩ := mem_support_bind_peel _ _ hi
  obtain ⟨r, hr, hi⟩ := mem_support_bind_peel _ _ hi
  have he := eq_of_mem_support_pure _ hi
  subst input
  let w : WorldOut P := ⟨σ, r.1.1, r.1.2, r.2⟩
  have hw : w ∈ support (worldRun pp (if b then m1 else m0) A) := by
    unfold worldRun
    exact (mem_support_bind_iff ..).mpr ⟨σ, hσ,
      (mem_support_bind_iff ..).mpr ⟨r, hr, by simp [w]⟩⟩
  exact h _ w hw

theorem jset_trace (ch : AdmissibleChoice P0) (S : Relation P0) (Q QH : ℕ) (A : Adversary P0)
    (hA : InClass A Q QH) (m0 m1 : Msg P0) :
    ∀ input ∈ support ((scheme ch).extractInputs S m0 m1 A), input.2.length ≤ Q := by
  haveI := (scheme ch).coins_nonempty S
  apply trace_from_world ((scheme ch).setup S) m0 m1 A Q
  intro m
  exact @Query.sig_ops ((scheme ch).setup S) ((scheme ch).coins_nonempty S) m A Q QH hA

theorem jset_small {P : Params} [Fact (Nat.Prime P.q)] (hq : P.q ≤ 2 ^ unitWordBits)
    (S : Relation P) (pub : PubView P) (tr : List (TrOp P)) :
    SmallSamples (extractorC (sparseOf S) pub tr) := by
  exact ns_extractor hq (sparseOf S) pub tr

end Praxis.Proofs.IndexSelection
