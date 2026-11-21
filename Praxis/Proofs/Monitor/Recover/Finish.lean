import Praxis.Proofs.Monitor.Recover.Span
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Recover.Helpers
import Praxis.Proofs.Monitor.Recover.Sampling
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

attribute [local irreducible] sampleAssigns GoodMark markSector markStack gradSpan recAssign

private def recoveryFailure {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (f : FullOut P) : Prop :=
  ∃ D ι, GoodMark pp f.w D ι ∧
    gradSpan pp (recAssign f.w0 f.w1) D (markSector D) ≠ jointSpace (markStack D)

private def sampleFailure {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (D : ExprT P) (as : Fin 3 → Assign P) : Prop :=
  Submodule.span (Fq P) (Set.range (fun l => rGrad pp (as l) D (markSector D))) ≠
    jointSpace (markStack D)

private lemma failure_plain {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (w : WorldOut P) (D : ExprT P) (ι : Fq P)
    (hg : GoodMark pp w D ι) (hs : markSector D = .plain)
    (p : Assign P) (a b : Fin 3 → Assign P) (x : Option (Vec (Fq P) P.N)) :
    recoveryFailure pp ⟨w,p,a,b,x⟩ → sampleFailure pp D a := by
  intro h
  have he := (goodRecovery_iff pp w D ι hg a b).mp h
  simpa only [sampleFailure, gradSpan, recAssign, hs] using he

private lemma failure_alpha {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (w : WorldOut P) (D : ExprT P) (ι : Fq P)
    (hg : GoodMark pp w D ι) (hs : markSector D = .alpha)
    (p : Assign P) (a b : Fin 3 → Assign P) (x : Option (Vec (Fq P) P.N)) :
    recoveryFailure pp ⟨w,p,a,b,x⟩ → sampleFailure pp D b := by
  intro h
  have he := (goodRecovery_iff pp w D ι hg a b).mp h
  simpa only [sampleFailure, gradSpan, recAssign, hs] using he

private lemma inner_plain_zero {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (ext : ExtractorLaw P) (w : WorldOut P) (D : ExprT P) (ι : Fq P)
    (hg : GoodMark pp w D ι) (hs : markSector D = .plain)
    (p : Assign P) (a : Fin 3 → Assign P) (ha : ¬ sampleFailure pp D a) :
    Pr[recoveryFailure pp | do
      let b ← sampleAssigns pp 3
      let x ← ext pp.S w.out.pv w.st.tr
      pure (⟨w,p,a,b,x⟩ : FullOut P)] = 0 := by
  apply probEvent_eq_zero
  intro f hf he
  obtain ⟨b, _, hf⟩ := (mem_support_bind_iff ..).mp hf
  obtain ⟨x, _, hf⟩ := (mem_support_bind_iff ..).mp hf
  have hfe := eq_of_mem_support_pure _ hf
  subst f
  exact ha (failure_plain pp w D ι hg hs p a b x he)

private lemma inner_alpha_zero {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (ext : ExtractorLaw P) (w : WorldOut P) (D : ExprT P) (ι : Fq P)
    (hg : GoodMark pp w D ι) (hs : markSector D = .alpha)
    (p : Assign P) (a b : Fin 3 → Assign P) (hb : ¬ sampleFailure pp D b) :
    Pr[recoveryFailure pp | do
      let x ← ext pp.S w.out.pv w.st.tr
      pure (⟨w,p,a,b,x⟩ : FullOut P)] = 0 := by
  apply probEvent_eq_zero
  intro f hf he
  obtain ⟨x, _, hf⟩ := (mem_support_bind_iff ..).mp hf
  have hfe := eq_of_mem_support_pure _ hf
  subst f
  exact hb (failure_alpha pp w D ι hg hs p a b x he)

private lemma postWorld_plain_le {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (ext : ExtractorLaw P) (w : WorldOut P) (D : ExprT P) (ι : Fq P)
    (hg : GoodMark pp w D ι) (hs : markSector D = .plain) :
    Pr[recoveryFailure pp | postWorld pp ext w] ≤ Pr[sampleFailure pp D | sampleAssigns pp 3] := by
  unfold postWorld
  apply probEvent_bind_le_of_forall_le
  intro p _
  apply probEvent_bind_le_probEvent
  intro a _ ha
  exact inner_plain_zero pp ext w D ι hg hs (p 0) a ha

private lemma postWorld_alpha_le {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (ext : ExtractorLaw P) (w : WorldOut P) (D : ExprT P) (ι : Fq P)
    (hg : GoodMark pp w D ι) (hs : markSector D = .alpha) :
    Pr[recoveryFailure pp | postWorld pp ext w] ≤ Pr[sampleFailure pp D | sampleAssigns pp 3] := by
  unfold postWorld
  apply probEvent_bind_le_of_forall_le
  intro p _
  apply probEvent_bind_le_of_forall_le
  intro a _
  apply probEvent_bind_le_probEvent
  intro b _ hb
  exact inner_alpha_zero pp ext w D ι hg hs (p 0) a b hb

theorem postWorld_recovery_le {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (ext : ExtractorLaw P) (w : WorldOut P) (D : ExprT P) (ι : Fq P)
    (h : GoodMark pp w D ι) :
    Pr[fun f => ∃ D' ι', GoodMark pp f.w D' ι' ∧
      gradSpan pp (recAssign f.w0 f.w1) D' (markSector D') ≠ jointSpace (markStack D') |
      postWorld pp ext w] ≤
    Pr[fun as : Fin 3 → Assign P => Submodule.span (Fq P)
      (Set.range (fun l => rGrad pp (as l) D (markSector D))) ≠ jointSpace (markStack D) |
      sampleAssigns pp 3] := by
  change Pr[recoveryFailure pp | postWorld pp ext w] ≤ Pr[sampleFailure pp D | sampleAssigns pp 3]
  have hs : markSector D = .plain ∨ markSector D = .alpha := by
    cases markSector D <;> simp
  rcases hs with hs | hs
  · exact postWorld_plain_le pp ext w D ι h hs
  · exact postWorld_alpha_le pp ext w D ι h hs

private lemma postWorld_world {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (ext : ExtractorLaw P) (w : WorldOut P) (f : FullOut P)
    (hf : f ∈ support (postWorld pp ext w)) : f.w = w := by
  unfold postWorld at hf
  obtain ⟨p, _, hf⟩ := (mem_support_bind_iff ..).mp hf
  obtain ⟨a, _, hf⟩ := (mem_support_bind_iff ..).mp hf
  obtain ⟨b, _, hf⟩ := (mem_support_bind_iff ..).mp hf
  obtain ⟨x, _, hf⟩ := (mem_support_bind_iff ..).mp hf
  have hfe := eq_of_mem_support_pure _ hf
  subst f
  rfl

private lemma postWorld_no_good {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (ext : ExtractorLaw P) (w : WorldOut P) (hg : ¬ ∃ D ι, GoodMark pp w D ι) :
    Pr[recoveryFailure pp | postWorld pp ext w] = 0 := by
  apply probEvent_eq_zero
  intro f hf he
  obtain ⟨D, ι, hd, _⟩ := he
  rw [postWorld_world pp ext w f hf] at hd
  exact hg ⟨D,ι,hd⟩

theorem postWorld_recovery_bound {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (ext : ExtractorLaw P) (w : WorldOut P) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ D ι, GoodMark pp w D ι →
      (Pr[fun as : Fin 3 → Assign P => Submodule.span (Fq P)
        (Set.range (fun l => rGrad pp (as l) D (markSector D))) ≠ jointSpace (markStack D) |
        sampleAssigns pp 3]).toReal ≤ ε) :
    Pr[fun f => ∃ D ι, GoodMark pp f.w D ι ∧
      gradSpan pp (recAssign f.w0 f.w1) D (markSector D) ≠ jointSpace (markStack D) |
      postWorld pp ext w] ≤ ENNReal.ofReal ε := by
  classical
  by_cases hg : ∃ D ι, GoodMark pp w D ι
  · obtain ⟨D,ι,hg⟩ := hg
    refine (postWorld_recovery_le pp ext w D ι hg).trans ?_
    exact (ENNReal.le_ofReal_iff_toReal_le probEvent_ne_top hε).mpr (h D ι hg)
  · change Pr[recoveryFailure pp | postWorld pp ext w] ≤ _
    rw [postWorld_no_good pp ext w hg]
    exact zero_le

theorem worldFull_recovery_bound {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P) (m : Msg P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (A : Adversary P)
    (ext : ExtractorLaw P) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ w D ι, GoodMark pp w D ι →
      (Pr[fun as : Fin 3 → Assign P => Submodule.span (Fq P)
        (Set.range (fun l => rGrad pp (as l) D (markSector D))) ≠ jointSpace (markStack D) |
        sampleAssigns pp 3]).toReal ≤ ε) :
    (Pr[fun f => ∃ D ι, GoodMark pp f.w D ι ∧
      gradSpan pp (recAssign f.w0 f.w1) D (markSector D) ≠ jointSpace (markStack D) |
      worldFull pp m A ext]).toReal ≤ ε := by
  apply worldFull_bound_toReal pp m A ext _ ε hε
  intro w
  exact postWorld_recovery_bound pp ext w ε hε (h w)

end Praxis.Proofs.Monitor
