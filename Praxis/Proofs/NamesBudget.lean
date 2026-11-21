import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesMonitor
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Cap
import Praxis.Proofs.NamesReservoir
import Praxis.Params
import Praxis.Setting

namespace Praxis.Proofs.Names.Game

open OracleComp OracleSpec

variable {P : Params}

theorem answer_bound (src : LabelEncoding P) (issued : Finset (Label P))
    (qr : GQuery P) (st : OracleState P) :
    IsQueryBoundP ((answer src issued qr).run st) Reservoir.isProbe 3 := by
  classical
  cases qr with
  | lin s a b u v =>
    cases s
    · simp [answer]
    · simp [answer]
    · simp only [answer, StateT.run_bind]
      apply isQueryBoundP_bind (m := 2) (decodeGT_bound u st)
      intro x _
      apply isQueryBoundP_bind (m := 1) (decodeGT_bound v x.2)
      intro y _
      cases x.1 <;> cases y.1 <;>
        simp [StateT.run_map, isQueryBoundP_map_iff, encodeGT_bound]
  | pair u v =>
    simp only [answer]
    split <;> simp [StateT.run_map, isQueryBoundP_map_iff]
    exact (encodeGT_bound _ st).mono (by omega)
  | name v =>
    simp only [answer]
    split
    · simp only [StateT.run_bind]
      apply (isQueryBoundP_bind (decodeGT_bound v st) ?_).mono (show 1+1 ≤ 3 by omega)
      intro x _
      cases x.1 <;> simp [StateT.run_bind, StateT.run_pure, StateT.run_map,
        isQueryBoundP_map_iff, encodeGT_bound]
    · simp

theorem group_bound (src : LabelEncoding P) (qr : GQuery P) (st : OracleState P) :
    IsQueryBoundP ((group src qr).run st) Reservoir.isProbe 3 := by
  classical
  simp only [group, StateT.run_bind, StateT.run_get, pure_bind]
  apply (isQueryBoundP_bind (m := 0) (answer_bound src st.issuedT qr st) ?_).mono (by omega)
  intro x _
  split <;> simp [StateT.run_bind, StateT.run_modify, liftGame_bound]

theorem resolvedKdf_bound (κ : Fq P) (pad : Msg P) (nm : ClassName P) (st : OracleState P) :
    IsQueryBoundP ((resolvedKdf κ pad nm).run st) Reservoir.isProbe 2 := by
  simp only [resolvedKdf, StateT.run_bind, StateT.run_modify, pure_bind]
  apply (isQueryBoundP_bind (m := 1) (decodeGT_bound _ _) ?_).mono (by omega)
  intro x _
  apply (isQueryBoundP_bind (m := 0) (decodeGT_bound _ _) ?_).mono (by omega)
  intro y _
  split <;> simp [StateT.run_pure, liftGame_bound]

theorem kdf_bound (κ : Fq P) (pad : Msg P) (q : KdfQuery P) (st : OracleState P) :
    IsQueryBoundP ((kdf κ pad q).run st) Reservoir.isProbe 2 := by
  simp only [kdf, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp [resolvedKdf_bound]

def probeCost (t : (AdvModel P).Domain) : ℕ :=
  3 * callCost t .group + 2 * callCost t .kdf

theorem handler_bound [NeZero P.q] (src : LabelEncoding P) (κ : Fq P) (pad : Msg P)
    (t : (AdvModel P).Domain) (st : OracleState P) :
    IsQueryBoundP ((handler src κ pad t).run st) Reservoir.isProbe (probeCost t) := by
  rcases t with (((n | qr) | i) | q)
  · simpa [handler, probeCost, callCost, isGroupQuery, isKDFQuery] using
      liftGame_bound (P := P) (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (GameM P)) n) st
  · simpa [handler, probeCost, callCost, isGroupQuery, isKDFQuery] using group_bound src qr st
  · simpa [handler, probeCost, callCost, isGroupQuery, isKDFQuery] using liftGame_bound (hfLazy i) st
  · simpa [handler, probeCost, callCost, isGroupQuery, isKDFQuery] using kdf_bound κ pad q st

theorem capComp_bound [NeZero P.q] (src : LabelEncoding P) (κ : Fq P) (pad : Msg P)
    (oa : OracleComp (AdvModel P) Bool) (left : QueryCount CallKind) (st : OracleState P) :
    IsQueryBoundP ((simulateQ (handler src κ pad) (capComp oa left)).run st)
      Reservoir.isProbe (3 * left .group + 2 * left .kdf) := by
  induction oa using OracleComp.inductionOn generalizing left st with
  | pure b => simp
  | query_bind t k ih =>
    rw [capComp_query_bind]
    split_ifs with ht
    · simp only [simulateQ_query_bind, StateT.run_bind]
      apply (isQueryBoundP_bind (handler_bound src κ pad t st) ?_).mono
        (show probeCost t + (3 * (left - callCost t) .group +
          2 * (left - callCost t) .kdf) ≤ 3 * left .group + 2 * left .kdf from ?_)
      · intro u _
        exact ih u.1 (left - callCost t) u.2
      · have hg := ht .group
        have hk := ht .kdf
        change callCost t .group ≤ left .group at hg
        change callCost t .kdf ≤ left .kdf at hk
        simp only [probeCost, Pi.sub_apply]
        omega
    · simp

theorem initial_bound [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (pp : PublicParams P)
    (forms : FormMatrix P) (c : Coins P) (hdr : Header P)
    (hf : Seed P × FormIndex P → Option (Rq P)) (st : OracleState P) :
    IsQueryBoundP ((initial src pp forms c hdr hf).run st) Reservoir.isProbe 2 := by
  simp only [initial, StateT.run_bind]
  apply (isQueryBoundP_bind (m := 1) (encodeGT_bound _ _) ?_).mono (by omega)
  intro x _
  apply (isQueryBoundP_bind (m := 0) (encodeGT_bound _ _) ?_).mono (by omega)
  intro y _
  simp [StateT.run_set, StateT.run_pure]

theorem program_bound [Fact (Nat.Prime P.q)] (src : LabelEncoding P) (pp : PublicParams P)
    (forms : FormMatrix P) (c : Coins P) (hdr : Header P) (pad : Msg P)
    (hf : Seed P × FormIndex P → Option (Rq P)) (A : Adversary P) (Q QH : ℕ) :
    IsQueryBoundP (program src pp forms c hdr pad hf A Q QH) Reservoir.isProbe
      (observerBudget Q QH) := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [program, StateT.run_bind]
  apply (isQueryBoundP_bind (initial_bound src pp forms c hdr hf _) ?_).mono
    (show 2 + (3*Q+2*QH) ≤ observerBudget Q QH by unfold observerBudget; omega)
  intro x _
  simpa [StateT.run_bind, StateT.run_pure, ← map_eq_bind_pure_comp,
    isQueryBoundP_map_iff, cap, budgets] using
      capComp_bound src (kappa pp c) pad (A.run x.1.pv x.1.header) (budgets Q QH) x.2

end Praxis.Proofs.Names.Game
