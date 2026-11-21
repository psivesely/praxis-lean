import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Relation

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration

open Classical

namespace ObservedLaw

section Core

variable (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)

lemma observedRun_law :
    evalSPMF (Prod.fst <$> observedRun (ppOf ch S) m A) = evalSPMF (lazyRun ch S m A) := by
  have hworld : Prod.fst <$> observedRun (ppOf ch S) m A = worldRun (ppOf ch S) m A := by
    unfold observedRun worldRun runWith
    simp only [map_bind, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    apply bind_congr
    intro σ
    apply bind_congr
    intro e
    let st : ObsState (ppOf ch S) :=
      ⟨e.2, Coupling.Symbolic.initialise (ppOf ch S) e.1.forms e.1.pv, [], [], none⟩
    have hquery : ∀ q (s : ObsState (ppOf ch S)),
        Prod.map id ObsState.oracle <$> (obsHandler (ppOf ch S) σ e.1.coins q).run s =
          (gameImpl σ q).run s.oracle := by
      intro q s
      simp [obsHandler, Functor.map_map]
    have hr := map_run_simulateQ_eq_of_query_map_eq
      (obsHandler (ppOf ch S) σ e.1.coins) (gameImpl σ) ObsState.oracle hquery
      (A.run e.1.pv e.1.header) st
    have hh := congrArg
      (fun p => (fun z => (⟨σ, e.1, z.1, z.2⟩ : WorldOut P0)) <$> p) hr
    simpa only [Functor.map_map, Function.comp_def, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Prod.map, id_eq, st] using hh
  rw [hworld]
  exact (lazy_law ch S m A).symm

private lemma observedRun_encGame_valid {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (σ : LabelEncoding P) (message : Msg P) (state : OracleState P)
    (e : EncOut P × OracleState P)
    (he : e ∈ support ((encGame σ pp message).run state)) :
    ValidCoins pp.qap e.1.coins := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  unfold encGame at he
  simp only [StateT.run_bind, mem_support_bind_iff] at he
  obtain ⟨seed, _, he⟩ := he
  unfold encAt at he
  simp only [StateT.run_bind, mem_support_bind_iff] at he
  obtain ⟨entries, _, coins, hc, pad, _, final, _, he⟩ := he
  simp only [StateT.run_lift, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hc
  obtain ⟨c, _, rfl⟩ := hc
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at he
  have hcoins : e.1.coins = c.val :=
    congrArg (fun out : EncOut P × OracleState P => out.1.coins) he
  rw [hcoins]
  exact c.property

lemma observedRun_valid :
    ∀ ω ∈ support (observedRun (ppOf ch S) m A),
      ValidCoins (ppOf ch S).qap ω.1.out.coins := by
  intro ω
  unfold observedRun
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  rintro ⟨σ, _, e, _, z, _, rfl⟩
  apply observedRun_encGame_valid (ppOf ch S) σ m OracleState.empty e
  assumption

end Core

end ObservedLaw

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration
