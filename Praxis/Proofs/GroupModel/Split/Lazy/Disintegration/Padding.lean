import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.Rank4
import Praxis.Constants
import Praxis.Domain
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingInitial
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Bounds.Rank
import Praxis.Stack
import Praxis.Algebra.Definitions.Stack

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable {ch : AdmissibleChoice P0} {S : Relation P0}

lemma padding_test (i : Kind) : Nonempty (Bounds ch S i) := by
  cases i with
  | light =>
      let D : ExprT P0 := (fun ab => match ab with
        | (some (.L1 _ i), some (.ZeroCoordinate .plain _ j)) => if i = j then 1 else 0
        | _ => 0, 0)
      have hplain : exprStack D .plain = (fun _ => 1) := by
        funext c i j
        simp [exprStack, D, Matrix.one_apply]
      have hn : exprStack D .plain ≠ 0 := by
        rw [hplain]
        intro hz
        have hh := congrArg (fun W : Stack P0 => W (0, (.E, 0)) 0 0) hz
        simpa using hh
      have hm : markStack D = (fun _ => 1) := by
        unfold markStack markSector
        rw [if_neg hn, hplain]
      refine ⟨.light 0 D 0 (Praxis.Proofs.Rank4.rank_four _ ?_)⟩
      let W := Praxis.Bounds.Rank.stackAsBase (markStack D)
      let c := Praxis.Bounds.Rank.cellEquiv P0 (0, (.E, 0))
      have hc : W c = 1 := by simp [W, c, Praxis.Bounds.Rank.stackAsBase, hm]
      have htop : Algebra.stackSpace W = ⊤ := by
        rw [eq_top_iff, ← (Pi.basisFun k (Fin (P0.N + 1))).span_eq, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        refine Submodule.subset_span ⟨(c, j), ?_⟩
        funext i
        simp [Algebra.stackRows, hc, Matrix.one_eq_pi_single]
      have hr : Algebra.stackRank W = P0.N + 1 := by
        rw [Algebra.stackRank, htop, finrank_top, Module.finrank_fin_fun]
      rw [hr]
      norm_num [lightRank, P0, Params.main, Constants.N]
  | field =>
      refine ⟨.source1 (Pi.single none 1) 0 0 ?_⟩
      intro h
      obtain ⟨c⟩ := (inferInstance : Nonempty (CoinDomain (ppOf ch S)))
      have he := h ⟨c.val, 0⟩ c.property
      simpa [Coupling.Symbolic.val1_single, e1At] using he
  | guess =>
      refine ⟨.guess {
        polynomial := 1
        nonzero := one_ne_zero
        nc := 0
        ng := 0
        dc := 0
        dg := 0
        used := 0
        degree := by simp [BiDegree]
        coin_slack := by norm_num [Constants.eps_f_numerator]
        guess_degree := by omega
        used_le := by omega
        pool := fun _ _ => Finset.univ
        nonempty := fun _ _ => Finset.univ_nonempty
        coin_pool := by simp
        guess_pool := by simp }⟩
  | reservoir =>
      refine ⟨.reservoir Finset.univ Finset.univ_nonempty ?_ 0⟩
      norm_num [Label, P0, Params.main, Constants.label_bits, Constants.N_free]
  | kdf => exact ⟨.kdf 0⟩
  | seed => exact ⟨.seed 0⟩

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration
