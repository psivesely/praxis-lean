import Praxis.Proofs.View.Locus
import Praxis.Proofs.View.SZ.Degree
import Praxis.Proofs.View.SZ.Finish
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Proofs.Degree
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.View.SZ.Bound
import Praxis.Proofs.View.SZ.Eval
import Praxis.Proofs.View.SZ.Grid
import Praxis.Proofs.View.SZ.Model
import Praxis.Proofs.View.SZ.PolyDegree
import Praxis.Params
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open OracleComp OracleSpec

open Praxis.Algebra (Vec)

set_option linter.constructorNameAsVariable false in

theorem view_sz (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) (r : Vec (Fq P0) P0.N) (ι : Fq P0)
    (h : ¬ IdentityAtR (ppOf ch S) (formVec A) r D ι) :
    (Pr[fun c => valT (ppOf ch S) (formVec A) ⟨c.1, r⟩ D = ι * kappa (ppOf ch S) c.1 |
      coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ) := by
  classical
  let pp := ppOf ch S
  let p := SZ.differenceP pp (formVec A) r D ι
  have hD : ValidQAP pp.qap S := QAP.domainMap_valid ch S
  have hp : p ≠ 0 := SZ.differenceP_ne_zero ch S A D r ι h
  have hd : p.totalDegree ≤ Constants.view_degree_total :=
    SZ.differenceP_degree_of_e2 pp S hD (formVec A) r D ι
      (SZ.e2P_degree pp S hD (formVec A) r)
  have hcard : Fintype.card (QAPIndex P0) ≤ Constants.D := by
    rw [SZ.qapIndex_card]
    decide
  have hm : 0 < P0.q - Constants.D := by decide
  have hs : ∀ i, P0.q - Constants.D ≤ (sampleSet pp.qap i).card :=
    sampleSet_card_lower pp.qap Constants.D hcard (by decide) (by decide)
  have hb := coinLaw_root_bound pp p hp (P0.q - Constants.D) Constants.view_degree_total hm hd hs
  have heq : (Pr[fun c => valT pp (formVec A) ⟨c.1, r⟩ D = ι * kappa pp c.1 |
      coinLaw pp]) = (Pr[fun c => MvPolynomial.eval (coinVar c.1) p = 0 | coinLaw pp]) := by
    apply probEvent_congr' _ rfl
    intro c hc
    have he := SZ.eval_differenceP pp c.1 (formVec A) r D ι c.2
    have hn := SZ.denom_ne_zero pp.qap c.1 c.2
    change _ ↔ MvPolynomial.eval (coinVar c.1) (SZ.differenceP pp (formVec A) r D ι) = 0
    rw [he, mul_eq_zero, sub_eq_zero]
    simp [hn]
  rw [heq]
  have hreal : ((P0.q - Constants.D : ℕ) : ℝ) = (Constants.q : ℝ) - Constants.D := by
    rw [Nat.cast_sub (by decide : Constants.D ≤ P0.q)]
    rfl
  change (Pr[fun c => MvPolynomial.eval (coinVar c.1) p = 0 | coinLaw pp]).toReal ≤ _ at hb
  rw [hreal] at hb
  exact hb.trans Degree.degree_le_eps.1

end Praxis.Proofs.View
