import Praxis.Proofs.Basic
import Praxis.Proofs.Injectivity.Counting
import Praxis.Proofs.Unit.WKey.Polynomial
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Probe.SZ
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Stmt.ProbeSZ

namespace Praxis.Proofs.Unit

open OracleComp OracleSpec

open Praxis.Algebra (Vec)

theorem wkey_vanish (x : Vec (Fq P0) P0.N) (hx : x 0 = 1) (seed : Seed P0) :
    (Pr[fun HF : FormOracle P0 => wKey (formsOf HF seed) x = 0 | $ᵗ (FormOracle P0)]).toReal ≤
      2 / (P0.q : ℝ) := by
  classical
  let f := WitnessKey.oracleMap (P := P0) seed
  let p := WitnessKey.weightPoly (P := P0) x
  have hn : 0 < P0.n := by decide
  letI := SampleableType.ofFintype (Fin (WitnessKey.K P0) → Fq P0)
  have hlaw := Injectivity.uniform_map_addHom f (WitnessKey.oracleMap_surjective seed)
  have hevent (HF : FormOracle P0) :
      wKey (formsOf HF seed) x = 0 ↔ MvPolynomial.eval (f HF) p = 0 := by
    change wKey (formVec (HF seed)) x = 0 ↔
      MvPolynomial.eval (WitnessKey.assignment (HF seed)) (WitnessKey.weightPoly x) = 0
    rw [WitnessKey.eval_weightPoly _ _ hn]
  have hprob :
      Pr[fun HF : FormOracle P0 => wKey (formsOf HF seed) x = 0 | $ᵗ (FormOracle P0)] =
      Pr[fun a : Fin (WitnessKey.K P0) → Fq P0 => MvPolynomial.eval a p = 0 |
        $ᵗ (Fin (WitnessKey.K P0) → Fq P0)] := by
    simp_rw [hevent]
    change Pr[(fun a => MvPolynomial.eval a p = 0) ∘ f | $ᵗ (FormOracle P0)] = _
    rw [← probEvent_map]
    have hh := congrArg (fun law : SPMF (Fin (WitnessKey.K P0) → Fq P0) =>
      probEvent law (fun a => MvPolynomial.eval a p = 0)) hlaw
    simpa only [probEvent_evalSPMF] using hh
  rw [hprob]
  have hb := Algebra.ProbeSZ.uniformProb_polynomial_zero (d := 2) p
    (WitnessKey.weightPoly_ne_zero x hx hn) (WitnessKey.degree_weightPoly x)
  rw [probEvent_uniformSample, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, ← Fintype.card_subtype]
  simpa only [Algebra.ProbeSZ.uniformProb, Nat.card_eq_fintype_card, Nat.cast_ofNat] using hb

end Praxis.Proofs.Unit
