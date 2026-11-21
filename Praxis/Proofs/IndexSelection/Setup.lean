import Praxis.Proofs.Basic
import Praxis.Proofs.IndexSelection.Setup.Bounds
import Praxis.Proofs.IndexSelection.Setup.Lengths
import Praxis.Constants
import Praxis.Enc
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Games
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.IndexSelection

open Praxis.Algebra (Vec)

theorem jset_draw (P : Params) (hP : P = P0) :
    WithinUnits (drawSketchesC (P := P)) Constants.running_time_extractor_sketch_draws := by
  have h : WithinUnits (drawSketchesC (P := P)) ((g2Keys P).length * (P.N + 1)) := by
    unfold drawSketchesC
    have ht := funOfM_units (g2Keys P) 0 (fun _ => vecOfM fun _ => sampleF) (P.N + 1) (by
      intro x hx
      simpa using vecOfM_units (fun _ : Fin (P.N + 1) => (sampleF : UnitComp P.q (ZMod P.q))) 1
        (fun _ => sampleF_units))
    simpa [WithinUnits] using OracleComp.isQueryBoundP_bind ht
      (fun t _ => OracleComp.isQueryBoundP_pure isUnit (fun c l s => t (c, l, s)) 0)
  apply h.mono
  rw [keys_length, hP]
  norm_num [P0, Params.main, Constants.K1, Constants.K2, Constants.N,
    Constants.running_time_extractor_sketch_draws]

theorem jset_init (P : Params) [Fact (Nat.Prime P.q)] (hP : P = P0) (σ : LabelEncoding P)
    (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N) (c : Coins P) (sk : Sketches P) :
    WithinUnits (initStateC (pubView σ pp v c) sk)
      (Constants.running_time_extractor_R1_total_scalars +
        Constants.running_time_extractor_label_table) := by
  have hN : 0 < P.N := by
    rw [hP]
    decide +kernel
  have h := initStateC_units (pubView σ pp v c) sk hN (filter_cells P)
  apply h.mono
  have hg1 := g1_length_bound P
  have hg2 := g2_weight P
  simp only [initCost] at hg2
  simp only [pubView, List.length_cons, List.length_map, List.length_nil,
    List.map_cons, List.map_map, List.sum_cons, Function.comp_def, initCost]
  rw [hg2]
  generalize hlen : (g1Order P).length = len at hg1 ⊢
  clear hlen
  rw [hP] at hg1 ⊢
  norm_num [P0, Params.main, Constants.K1, Constants.K2, Constants.N, Constants.E1,
    Constants.U, Constants.E1p, Constants.M_q, Constants.W_r, Constants.n,
    Constants.running_time_extractor_R1_total_scalars,
    Constants.running_time_extractor_label_table] at hg1 ⊢
  omega

end Praxis.Proofs.IndexSelection
