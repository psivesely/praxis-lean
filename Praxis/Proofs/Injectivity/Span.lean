import Praxis.Proofs.Injectivity.Core
import Praxis.Proofs.Injectivity.Counting
import Praxis.Proofs.Injectivity.SketchMap
import Praxis.Constants
import Praxis.Extractor
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec

set_option maxRecDepth 2048 in

theorem jse_span (W : Stack P0) (hdim : Module.finrank (Fq P0) (jointSpace W) ≤ dimMax)
    (σ : Sector) :
    (Pr[fun sk : Sketches P0 =>
        Submodule.span (Fq P0) (Set.range fun l : Fin dimMax => ∑ c, (W c).mulVec (sk c l σ)) ≠
          jointSpace W |
      sketchLaw]).toReal ≤ (Constants.extractor_recovery_failure_per_sector : ℝ) := by
  classical
  let d := Module.finrank (Fq P0) (jointSpace W)
  let e : jointSpace W ≃ₗ[Fq P0] (Fin d → Fq P0) :=
    (Module.finBasis (Fq P0) (jointSpace W)).equivFun
  let f := coordinateSketchMap W σ e
  letI := SampleableType.ofFintype (Sketches P0)
  letI := SampleableType.ofFintype (Fin 3 → Fin d → Fq P0)
  have hlaw := uniform_map_addHom f.toAddMonoidHom (coordinateSketchMap_surjective W σ e)
  have hevent (sk : Sketches P0) :
      (Submodule.span (Fq P0) (Set.range fun l : Fin dimMax =>
        ∑ c, (W c).mulVec (sk c l σ)) ≠ jointSpace W) ↔
      Submodule.span (Fq P0) (Set.range (f sk)) ≠ ⊤ := by
    have hsub := Submodule.span_val_image_eq_iff (jointSpace W)
      (Set.range (fun l : Fin 3 => jointSketchMap W σ sk l))
    rw [← Set.range_comp] at hsub
    have hval : (fun l : Fin 3 => ((jointSketchMap W σ sk l : jointSpace W) :
        Algebra.Vec (Fq P0) P0.N)) =
        (fun l : Fin 3 => ∑ c, (W c).mulVec (sk c l σ)) := rfl
    change (Submodule.span (Fq P0) (Set.range (fun l : Fin 3 =>
      ((jointSketchMap W σ sk l : jointSpace W) : Algebra.Vec (Fq P0) P0.N))) = jointSpace W ↔
      Submodule.span (Fq P0) (Set.range (fun l : Fin 3 => jointSketchMap W σ sk l)) = ⊤) at hsub
    rw [hval] at hsub
    have hcoord := span_equiv_eq_top_iff e (fun l => jointSketchMap W σ sk l)
    exact (hsub.trans hcoord.symm).not

  have hprob :
      Pr[fun sk : Sketches P0 =>
        Submodule.span (Fq P0) (Set.range fun l : Fin dimMax =>
          ∑ c, (W c).mulVec (sk c l σ)) ≠ jointSpace W | sketchLaw] =
      Pr[fun s : Fin 3 → Fin d → Fq P0 =>
        Submodule.span (Fq P0) (Set.range s) ≠ ⊤ | $ᵗ (Fin 3 → Fin d → Fq P0)] := by
    simp_rw [hevent]
    change Pr[(fun s => Submodule.span (Fq P0) (Set.range s) ≠ ⊤) ∘ f |
      $ᵗ (Sketches P0)] = _
    rw [← probEvent_map]
    change evalSPMF (f <$> ($ᵗ (Sketches P0))) =
      evalSPMF ($ᵗ (Fin 3 → Fin d → Fq P0)) at hlaw
    have hh := congrArg (fun law : SPMF (Fin 3 → Fin d → Fq P0) =>
      probEvent law (fun s => Submodule.span (Fq P0) (Set.range s) ≠ ⊤)) hlaw
    simpa only [probEvent_evalSPMF] using hh
  rw [hprob]
  have hb := coordinate_span_failure_bound (K := Fq P0) (d := d) hdim
  convert hb using 1 <;>
    norm_num [Fq, P0, Params.main, Constants.q,
      Constants.extractor_recovery_failure_per_sector]

end Praxis.Proofs.Injectivity
