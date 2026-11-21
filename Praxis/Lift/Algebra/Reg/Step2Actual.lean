import Praxis.Lift.Algebra.Reg.Step2Geometry
import Praxis.Lift.Algebra.Reg.Rank3
import Praxis.Lift.Algebra.Reg.Promote2
import Praxis.Algebra.Point.Count
import Praxis.Algebra.Point.VertexGain
import Praxis.Algebra.Point.Pyramid
import Praxis.Algebra.Point.Layer
import Praxis.Algebra.Point.SimplexLower
import Praxis.Algebra.Point.SimplexDet
import Praxis.Algebra.Point.StdSimplex
import Praxis.Algebra.Point.LatticeDet
import Praxis.Algebra.Point.Exposed
import Praxis.Algebra.Point.Dim0
import Praxis.Algebra.Point.Dim1
import Praxis.Algebra.Point.Dim2
import Praxis.Algebra.Point.Dim3
import Praxis.Algebra.Trim.Assemble
import Praxis.Algebra.Trim.Coeff
import Praxis.Algebra.Trim.UniformMGF
import Praxis.Algebra.Power.Ceiling
import Praxis.Algebra.Power.Stretch
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Lift.Algebra.Reg.Pivot2
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Algebra.Reg.Step2
import Praxis.Lift.Algebra.Trans.Definitions
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Power.Definitions
import Praxis.Algebra.Prefix.Chain
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Trim.Tensor
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Step2.Actual

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open scoped BigOperators Matrix

theorem trim : Algebra.Trim.TrimForIntLat :=
  Algebra.Trim.trimForIntLat (Algebra.Trim.gridDirectionalMGF_of_uniformGridMGF
    (Algebra.Trim.uniform_grid_mgf Algebra.Trim.sinhDivLeExp))

theorem simplex_lower : Algebra.Point.SimplexVolumeLower :=
  Algebra.Point.simplexVolumeLower_of_det
    (Algebra.Point.simplexVolumeDet_of_stdSimplexVolume Algebra.Point.stdSimplexVolume)
    Algebra.Point.latticeDetLower

theorem simplex_count (e : ℕ) : Algebra.Point.SimplexCount e :=
  Algebra.Point.simplexCount (Algebra.Point.VertexGain.vertexRemovalGain simplex_lower Algebra.Point.exposedPoint)
    Algebra.Point.pyramidVolume Algebra.Point.layerSpacing simplex_lower
    Algebra.Point.exposedPoint Algebra.Point.countDim0 Algebra.Point.countDim1 e

theorem planar : Algebra.Point.PlanarCount :=
  Algebra.Point.planarCount_of_simplexCount (simplex_count 2)

theorem section3 : Algebra.Point.SectionCount3 :=
  Algebra.Point.sectionCount3 (simplex_count 3) simplex_lower

theorem power : Algebra.Power.StretchEstimate :=
  Algebra.Power.stretchEstimate_of_ceilingPower Algebra.Power.ceilingPower_holds

theorem rank3 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 3) : Rank3Height P G L :=
  Algebra.Reg.rank3_height P G L (Algebra.Prefix.integer_mass_height L G P.g)

noncomputable def events {n : ℕ} {L : IntLat (Fin n) 2}
    (R : Pivot2.Presentation L) (P : VITParameters) (G : Fin n → ℕ)
    (hG : GridBudget P.toVITData G) (hpos : ∀ i, 0 < G i)
    (hm : P.theta0 - 30 * P.eps ≤ L.mZ G) :
    (j : Fin (n-2+1)) → Geometry.CurrentEvent P (R.grids G j) (R.lattices j) :=
  (Geometry.exists_presentation_events R P G hG hpos hm trim).choose

theorem hstep_actual {n : ℕ} {L : IntLat (Fin n) 2}
    (R : Pivot2.Presentation L) (P : VITParameters) (G : Fin n → ℕ)
    (hG : GridBudget P.toVITData G) (hpos : ∀ i, 0 < G i)
    (hm : P.theta0 - 30 * P.eps ≤ L.mZ G)
    (hStretch : Algebra.Power.StretchEstimate) (hT : Algebra.Trans.Transition32 P)
    (hrank3 : ∀ (j : Fin (n-2+1)) (L3 : IntLat (Fin (j.val+2)) 3),
      Rank3Height P (R.grids G j) L3) :
    let C := events R P G hG hpos hm
    ∀ j : Fin (n-2),
      ordinaryNormals (R.grids G j.succ) (C j.succ).event = (R.lattices j.succ).carrier →
      (ordinaryNormals (R.grids G j.castSucc) (C j.castSucc).event =
          (R.lattices j.castSucc).carrier ∧
        (((R.lattices j.succ).mZ (R.grids G j.succ) * ((R.lattices j.succ).H : ℝ)) ^
          (P.L0 - 1)) * (R.lattices j.succ).mZ (R.grids G j.succ) ≤
        (((R.lattices j.castSucc).mZ (R.grids G j.castSucc) *
          ((R.lattices j.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (R.lattices j.castSucc).mZ (R.grids G j.castSucc)) ∨
      ((R.lattices j.succ).mZ (R.grids G j.succ) * ((R.lattices j.succ).H : ℝ) ≤
          P.A * P.D * P.C3 / (P.g : ℝ)^2 ∧
        (R.lattices j.succ).mZ (R.grids G j.succ) ≤ (P.g : ℝ)^(-(3 : ℤ)) + P.eps) := by
  let C := events R P G hG hpos hm
  exact Presentation.hstep R P G hG hpos hm (fun j => (C j).event)
    (fun j => (C j).target) (fun j => (C j).subset_fibre) (fun j => (C j).retained)
    hStretch hT planar section3 trim hrank3
    (Geometry.exists_presentation_events R P G hG hpos hm trim).choose_spec

theorem hstep_actual_of_transition {n : ℕ} {L : IntLat (Fin n) 2}
    (R : Pivot2.Presentation L) (P : VITParameters) (G : Fin n → ℕ)
    (hG : GridBudget P.toVITData G) (hpos : ∀ i, 0 < G i)
    (hm : P.theta0 - 30 * P.eps ≤ L.mZ G) (hT : Algebra.Trans.Transition32 P) :
    let C := events R P G hG hpos hm
    ∀ j : Fin (n-2),
      ordinaryNormals (R.grids G j.succ) (C j.succ).event = (R.lattices j.succ).carrier →
      (ordinaryNormals (R.grids G j.castSucc) (C j.castSucc).event =
          (R.lattices j.castSucc).carrier ∧
        (((R.lattices j.succ).mZ (R.grids G j.succ) * ((R.lattices j.succ).H : ℝ)) ^
          (P.L0 - 1)) * (R.lattices j.succ).mZ (R.grids G j.succ) ≤
        (((R.lattices j.castSucc).mZ (R.grids G j.castSucc) *
          ((R.lattices j.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (R.lattices j.castSucc).mZ (R.grids G j.castSucc)) ∨
      ((R.lattices j.succ).mZ (R.grids G j.succ) * ((R.lattices j.succ).H : ℝ) ≤
          P.A * P.D * P.C3 / (P.g : ℝ)^2 ∧
        (R.lattices j.succ).mZ (R.grids G j.succ) ≤ (P.g : ℝ)^(-(3 : ℤ)) + P.eps) :=
  hstep_actual R P G hG hpos hm power hT (fun _ L3 => rank3 P _ L3)

end Algebra.Reg.Step2.Actual

end Praxis.Lift
