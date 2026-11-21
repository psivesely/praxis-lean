import Praxis.Algebra.Point.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open MeasureTheory

open scoped Pointwise

namespace Praxis.Algebra.Point

theorem simplexVolumeDet_of_stdSimplexVolume
    (hstd : StdSimplexVolume) : SimplexVolumeDet := by
  classical
  intro e v _
  let b := (EuclideanSpace.basisFun (Fin e) ℝ).toBasis
  let L : E e →ₗ[ℝ] E e := b.constr ℝ (edgeVectors v)
  let A : E e →ᵃ[ℝ] E e :=
    (AffineEquiv.constVAdd ℝ (E e) (v 0)).toAffineMap.comp L.toAffineMap
  have hvertices (i : Fin (e + 1)) : A (standardVertices e i) = v i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change v 0 + L 0 = v 0
      rw [map_zero, add_zero]
    · change v 0 + L (b j) = v j.succ
      rw [Module.Basis.constr_basis]
      simp only [edgeVectors, add_sub_cancel]
  have hpoints :
      A '' (simplexPoints (standardVertices e) : Set (E e)) =
        (simplexPoints v : Set (E e)) := by
    simp only [simplexPoints, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hvertices)
  have hhull : A '' convexHull ℝ (simplexPoints (standardVertices e) : Set (E e)) =
      convexHull ℝ (simplexPoints v : Set (E e)) := by
    rw [A.image_convexHull, hpoints]
  have hdet : LinearMap.det L = vectorDet (edgeVectors v) := by
    rw [← LinearMap.det_toMatrix b]
    unfold vectorDet
    congr 1
    ext i j
    simp only [LinearMap.toMatrix_apply, L, Module.Basis.constr_basis, b,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  change (volume (convexHull ℝ (simplexPoints v : Set (E e)))).toReal = _
  calc
    _ = (volume (A '' convexHull ℝ
        (simplexPoints (standardVertices e) : Set (E e)))).toReal := by rw [hhull]
    _ = (volume (L '' convexHull ℝ
        (simplexPoints (standardVertices e) : Set (E e)))).toReal := by
      change (volume (((fun x : E e => v 0 + x) ∘ L) '' convexHull ℝ
        (simplexPoints (standardVertices e) : Set (E e)))).toReal = _
      rw [Set.image_comp]
      change (volume (v 0 +ᵥ (L '' convexHull ℝ
        (simplexPoints (standardVertices e) : Set (E e))))).toReal = _
      rw [measure_vadd]
    _ = |vectorDet (edgeVectors v)| * volHull (simplexPoints (standardVertices e)) := by
      rw [Measure.addHaar_image_linearMap, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg _), hdet]
      rfl
    _ = |vectorDet (edgeVectors v)| / (e.factorial : ℝ) := by
      rw [hstd e, mul_one_div]

end Praxis.Algebra.Point
