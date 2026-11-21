import Praxis.Algebra.Point.Definitions

namespace Praxis.Algebra.Point

theorem edgeVectors_mem_of_coset {e : ℕ} (L : FullLat e) (a : E e)
    (v : Fin (e + 1) → E e) (hv : ∀ i, v i - a ∈ L.carrier) (i : Fin e) :
    edgeVectors v i ∈ L.carrier := by
  have h := L.carrier.sub_mem (hv i.succ) (hv 0)
  simpa only [sub_sub_sub_cancel_right, edgeVectors] using h

theorem linearIndependent_edgeVectors {e : ℕ} (v : Fin (e + 1) → E e)
    (hv : AffineIndependent ℝ v) : LinearIndependent ℝ (edgeVectors v) := by
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ v 0).mp hv
  exact h.comp (fun i : Fin e => ⟨i.succ, Fin.succ_ne_zero i⟩)
    (fun _ _ hij => Fin.succ_injective _ (congrArg Subtype.val hij))

theorem simplexVolumeLower_of_det (hvolume : SimplexVolumeDet)
    (hlattice : LatticeDetLower) : SimplexVolumeLower := by
  intro e L a v hcoset hindependent
  rw [hvolume e v hindependent]
  exact div_le_div_of_nonneg_right
    (hlattice e L (edgeVectors v) (edgeVectors_mem_of_coset L a v hcoset)
      (linearIndependent_edgeVectors v hindependent))
    (Nat.cast_nonneg e.factorial)

end Praxis.Algebra.Point
