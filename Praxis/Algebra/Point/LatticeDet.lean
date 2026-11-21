import Praxis.Algebra.Point.Definitions

noncomputable section

open Module MeasureTheory

namespace Praxis.Algebra.Point

theorem coordinate_det_eq_vectorDet {e : ℕ} (v : Fin e → E e) :
    (EuclideanSpace.basisFun (Fin e) ℝ).toBasis.det v = vectorDet v := by
  rw [Basis.det_apply]
  rfl

theorem FullLat.det_eq_abs_vectorDet {e : ℕ} (L : FullLat e)
    (b : Basis (Fin e) ℤ L.carrier) :
    L.det = |vectorDet (fun i => (b i : E e))| := by
  rw [FullLat.det, ZLattice.covolume_eq_det_mul_measureReal L.carrier volume b
    (EuclideanSpace.basisFun (Fin e) ℝ).toBasis]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped
    (EuclideanSpace.basisFun (Fin e) ℝ).toBasis volume)]
  simp [(EuclideanSpace.basisFun (Fin e) ℝ).volume_parallelepiped,
    Measure.real, coordinate_det_eq_vectorDet, Function.comp_def]

theorem latticeDetLower : LatticeDetLower := by
  classical
  intro e L v hmem hind
  let := ZLattice.module_finite ℝ L.carrier
  let := ZLattice.module_free ℝ L.carrier
  let b : Basis (Fin e) ℤ L.carrier :=
    (Free.chooseBasis ℤ L.carrier).reindex (Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ,
        finrank_euclideanSpace_fin, Fintype.card_fin]))
  let br := b.ofZLatticeBasis ℝ
  let w := basisOfLinearIndependentOfCardEqFinrank' v hind (by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin])
  let A : Matrix (Fin e) (Fin e) ℤ := fun i j => b.repr ⟨v j, hmem j⟩ i
  have hcast : (A.det : ℝ) = br.det v := by
    rw [Basis.det_apply, Int.cast_det]
    congr 1
    ext i j
    exact (b.ofZLatticeBasis_repr_apply ℝ L.carrier ⟨v j, hmem j⟩ i).symm
  have hnonzero : A.det ≠ 0 := by
    have hreal : br.det v ≠ 0 := by
      simpa [w] using (br.isUnit_det w).ne_zero
    intro hzero
    apply hreal
    rw [← hcast, hzero, Int.cast_zero]
  have hone : (1 : ℝ) ≤ |br.det v| := by
    rw [← hcast]
    exact_mod_cast Int.one_le_abs hnonzero
  have hfactor : vectorDet (fun i => (b i : E e)) * br.det v = vectorDet v := by
    have hbr : ⇑br = fun i => (b i : E e) := by
      funext i
      exact b.ofZLatticeBasis_apply ℝ L.carrier i
    have h := Basis.det_mul_det (EuclideanSpace.basisFun (Fin e) ℝ).toBasis br w
    simpa [coordinate_det_eq_vectorDet, hbr, w] using h
  rw [L.det_eq_abs_vectorDet b, ← hfactor, abs_mul]
  exact le_mul_of_one_le_right (abs_nonneg _) hone

end Praxis.Algebra.Point
