import Praxis.Algebra.Point.Definitions
import Mathlib.LinearAlgebra.Basis.Fin

noncomputable section

open Module MeasureTheory

namespace Praxis.Algebra.Point

theorem latticeInSubspace_discrete {e : ℕ} (L : FullLat e)
    (H : Submodule ℝ (E e)) : DiscreteTopology (latticeInSubspace L.carrier H) :=
  ZLattice.comap_discreteTopology ℝ L.carrier continuous_subtype_val H.subtype_injective

theorem latticeInSubspace_isZLattice {e : ℕ} (L : FullLat e)
    (H : Submodule ℝ (E e)) (hrat : LatticeRational L.carrier H) :
    haveI := latticeInSubspace_discrete L H
    IsZLattice ℝ (latticeInSubspace L.carrier H) := by
  have := latticeInSubspace_discrete L H
  constructor
  have himage : H.subtype '' (latticeInSubspace L.carrier H : Set H) =
      (L.carrier : Set (E e)) ∩ (H : Set (E e)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · rintro ⟨hL, hH⟩
      exact ⟨⟨x, hH⟩, hL, rfl⟩
  apply (Submodule.map_injective_of_injective H.subtype_injective).eq_iff.mp
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, himage]
  exact hrat

private theorem orthonormal_fundamentalDomain_real {F ι : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ F) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  change (volume (parallelepiped o)).toReal = 1
  rw [o.volume_parallelepiped]
  simp

theorem covolume_le_basis_volume {F ι : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [Fintype ι]
    (L : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℝ F) (hb : ∀ i, b i ∈ L) :
    ZLattice.covolume L ≤ volume.real (ZSpan.fundamentalDomain b) := by
  let M := Submodule.span ℤ (Set.range b)
  have hML : M ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hindex := ZLattice.covolume_div_covolume_eq_relIndex' M L hML
  have hpos : 0 < (M.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    rw [← hindex]
    exact div_pos (ZLattice.covolume_pos M) (ZLattice.covolume_pos L)
  have hone : (1 : ℝ) ≤ (M.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (by exact_mod_cast hpos :
      0 < M.toAddSubgroup.relIndex L.toAddSubgroup))
  rw [← hindex] at hone
  have hle := (le_div_iff₀ (ZLattice.covolume_pos L)).mp hone
  rw [one_mul] at hle
  rwa [ZLattice.covolume_eq_measure_fundamentalDomain M volume
    (ZSpan.isAddFundamentalDomain b volume)] at hle

private theorem exists_adapted_orthonormal {n : ℕ} (H : Submodule ℝ (E (n + 1)))
    (oH : OrthonormalBasis (Fin n) ℝ H) :
    ∃ o : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)),
      ∀ i, o i.succ = (oH i : E (n + 1)) := by
  classical
  let s : Set (Fin (n + 1)) := Set.range Fin.succ
  let w : Fin (n + 1) → E (n + 1) := Fin.cons 0 (fun i => (oH i : E (n + 1)))
  have hw : Orthonormal ℝ (s.domRestrict w) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    obtain ⟨i, hi⟩ := i.property
    obtain ⟨j, hj⟩ := j.property
    have h := orthonormal_iff_ite.mp oH.orthonormal i j
    simpa [w, Set.domRestrict, ← hi, ← hj, Subtype.ext_iff] using h
  obtain ⟨o, ho⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by simp [E])
  exact ⟨o, fun i => by simpa [w] using ho i.succ ⟨i, rfl⟩⟩

private theorem adapted_inner_zero {n : ℕ} (H : Submodule ℝ (E (n + 1)))
    (oH : OrthonormalBasis (Fin n) ℝ H)
    (o : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)))
    (ho : ∀ i, o i.succ = (oH i : E (n + 1))) (x : H) :
    inner ℝ (o 0) (x : E (n + 1)) = 0 := by
  have horth : (o 0) ∈ Hᗮ := by
    have hspan : Submodule.span ℝ (Set.range (fun i => (oH i : E (n + 1)))) = H := by
      change Submodule.span ℝ (Set.range (H.subtype ∘ ⇑oH)) = H
      rw [Set.range_comp, Submodule.span_image H.subtype, ← oH.coe_toBasis,
        oH.toBasis.span_eq, Submodule.map_subtype_top]
    rw [← hspan]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      change inner ℝ (oH i : E (n + 1)) (o 0) = 0
      rw [← ho i]
      exact o.orthonormal.inner_eq_zero (Fin.succ_ne_zero i)
    | zero => simp
    | add y z hy hz ihy ihz => simp [inner_add_left, ihy, ihz]
    | smul r y hy ih => simp [inner_smul_left, ih]
  exact Submodule.inner_left_of_mem_orthogonal x.property horth

theorem layerSpacing : LayerSpacing := by
  classical
  intro e he L H v hdim hrat hv hvH
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  have hdim' : Module.finrank ℝ H = n := by simpa using hdim
  let M := latticeInSubspace L.carrier H
  have : DiscreteTopology M := latticeInSubspace_discrete L H
  have : IsZLattice ℝ M := latticeInSubspace_isZLattice L H hrat
  have : Module.Free ℤ M := ZLattice.module_free ℝ M
  let bZ : Basis (Fin n) ℤ M := Module.finBasisOfFinrankEq ℤ M
    (by rw [ZLattice.rank ℝ M, hdim'])
  let bH : Basis (Fin n) ℝ H := bZ.ofZLatticeBasis ℝ M
  let oH : OrthonormalBasis (Fin n) ℝ H :=
    (stdOrthonormalBasis ℝ H).reindex (finCongr hdim')
  obtain ⟨o, ho⟩ := exists_adapted_orthonormal H oH
  have hspan : Submodule.span ℝ (Set.range (fun i => (bH i : E (n + 1)))) = H := by
    change Submodule.span ℝ (Set.range (H.subtype ∘ ⇑bH)) = H
    rw [Set.range_comp, Submodule.span_image H.subtype, bH.span_eq,
      Submodule.map_subtype_top]
  have hli : LinearIndependent ℝ (Fin.cons v (fun i => (bH i : E (n + 1)))) :=
    (bH.linearIndependent.map' H.subtype (Submodule.ker_subtype H)).finCons
      (by change v ∉ Submodule.span ℝ (Set.range (fun i => (bH i : E (n + 1))))
          rwa [hspan])
  let b : Basis (Fin (n + 1)) ℝ (E (n + 1)) := Basis.mk hli
    (by rw [hli.span_eq_top_of_card_eq_finrank' (by simp [E])])
  have b_zero : b 0 = v := by simp [b]
  have b_succ (i : Fin n) : b i.succ = (bH i : E (n + 1)) := by simp [b]
  have hb : ∀ i, b i ∈ L.carrier := by
    intro i
    refine Fin.cases (motive := fun i => b i ∈ L.carrier) ?_ (fun j => ?_) i
    · rwa [b_zero]
    · rw [b_succ]
      have hH : bH j = (bZ j : H) := bZ.ofZLatticeBasis_apply ℝ M j
      rw [hH]
      exact (bZ j).property
  have hdet : o.toBasis.det b = inner ℝ (o 0) v * oH.toBasis.det bH := by
    rw [Basis.det_apply, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∀ j : Fin n, (o.toBasis.toMatrix b) 0 j.succ = 0 := by
      intro j
      change o.toBasis.repr (b j.succ) 0 = 0
      rw [o.coe_toBasis_repr_apply, o.repr_apply_apply, b_succ]
      exact adapted_inner_zero H oH o ho (bH j)
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    congr 1
    · change o.toBasis.repr (b 0) 0 = _
      rw [o.coe_toBasis_repr_apply, o.repr_apply_apply, b_zero]
    · rw [Basis.det_apply]
      congr 1
      ext i j
      change o.toBasis.repr (b j.succ) i.succ = oH.toBasis.repr (bH j) i
      rw [o.coe_toBasis_repr_apply, o.repr_apply_apply,
        oH.coe_toBasis_repr_apply, oH.repr_apply_apply, ho, b_succ]
      rfl
  have hMdet : ZLattice.covolume M = |oH.toBasis.det bH| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal M volume bZ oH.toBasis,
      orthonormal_fundamentalDomain_real, mul_one]
    have hco : ((↑) ∘ bZ : Fin n → H) = bH := by
      funext i
      exact (bZ.ofZLatticeBasis_apply ℝ M i).symm
    rw [hco]
  have hfull : L.det ≤ |inner ℝ (o 0) v| * ZLattice.covolume M := by
    have h := covolume_le_basis_volume L.carrier b hb
    rw [ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
      orthonormal_fundamentalDomain_real, mul_one, hdet, abs_mul, ← hMdet] at h
    exact h
  have hdiv : L.det / ZLattice.covolume M ≤ |inner ℝ (o 0) v| :=
    (div_le_iff₀ (ZLattice.covolume_pos M)).mpr hfull
  apply hdiv.trans
  apply (Metric.le_infDist (show (H : Set (E (n + 1))).Nonempty from ⟨0, H.zero_mem⟩)).mpr
  intro x hx
  have hz := adapted_inner_zero H oH o ho ⟨x, hx⟩
  have hnorm := abs_real_inner_le_norm (o 0) (v - x)
  simpa [inner_sub_right, hz, o.orthonormal.norm_eq_one, dist_eq_norm] using hnorm

end Praxis.Algebra.Point
