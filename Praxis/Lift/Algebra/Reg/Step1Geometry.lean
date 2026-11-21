import Praxis.Lift.Algebra.Reg.Step1
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Lift.Algebra.Reg.Promote1
import Praxis.Lift.Algebra.Reg.Promote2
import Praxis.Lift.Algebra.Reg.Regularize1
import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Lift.Algebra.Reg.Regularize2Closed
import Praxis.Lift.Algebra.Reg.Step2Actual
import Praxis.Lift.Algebra.Reg.Step2Geometry
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Prefix.Chain
import Praxis.Algebra.Prefix.Mono
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Trans.Pullback
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Trim.Tensor
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.NumericTrim

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Step1.Geometry

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Lift.Algebra.Reg.Step2.Geometry

open scoped BigOperators Matrix

theorem next_carrier_in_extended1 {n k r : ℕ} (S : PivotFirstStep 1 n k)
    (M : IntLat (Fin k) r) (hcontain : S.old.primitive.carrier ≤ M.carrier) :
    S.next.primitive.carrier ≤ (extendMatrix M.matrix).mulVecLin.range := by
  obtain ⟨D, hD⟩ := extended_basis_split M
  have hs := split_range_saturated (extendMatrix M.matrix) D hD
  have hr : S.next.matrix.mulVecLin.range ≤ (extendMatrix M.matrix).mulVecLin.range := by
    rintro _ ⟨a, rfl⟩
    apply (mem_extended_range M _).mpr
    apply hcontain
    rw [S.old.primitive_eq]
    apply Algebra.Lattice.le_saturation
    refine ⟨a, ?_⟩
    ext i
    have hi := congrFun (congrArg (fun B : Matrix (Fin k) (Fin 1) ℤ => B.mulVec a)
      (Algebra.Prefix.step_matrix_init S)) i
    exact hi.symm
  intro x hx
  rw [S.next.primitive_eq] at hx
  obtain ⟨a, ha, hax⟩ := hx
  exact hs a ha x (hr hax)

theorem image_old_pivot1 {m r : ℕ} (T : Algebra.Trans.TransitionInput m r 1)
    (hpull : T.pulledNormal = T.normal) (pivot : Fin 1 → Fin m)
    (hdet : (T.normal.submatrix (fun j => (pivot j).castSucc) id).det ≠ 0) :
    ∃ p : Fin 1 → Fin r, ((Algebra.Trans.oldBlock T.imageNormal).submatrix p id).det ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hdet
  have hz : ∀ l : Fin r, T.imageNormal l.castSucc 0 = 0 := by
    intro l
    have h := hcon (fun _ => l)
    rw [Matrix.det_fin_one] at h
    simpa [Algebra.Trans.oldBlock] using h
  rw [Matrix.det_fin_one]
  change T.normal (pivot 0).castSucc 0 = 0
  rw [← hpull, Algebra.Trans.pulledNormal_old_entry T (pivot 0) 0]
  simp [hz]

theorem descent_geometry_of_trim {n k r : ℕ} (P : VITParameters)
    (S : PivotFirstStep 1 n k) (M : IntLat (Fin k) r)
    (E : Finset (Grid (S.next.grids S.grids)))
    (hcontain : S.old.primitive.carrier ≤ M.carrier)
    (hretain : S.old.primitive.mZ (S.old.grids S.grids) - 2 * P.eps ≤
      M.mZ (S.old.grids S.grids))
    (hreg : Regular P.toVITData (S.old.grids S.grids) M)
    (hnormals : ordinaryNormals (S.next.grids S.grids) E = S.next.primitive.carrier)
    (htrim : S.next.primitive.mZ (S.next.grids S.grids) - P.eps ≤
      density (S.next.grids S.grids) E)
    (hellipsoid : (descentInput S M 0 E).TrimmedEvent P.toVITData)
    (hG : GridBudget P.toVITData (S.next.grids S.grids)) : DescentGeometry1 P S r := by
  obtain ⟨D, hD⟩ := extended_basis_split M
  obtain ⟨K, hK, hprim⟩ := basis_factor_of_split (extendMatrix M.matrix) D hD
    S.next.primitive (next_carrier_in_extended1 S M hcontain)
  let T := descentInput S M K E
  have hB : T.OldLattice := Algebra.Prefix.primitive_rows M
  have hpull : T.pulledNormal = T.normal := by
    rw [pulled_eq_extended]
    exact hK.symm
  obtain ⟨hOrdinary, hWhole, hImage⟩ := normal_premises T S.next.primitive rfl
    hnormals hB hpull
  let pivot : Fin 1 → Fin k := fun j => ⟨j.val, lt_of_lt_of_le j.isLt S.old.rank_le_prefix⟩
  have hpiv : (T.normal.submatrix (fun j => (pivot j).castSucc) id).det.natAbs =
      S.next.primitive.H := primitive_pivot_max S.next
  have hdet : (T.normal.submatrix (fun j => (pivot j).castSucc) id).det ≠ 0 := by
    apply Int.natAbs_ne_zero.mp
    rw [hpiv]
    exact ne_of_gt (Algebra.Prefix.height_pos S.next.primitive)
  refine ⟨M, K, E, hcontain, hretain, hreg, htrim, hB, ?_, hOrdinary, hWhole,
    ⟨hprim, hImage, image_old_pivot1 T hpull pivot hdet⟩, ⟨pivot, hpiv⟩,
    ⟨fun i => S.grids_pos (S.next.coord i), hG.2.1⟩⟩
  exact hellipsoid

theorem exists_current_trim1 {n k r : ℕ} (P : VITParameters)
    (S : PivotFirstStep 1 n k) (M : IntLat (Fin k) r) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hTrim : Algebra.Trim.TrimForIntLat)
    (hdomain : P.theta0 - 20 * P.eps ≤ S.next.primitive.mZ (S.next.grids S.grids)) :
    ∃ (t : Fin 1 → ℤ) (E : Finset (Grid (S.next.grids S.grids))),
      atom (S.next.grids S.grids) (imageZ (S.next.grids S.grids) S.next.primitive.matrix) t =
        S.next.primitive.mZ (S.next.grids S.grids) ∧
      E ⊆ ordinaryFibre (S.next.grids S.grids) S.next.primitive t ∧
      S.next.primitive.mZ (S.next.grids S.grids) - P.eps ≤ density (S.next.grids S.grids) E ∧
      (descentInput S M 0 E).TrimmedEvent P.toVITData := by
  classical
  let G := S.next.grids S.grids
  have hpos : ∀ i, 0 < G i := fun i => S.grids_pos (S.next.coord i)
  obtain ⟨t, ht, _hne⟩ := Algebra.Reg.largest_fibre G S.next.primitive hpos

  obtain ⟨U, _hout, hU⟩ := hTrim P.R P.eps P.trim.2 (Fin (k+1)) r G hpos
    (appendZero M.matrix) ⟨hr1, hr3⟩ (appendZero_independent M)
  let E := (ordinaryFibre G S.next.primitive t).filter (fun x => x ∈ U.ellipsoid P.R)
  have hset : (ordinaryFibre G S.next.primitive t : Set (Grid G)) ∩ U.ellipsoid P.R =
      (E : Set (Grid G)) := by ext x; simp [E]
  have hretain : S.next.primitive.mZ G - P.eps ≤ density G E := by
    have hh := hU (ordinaryFibre G S.next.primitive t : Set (Grid G))
    rw [hset] at hh
    change (Analysis.gridLaw G U.grid_pos).prob _ - _ ≤
      (Analysis.gridLaw G U.grid_pos).prob _ at hh
    rw [gridLaw_density, gridLaw_density, Algebra.Reg.ordinaryFibre_density, ht] at hh
    exact hh
  refine ⟨t, E, ht, filter_subset _ _, hretain, ?_, ?_⟩
  · apply Algebra.Reg.nonempty_of_density_pos G E
    have hs := (Algebra.Reg.Regularize1.rank1_slack P hdomain).1
    linarith [P.eps_pos, Algebra.Reg.threshold_pos P]
  · intro x hx
    have he := (mem_filter.mp hx).2
    have hc : U.center = (descentInput S M 0 E).center := by
      ext j
      rw [Analysis.GridImage.center]
      change (Analysis.gridLaw G U.grid_pos).mean _ j = _
      rw [Algebra.Trim.grid_mean]
      simp only [appendZero, Matrix.map_apply, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, Int.coe_castRingHom,
        Int.cast_zero, zero_mul, add_zero]
      change (∑ i : Fin k, (M.matrix i j : ℝ) * (((G i.castSucc : ℝ) - 1) / 2)) =
        ∑ i : Fin k, (M.matrix i j : ℝ) * ((G i.castSucc : ℝ) - 1) / 2
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hs : Analysis.gridCovariance G ((appendZero M.matrix).map (Int.castRingHom ℝ)) =
        (descentInput S M 0 E).sigma := by
      ext j l
      simp [Analysis.gridCovariance, appendZero, descentInput,
        Algebra.Trans.TransitionInput.sigma, Algebra.Trans.TransitionInput.oldGrids,
        Algebra.Trans.realMatrix, Fin.sum_univ_castSucc, G]
    have hi : Analysis.gridImage G ((appendZero M.matrix).map (Int.castRingHom ℝ)) x =
        (fun j => (imageZ (descentInput S M 0 E).oldGrids M.matrix
          ((descentInput S M 0 E).oldPoint x) j : ℝ)) := by
      ext j
      simp [Analysis.gridImage, appendZero, imageZ, descentInput,
        Algebra.Trans.TransitionInput.oldPoint, Fin.sum_univ_castSucc]
    change Analysis.mahalanobisSq _ U.center _ ≤ P.R^2 at he
    rw [hs, hc, hi] at he
    simpa only [descentInput] using he

structure CurrentEvent1 {m : ℕ} (P : VITParameters) (G : Fin m → ℕ)
    (L : IntLat (Fin m) 1) where
  target : Fin 1 → ℤ
  event : Finset (Grid G)
  maximal : atom G (imageZ G L.matrix) target = L.mZ G
  subset_fibre : event ⊆ ordinaryFibre G L target
  retained : L.mZ G - P.eps ≤ density G event

theorem exists_current_event1 {m : ℕ} (P : VITParameters) (G : Fin m → ℕ)
    (L : IntLat (Fin m) 1) (hpos : ∀ i, 0 < G i) : Nonempty (CurrentEvent1 P G L) := by
  obtain ⟨t, ht, _hne⟩ := Algebra.Reg.largest_fibre G L hpos
  refine ⟨⟨t, ordinaryFibre G L t, ht, le_rfl, ?_⟩⟩
  rw [Algebra.Reg.ordinaryFibre_density, ht]
  exact sub_le_self _ P.eps_pos.le

theorem exists_descent_lattice {k : ℕ} (P : VITParameters) (G : Fin k → ℕ)
    (L : IntLat (Fin k) 1) (hG : GridBudget P.toVITData G)
    (hd : P.theta0 - 20 * P.eps ≤ L.mZ G) (C : CurrentEvent1 P G L)
    (ho : ordinaryNormals G C.event ≠ L.carrier) :
    (∃ M : IntLat (Fin k) 2, L.carrier ≤ M.carrier ∧
      L.mZ G - 2 * P.eps ≤ M.mZ G ∧ Regular P.toVITData G M) ∨
    (∃ M : IntLat (Fin k) 3, L.carrier ≤ M.carrier ∧
      L.mZ G - 2 * P.eps ≤ M.mZ G ∧ Regular P.toVITData G M) := by
  have hs := (Algebra.Reg.Regularize1.rank1_slack P hd).1
  have hr := C.retained
  have hheavy : P.toVITData.mu ≤ density G C.event := by linarith [P.eps_pos]
  have hne := Algebra.Reg.nonempty_of_density_pos _ C.event
    ((Algebra.Reg.threshold_pos P).trans_le hheavy)
  have hL := Algebra.Reg.carrier_le_normals G L C.target C.event C.subset_fibre
  rcases (Algebra.Reg.Regularize1.rank1_normal_dichotomy P G L C.target C.event hG
    C.subset_fibre hheavy).resolve_left ho with h2 | h3
  · have hm2 : L.mZ G - P.eps ≤ (Algebra.Reg.Promote1.normalLattice C.event h2).mZ G :=
      hr.trans (Promote2.density_le_mass _ C.event hne le_rfl)
    have hdom : P.theta0 - 30 * P.eps ≤ (Algebra.Reg.Promote1.normalLattice C.event h2).mZ G := by
      linarith [P.eps_pos]
    rcases Algebra.Reg.Closed2.regularize2 P G (Algebra.Reg.Promote1.normalLattice C.event h2) hG hdom
      with hreg | ⟨M3, h23, hm3, _hH3, hreg3⟩
    · exact Or.inl ⟨_, hL, by linarith [P.eps_pos], hreg⟩
    · exact Or.inr ⟨M3, hL.trans h23, by linarith, hreg3⟩
  · have hm3 : density G C.event ≤ (Algebra.Reg.Promote1.normalLattice C.event h3).mZ G :=
      Promote2.density_le_mass _ C.event hne le_rfl
    obtain ⟨_hH, hreg⟩ := Algebra.Reg.Step2.Actual.rank3 P G
      (Algebra.Reg.Promote1.normalLattice C.event h3) hG (hheavy.trans hm3)
    exact Or.inr ⟨_, hL, by linarith [P.eps_pos], hreg⟩

theorem exists_next_event1 {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 1 n k)
    (hOld : GridBudget P.toVITData (S.old.grids S.grids))
    (hNew : GridBudget P.toVITData (S.next.grids S.grids))
    (hdOld : P.theta0 - 20 * P.eps ≤ S.old.primitive.mZ (S.old.grids S.grids))
    (hdNew : P.theta0 - 20 * P.eps ≤ S.next.primitive.mZ (S.next.grids S.grids))
    (C : CurrentEvent1 P (S.old.grids S.grids) S.old.primitive) :
    ∃ N : CurrentEvent1 P (S.next.grids S.grids) S.next.primitive,
      ordinaryNormals (S.next.grids S.grids) N.event = S.next.primitive.carrier →
      ordinaryNormals (S.old.grids S.grids) C.event ≠ S.old.primitive.carrier →
      DescentGeometry1 P S 2 ∨ DescentGeometry1 P S 3 := by
  classical
  by_cases ho : ordinaryNormals (S.old.grids S.grids) C.event = S.old.primitive.carrier
  · obtain ⟨N⟩ := exists_current_event1 P _ S.next.primitive
      (fun i => S.grids_pos (S.next.coord i))
    exact ⟨N, fun _ hn => (hn ho).elim⟩
  · rcases exists_descent_lattice P _ S.old.primitive hOld hdOld C ho with
        ⟨M, hc, hm, hreg⟩ | ⟨M, hc, hm, hreg⟩
    · obtain ⟨t, E, ht, hE, hret, hEll⟩ :=
        exists_current_trim1 P S M (by decide) (by decide) Algebra.Reg.Step2.Actual.trim hdNew
      exact ⟨⟨t, E, ht, hE, hret⟩, fun hn _ =>
        Or.inl (descent_geometry_of_trim P S M E hc hm hreg hn hret hEll hNew)⟩
    · obtain ⟨t, E, ht, hE, hret, hEll⟩ :=
        exists_current_trim1 P S M (by decide) le_rfl Algebra.Reg.Step2.Actual.trim hdNew
      exact ⟨⟨t, E, ht, hE, hret⟩, fun hn _ =>
        Or.inr (descent_geometry_of_trim P S M E hc hm hreg hn hret hEll hNew)⟩

end Algebra.Reg.Step1.Geometry

end Praxis.Lift
