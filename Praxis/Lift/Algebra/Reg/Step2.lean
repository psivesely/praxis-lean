import Praxis.Lift.Algebra.Reg.Pivot2
import Praxis.Algebra.Reg.Stretch2
import Praxis.Lift.Algebra.Reg.Transition2
import Praxis.Algebra.Prefix.Jump
import Praxis.Combinatorics.Chain
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Lift.Algebra.Reg.Return2
import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Algebra.Trans.Definitions
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Power.Definitions
import Praxis.Algebra.Prefix.Height
import Praxis.Algebra.Prefix.Mono
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Step2

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open scoped BigOperators Matrix

theorem mass_add_cyclic {Y A : Type*} [Fintype Y] [Nonempty Y]
    [AddCommGroup A] (H : AddSubgroup A) (f : Y → A) (a : A)
    (hf : ∀ y, QuotientAddGroup.mk' H (f y) = 0)
    (w v : ℕ) (_hw : 0 < w)
    (hv : v = addOrderOf (QuotientAddGroup.mk' H a)) (hvpos : 0 < v) :
    Algebra.FiniteProbability.atomMass (fun xy : Fin w × Y => f xy.2 + xy.1.val • a) ≤
      Algebra.FiniteProbability.atomMass f * (((w + v - 1) / v : ℕ) : ℝ) / (w : ℝ) := by
  classical
  let q := QuotientAddGroup.mk' H
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  let R : Finset (Fin w) := univ.filter (fun x => x.val • q a = q t)
  have hmod : ∀ x ∈ R, ∀ y ∈ R, (x : ℕ) ≡ y [MOD v] := by
    intro x hx y hy
    apply Nat.modEq_iff_dvd.mpr
    rw [hv]
    apply addOrderOf_dvd_iff_zsmul_eq_zero.mpr
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul,
      (mem_filter.mp hy).2, (mem_filter.mp hx).2, add_neg_cancel]
  have hcard := Combinatorics.card_le_ceil hvpos R hmod
  have hzero (x : Fin w) (hx : x ∉ R) :
      Algebra.FiniteProbability.pointProb (fun y => f y + x.val • a) t = 0 := by
    have hn (y : Y) : f y + x.val • a ≠ t := by
      intro he
      apply hx
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      have h := congrArg q he
      simpa only [q, map_add, map_nsmul, hf y, zero_add] using h
    simp [Algebra.FiniteProbability.pointProb_eq_sum, hn]
  have hslice (x : Fin w) :
      Algebra.FiniteProbability.pointProb (fun y => f y + x.val • a) t ≤ Algebra.FiniteProbability.atomMass f :=
    (Algebra.FiniteProbability.pointProb_le_mass _ _).trans
      (Algebra.Prefix.mass_le_of_fibres _ _ (fun _ _ h => add_right_cancel h))
  rw [Algebra.FiniteProbability.pointProb_prod, Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ∑ x : Fin w, Algebra.FiniteProbability.pointProb (fun y => f y + x.val • a) t =
        ∑ x ∈ R, Algebra.FiniteProbability.pointProb (fun y => f y + x.val • a) t := by
      symm
      apply sum_subset (subset_univ R)
      intro x _ hx
      exact hzero x hx
    _ ≤ ∑ _x ∈ R, Algebra.FiniteProbability.atomMass f := sum_le_sum (fun x _ => hslice x)
    _ = (R.card : ℝ) * Algebra.FiniteProbability.atomMass f := by simp
    _ ≤ (((w + v - 1) / v : ℕ) : ℝ) * Algebra.FiniteProbability.atomMass f :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Algebra.FiniteProbability.atomMass_nonneg f)
    _ = _ := mul_comm _ _

theorem last_width {d n k : ℕ} (S : PivotFirstStep d n k) :
    S.next.grids S.grids (Fin.last k) = S.grids S.newCoord := by
  unfold PivotFirstPrefix.grids PivotFirstPrefix.coord PivotFirstStep.newCoord
  rw [S.same_order]
  rfl

theorem prefix_ceiling_mass {n k : ℕ} (S : PivotFirstStep 2 n k) :
    S.next.primitive.mZ (S.next.grids S.grids) ≤
      S.old.primitive.mZ (S.old.grids S.grids) *
        (((S.grids S.newCoord + S.residueOrder - 1) / S.residueOrder : ℕ) : ℝ) /
          (S.grids S.newCoord : ℝ) := by
  rw [Algebra.Prefix.primitive_mass_eq (S.next.grids S.grids)
      (fun i => S.grids_pos (S.next.coord i)) S.next.matrix
      S.next.primitive S.next.primitive_eq,
    Algebra.Prefix.primitive_mass_eq (S.old.grids S.grids)
      (fun i => S.grids_pos (S.old.coord i)) S.old.matrix
      S.old.primitive S.old.primitive_eq]
  let G := S.next.grids S.grids
  let G0 := fun i : Fin k => G i.castSucc
  let B := S.next.matrix
  let f := imageZ G0 (B.submatrix Fin.castSucc id)
  let a := B (Fin.last k)
  let e := Fin.snocEquiv (fun i => Fin (G i))
  let : Nonempty (Grid G0) := ⟨fun i => ⟨0, S.grids_pos (S.next.coord i.castSucc)⟩⟩
  have he : imageZ G B ∘ e = fun xy => f xy.2 + xy.1.val • a := by
    funext xy j
    change (∑ i, B i j * ((e xy i : ℕ) : ℤ)) = _
    rw [Fin.sum_univ_castSucc]
    simp [e, Fin.snocEquiv, f, a, imageZ, Matrix.submatrix,
      nsmul_eq_mul, mul_comm]
  have hf (y : Grid G0) : QuotientAddGroup.mk' S.old.rows (f y) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    have him : f y = ∑ i : Fin k, (y i : ℕ) • S.next.matrix i.castSucc := by
      ext j
      simp [f, B, imageZ, Matrix.submatrix, Finset.sum_apply, nsmul_eq_mul, mul_comm]
    rw [him]
    exact S.old.rows.sum_mem (fun i _ => S.old.rows.nsmul_mem (Algebra.Prefix.old_row_mem S i) _)
  have hv : S.residueOrder = addOrderOf (QuotientAddGroup.mk' S.old.rows a) := by
    dsimp [a, B]
    rw [Algebra.Prefix.last_row_eq]
    exact S.quotient_order
  have hb := mass_add_cyclic S.old.rows f a hf (G (Fin.last k)) S.residueOrder
    (S.grids_pos (S.next.coord (Fin.last k))) hv
    (lt_of_lt_of_le Nat.zero_lt_one (Pivot2.step_identities S).1)
  rw [← he, Algebra.Prefix.mass_precomp_equiv] at hb
  have hmass : Algebra.FiniteProbability.atomMass f =
      mass (S.old.grids S.grids) (imageZ (S.old.grids S.grids) S.old.matrix) := by
    change mass G0 (imageZ G0 (B.submatrix Fin.castSucc id)) = _
    dsimp only [B]
    rw [Algebra.Prefix.step_matrix_init]
    exact congrArg (fun g : Fin k → ℕ => mass g (imageZ g S.old.matrix))
      (Algebra.Prefix.step_grids_init S)
  rw [hmass] at hb
  simpa only [mass, G, B, last_width] using hb

theorem primitive_pivot_ne_zero {d n k : ℕ} (Q : PivotFirstPrefix d n k) :
    (Q.primitive.matrix.submatrix
      (fun j : Fin d => (⟨j.val, lt_of_lt_of_le j.isLt Q.rank_le_prefix⟩ : Fin k))
      id).det ≠ 0 := by
  let pivot : Fin d → Fin k := fun j => ⟨j.val, lt_of_lt_of_le j.isLt Q.rank_le_prefix⟩
  have hB : Q.matrix.mulVecLin.range ≤ Q.primitive.carrier := by
    rw [Q.primitive_eq]
    exact Algebra.Lattice.le_saturation _
  obtain ⟨A, hA⟩ := Algebra.Prefix.exists_basis_factor Q.primitive Q.matrix hB
  have hp : (Q.matrix.submatrix pivot id).det.natAbs = Q.original.H := Q.maximal_pivot
  rw [hA, Algebra.Prefix.minor_mul] at hp
  have hpos := Q.pivot_nonzero
  apply Int.natAbs_ne_zero.mp
  intro hz
  rw [hz, zero_mul] at hp
  omega

theorem step_isOrdinaryFibre {n k : ℕ} (S : PivotFirstStep 2 n k)
    (t : Fin 2 → ℤ) (F : Finset (Grid (S.next.grids S.grids)))
    (hF : F ⊆ ordinaryFibre (S.next.grids S.grids) S.next.primitive t) :
    S.IsOrdinaryFibre F := by
  classical
  intro r hr s hs
  apply (Algebra.Prefix.primitive_image_eq_iff _ _ _ S.next.primitive_eq r s).mp
  have h1 : imageZ (S.next.grids S.grids) S.next.primitive.matrix r = t := by
    simpa only [ordinaryFibre, mem_filter, mem_univ, true_and] using hF hr
  have h2 : imageZ (S.next.grids S.grids) S.next.primitive.matrix s = t := by
    simpa only [ordinaryFibre, mem_filter, mem_univ, true_and] using hF hs
  exact h1.trans h2.symm

theorem continuing_order_lt_width {n k : ℕ} (S : PivotFirstStep 2 n k)
    (t : Fin 2 → ℤ) (F : Finset (Grid (S.next.grids S.grids)))
    (hne : F.Nonempty)
    (hF : F ⊆ ordinaryFibre (S.next.grids S.grids) S.next.primitive t)
    (hnormals : ordinaryNormals (S.next.grids S.grids) F = S.next.primitive.carrier) :
    S.residueOrder < S.grids S.newCoord := by
  have h := Algebra.Reg.order_lt_width_of_normals
    (S.next.grids S.grids) S.next.primitive F hnormals
    (fun j : Fin 2 => ⟨j.val, lt_of_lt_of_le j.isLt S.next.rank_le_prefix⟩)
    (primitive_pivot_ne_zero S.next) (Fin.last k)
    (by
      intro j he
      have h := congrArg Fin.val he
      have hj := j.isLt
      have hk := S.old.rank_le_prefix
      simp only [Fin.val_last] at h
      omega)
    S.residueOrder (by
      intro hj
      rw [last_width] at hj
      obtain ⟨a, ha⟩ := Algebra.Prefix.jump_fixes_coordinate S F hne
        (step_isOrdinaryFibre S t F hF) hj
      exact ⟨(a : ℤ), fun r hr => congrArg
        (fun z : Fin (S.next.grids S.grids (Fin.last k)) => ((z : ℕ) : ℤ)) (ha r hr)⟩)
  simpa only [last_width] using h

theorem continuation {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 2 n k)
    (hStretch : Algebra.Power.StretchEstimate)
    (hwidth : 2 ^ P.L0 ≤ S.grids S.newCoord)
    (hnojump : S.residueOrder < S.grids S.newCoord) :
    (S.next.primitive.mZ (S.next.grids S.grids) * (S.next.primitive.H : ℝ)) ^
        (P.L0 - 1) * S.next.primitive.mZ (S.next.grids S.grids) ≤
      (S.old.primitive.mZ (S.old.grids S.grids) * (S.old.primitive.H : ℝ)) ^
        (P.L0 - 1) * S.old.primitive.mZ (S.old.grids S.grids) := by
  exact Algebra.Reg.continuation_moment_step P (Pivot2.pairGrids S) (Pivot2.pairLattices S)
    (S.grids S.newCoord) S.residueOrder
    (Algebra.Reg.rank2_stretch_of_estimate hStretch _ _ _ _ _)
    (Pivot2.pair_positive S) hwidth (Pivot2.step_identities S).1 hnojump
    (Pivot2.pair_hheight S) (prefix_ceiling_mass S) (Pivot2.pair_hmono S)

noncomputable def returnInput {n k : ℕ} (S : PivotFirstStep 2 n k)
    (L3 : IntLat (Fin k) 3) (K : Matrix (Fin 4) (Fin 2) ℤ)
    (E : Finset (Grid (S.next.grids S.grids))) : Algebra.Trans.TransitionInput k 3 2 :=
  ⟨S.next.grids S.grids, L3.matrix, S.next.primitive.matrix, K, E⟩

def ReturnGeometry {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 2 n k) : Prop :=
  ∃ (L3 : IntLat (Fin k) 3) (K : Matrix (Fin 4) (Fin 2) ℤ)
      (E : Finset (Grid (S.next.grids S.grids))),
    S.old.primitive.carrier ≤ L3.carrier ∧
    S.old.primitive.mZ (S.old.grids S.grids) - P.eps ≤ L3.mZ (S.old.grids S.grids) ∧
    S.next.primitive.mZ (S.next.grids S.grids) - P.eps ≤ density (S.next.grids S.grids) E ∧
    Algebra.Trans.TransitionData 3 2 P.toVITData (returnInput S L3 K E)

theorem return_reset {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 2 n k)
    (hT : Algebra.Trans.Transition32 P) (hPlanar : Algebra.Point.PlanarCount)
    (hSection : Algebra.Point.SectionCount3) (hTrim : Algebra.Trim.TrimForIntLat)
    (hrank3 : ∀ L3 : IntLat (Fin k) 3, Rank3Height P (S.old.grids S.grids) L3)
    (hG : GridBudget P.toVITData (S.old.grids S.grids))
    (hdomain : P.theta0 - 30 * P.eps ≤ S.next.primitive.mZ (S.next.grids S.grids))
    (hgeometry : ReturnGeometry P S) :
    S.next.primitive.mZ (S.next.grids S.grids) * (S.next.primitive.H : ℝ) ≤
        P.A * P.D * P.C3 / (P.g : ℝ)^2 ∧
      S.next.primitive.mZ (S.next.grids S.grids) ≤ (P.g : ℝ)^(-(3 : ℤ)) + P.eps := by
  obtain ⟨L3, K, E, _hcontain, hretain, htrim, hData⟩ := hgeometry
  have hraw := Transition2.transition32_raw P hT hPlanar hSection hTrim
    (returnInput S L3 K E) hData L3 S.next.primitive rfl rfl
  have hgrid : (returnInput S L3 K E).oldGrids = S.old.grids S.grids :=
    Algebra.Prefix.step_grids_init S
  have hmass : L3.mZ (returnInput S L3 K E).oldGrids = L3.mZ (S.old.grids S.grids) :=
    congrArg (fun g => L3.mZ g) hgrid
  rw [hmass] at hraw
  exact Algebra.Reg.return_step_reset P (S.old.grids S.grids) L3
    (S.next.grids S.grids) S.next.primitive (density (S.next.grids S.grids) E)
    (S.old.primitive.mZ (S.old.grids S.grids)) (hrank3 L3) hG
    (Algebra.Reg.Return2.rank2_return P _ L3 _ S.next.primitive _)
    hretain (Pivot2.step_identities S).2.2 hdomain htrim hraw

namespace Presentation

variable {n : ℕ} {L : IntLat (Fin n) 2} (R : Pivot2.Presentation L)

theorem domain (P : VITParameters) (G : Fin n → ℕ) (hG : ∀ i, 0 < G i)
    (hm : P.theta0 - 30 * P.eps ≤ L.mZ G) :
    ∀ j, P.theta0 - 30 * P.eps ≤ (R.lattices j).mZ (R.grids G j) := by
  have ha : Antitone (fun j => (R.lattices j).mZ (R.grids G j)) :=
    Fin.antitone_iff_succ_le.mpr (R.hmono G hG)
  intro j
  exact hm.trans ((R.last_mass G hG).symm.le.trans (ha (Fin.le_last j)))

theorem hstep (P : VITParameters) (G : Fin n → ℕ)
    (hG : GridBudget P.toVITData G)
    (hpos : ∀ i, 0 < G i) (hm : P.theta0 - 30 * P.eps ≤ L.mZ G)
    (F : (j : Fin (n - 2 + 1)) → Finset (Grid (R.grids G j)))
    (t : Fin (n - 2 + 1) → Fin 2 → ℤ)
    (hF : ∀ j, F j ⊆ ordinaryFibre (R.grids G j) (R.lattices j) (t j))
    (hretain : ∀ j, (R.lattices j).mZ (R.grids G j) - P.eps ≤ density (R.grids G j) (F j))
    (hStretch : Algebra.Power.StretchEstimate)
    (hT : Algebra.Trans.Transition32 P) (hPlanar : Algebra.Point.PlanarCount)
    (hSection : Algebra.Point.SectionCount3) (hTrim : Algebra.Trim.TrimForIntLat)
    (hrank3 : ∀ (j : Fin (n - 2 + 1)) (L3 : IntLat (Fin (j.val + 2)) 3),
      Rank3Height P (R.grids G j) L3)
    (hgeometry : ∀ j : Fin (n - 2),
      ordinaryNormals (R.grids G j.succ) (F j.succ) = (R.lattices j.succ).carrier →
      ordinaryNormals (R.grids G j.castSucc) (F j.castSucc) ≠ (R.lattices j.castSucc).carrier →
      ReturnGeometry P (R.step G hpos j)) :
    ∀ j : Fin (n - 2),
      ordinaryNormals (R.grids G j.succ) (F j.succ) = (R.lattices j.succ).carrier →
      (ordinaryNormals (R.grids G j.castSucc) (F j.castSucc) = (R.lattices j.castSucc).carrier ∧
        (((R.lattices j.succ).mZ (R.grids G j.succ) * ((R.lattices j.succ).H : ℝ)) ^
          (P.L0 - 1)) * (R.lattices j.succ).mZ (R.grids G j.succ) ≤
        (((R.lattices j.castSucc).mZ (R.grids G j.castSucc) *
          ((R.lattices j.castSucc).H : ℝ)) ^ (P.L0 - 1)) *
            (R.lattices j.castSucc).mZ (R.grids G j.castSucc)) ∨
      ((R.lattices j.succ).mZ (R.grids G j.succ) * ((R.lattices j.succ).H : ℝ) ≤
          P.A * P.D * P.C3 / (P.g : ℝ)^2 ∧
        (R.lattices j.succ).mZ (R.grids G j.succ) ≤ (P.g : ℝ)^(-(3 : ℤ)) + P.eps) := by
  intro j hn
  by_cases ho : ordinaryNormals (R.grids G j.castSucc) (F j.castSucc) =
      (R.lattices j.castSucc).carrier
  · left
    refine ⟨ho, ?_⟩
    have hd := domain R P G hpos hm j.succ
    have hne : (F j.succ).Nonempty := by
      apply Algebra.Reg.nonempty_of_density_pos (R.grids G j.succ) (F j.succ)
      have hs := (Algebra.Reg.rank2_slack P hd).1
      have hr := hretain j.succ
      linarith [P.eps_pos, Algebra.Reg.threshold_pos P]
    exact continuation P (R.step G hpos j) hStretch
      (P.g_lower.trans (hG.1 _))
      (continuing_order_lt_width (R.step G hpos j) (t j.succ) (F j.succ)
        hne (hF j.succ) hn)
  · right
    exact return_reset P (R.step G hpos j) hT hPlanar hSection hTrim
      (hrank3 j.castSucc) (R.budget P.toVITData G hG j.castSucc)
      (domain R P G hpos hm j.succ) (hgeometry j hn ho)

end Presentation

end Algebra.Reg.Step2

end Praxis.Lift
