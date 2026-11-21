import Praxis.Lift.Algebra.Reg.Step2
import Praxis.Lift.Algebra.Reg.Regularize1
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Reg.Rank1Model
import Praxis.Lift.Record
import Praxis.Lift.Algebra.Reg.Pivot2
import Praxis.Lift.Algebra.Reg.Regularize2
import Praxis.Lift.Algebra.Reg.Return1
import Praxis.Lift.Algebra.Reg.Step2Actual
import Praxis.Lift.Algebra.Trans.ChartTransitions
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.Prefix.Height
import Praxis.Algebra.Prefix.Jump
import Praxis.Algebra.Prefix.Mono
import Praxis.Algebra.Prefix.Order
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Step1

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions Praxis.Lift.Algebra.Reg.Rank1Model

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Algebra.Reg.Rank1Model hiding Rank1Promotion Rank1Return21 Rank1Return31 Rank1NestedCall

open scoped BigOperators Matrix

theorem step_identities1 {n k : ℕ} (S : PivotFirstStep 1 n k) :
    1 ≤ S.residueOrder ∧
    S.next.primitive.H = S.residueOrder * S.old.primitive.H ∧ PrefixMassMono S := by
  have hO := Algebra.Prefix.Order.prefix_order S
  have h1 := Algebra.Prefix.prefix_height S.old
  have h2 := Algebra.Prefix.prefix_height S.next
  change S.old.divisor = S.residueOrder * S.next.divisor at hO
  change S.old.divisor * S.old.primitive.H = S.old.original.H at h1
  change S.next.divisor * S.next.primitive.H = S.next.original.H at h2
  rw [S.same_original] at h2
  have hp := S.old.pivot_nonzero
  have hd : 0 < S.next.divisor := by nlinarith
  have hod : 0 < S.old.divisor := by nlinarith
  have ho : 1 ≤ S.residueOrder := by
    by_contra h
    have hz : S.residueOrder = 0 := by omega
    rw [hz, zero_mul] at hO
    omega
  refine ⟨ho, ?_, Algebra.Prefix.prefix_mass_mono S⟩
  apply Nat.eq_of_mul_eq_mul_left hd
  calc S.next.divisor * S.next.primitive.H = S.old.original.H := h2
    _ = S.old.divisor * S.old.primitive.H := h1.symm
    _ = S.next.divisor * (S.residueOrder * S.old.primitive.H) := by rw [hO]; ring

noncomputable def pairLattices1 {n k : ℕ} (S : PivotFirstStep 1 n k) :
    (j : Fin 2) → IntLat (Pivot2.pairTypes k j) 1 :=
  Fin.cases S.old.primitive (fun _ => S.next.primitive)

noncomputable def pairGrids1 {n k : ℕ} (S : PivotFirstStep 1 n k) :
    (j : Fin 2) → Pivot2.pairTypes k j → ℕ :=
  Fin.cases (S.old.grids S.grids) (fun _ => S.next.grids S.grids)

theorem pair_positive1 {n k : ℕ} (S : PivotFirstStep 1 n k) :
    ∀ j i, 0 < pairGrids1 S j i := by
  intro j
  refine Fin.cases ?_ (fun _ => ?_) j
  · exact fun i => S.grids_pos (S.old.coord i)
  · exact fun i => S.grids_pos (S.next.coord i)

theorem prefix_ceiling_mass1 {n k : ℕ} (S : PivotFirstStep 1 n k) :
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
  have hb := Step2.mass_add_cyclic S.old.rows f a hf (G (Fin.last k)) S.residueOrder
    (S.grids_pos (S.next.coord (Fin.last k))) hv
    (lt_of_lt_of_le Nat.zero_lt_one (step_identities1 S).1)
  rw [← he, Algebra.Prefix.mass_precomp_equiv] at hb
  have hmass : Algebra.FiniteProbability.atomMass f =
      mass (S.old.grids S.grids) (imageZ (S.old.grids S.grids) S.old.matrix) := by
    change mass G0 (imageZ G0 (B.submatrix Fin.castSucc id)) = _
    dsimp only [B]
    rw [Algebra.Prefix.step_matrix_init]
    exact congrArg (fun g : Fin k → ℕ => mass g (imageZ g S.old.matrix))
      (Algebra.Prefix.step_grids_init S)
  rw [hmass] at hb
  simpa only [mass, G, B, Step2.last_width] using hb

theorem new_unit_not_mem1 {n k : ℕ} (S : PivotFirstStep 1 n k) :
    Pi.single (Fin.last k) 1 ∉ S.next.primitive.carrier := by
  apply Algebra.Reg.unit_not_mem_of_pivot S.next.primitive
    (fun j : Fin 1 => ⟨j.val, lt_of_lt_of_le j.isLt S.next.rank_le_prefix⟩)
    (Step2.primitive_pivot_ne_zero S.next) (Fin.last k)
  intro j he
  have h := congrArg Fin.val he
  have hj := j.isLt
  have hk := S.old.rank_le_prefix
  simp only [Fin.val_last] at h
  omega

theorem step_isOrdinaryFibre1 {n k : ℕ} (S : PivotFirstStep 1 n k)
    (t : Fin 1 → ℤ) (F : Finset (Grid (S.next.grids S.grids)))
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

theorem jump_promotion_trigger1 {n k : ℕ} (S : PivotFirstStep 1 n k)
    (t : Fin 1 → ℤ) (F : Finset (Grid (S.next.grids S.grids)))
    (hne : F.Nonempty)
    (hF : F ⊆ ordinaryFibre (S.next.grids S.grids) S.next.primitive t)
    (hjump : S.grids S.newCoord ≤ S.residueOrder) :
    ∃ (i : Fin (k+1)) (a : ℤ),
      (∀ r ∈ F, ((r i : ℕ) : ℤ) = a) ∧ Pi.single i 1 ∉ S.next.primitive.carrier := by
  obtain ⟨a, ha⟩ := Algebra.Prefix.jump_fixes_coordinate S F hne
    (step_isOrdinaryFibre1 S t F hF) hjump
  exact ⟨Fin.last k, (a : ℤ), fun r hr => congrArg
    (fun z : Fin (S.next.grids S.grids (Fin.last k)) => ((z : ℕ) : ℤ)) (ha r hr),
    new_unit_not_mem1 S⟩

theorem continuing_order_lt_width1 {n k : ℕ} (S : PivotFirstStep 1 n k)
    (t : Fin 1 → ℤ) (F : Finset (Grid (S.next.grids S.grids)))
    (hne : F.Nonempty)
    (hF : F ⊆ ordinaryFibre (S.next.grids S.grids) S.next.primitive t)
    (hnormals : ordinaryNormals (S.next.grids S.grids) F = S.next.primitive.carrier) :
    S.residueOrder < S.grids S.newCoord := by
  by_contra hn
  obtain ⟨i, a, ha, hind⟩ := jump_promotion_trigger1 S t F hne hF (by omega)
  have hu := Algebra.Reg.unit_normal_of_fixed (S.next.grids S.grids) F i a ha
  rw [hnormals] at hu
  exact hind hu

theorem continuation_moment_step1 (P : VITParameters) {η : Fin 2 → Type*}
    [∀ k, Fintype (η k)] [∀ k, DecidableEq (η k)]
    (G : (k : Fin 2) → η k → ℕ) (L : (k : Fin 2) → IntLat (η k) 1)
    (width order : ℕ)
    (hstretch : Rank1Stretch P.L0 G L (fun _ : Fin 1 => width) (fun _ => order))
    (hpos : ∀ k i, 0 < G k i) (hwidth : 2 ^ P.L0 ≤ width)
    (horder : 1 ≤ order) (hnojump : order < width)
    (hheight : (L 1).H = order * (L 0).H)
    (hmass : (L 1).mZ (G 1) ≤ (L 0).mZ (G 0) *
      (((width + order - 1) / order : ℕ) : ℝ) / (width : ℝ))
    (hmono : (L 1).mZ (G 1) ≤ (L 0).mZ (G 0)) :
    (((L 1).mZ (G 1) * ((L 1).H : ℝ)) ^ (P.L0 - 1)) * (L 1).mZ (G 1) ≤
      (((L 0).mZ (G 0) * ((L 0).H : ℝ)) ^ (P.L0 - 1)) * (L 0).mZ (G 0) := by
  by_cases hv : order = 1
  · have hh : (L 1).H = (L 0).H := by simpa only [hv, one_mul] using hheight
    rw [hh]
    exact Algebra.Reg.moment_mono (Algebra.Reg.mass_nonneg _ _) (Nat.cast_nonneg _) hmono
  · have hv2 : 2 ≤ order := by omega
    apply hstretch P.L0_lower hpos (fun _ => hwidth) (fun _ => ⟨hv2, hnojump⟩)
    · intro k
      fin_cases k
      exact hheight
    · intro k
      fin_cases k
      exact hmass

theorem continuation1 {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 1 n k)
    (hwidth : 2 ^ P.L0 ≤ S.grids S.newCoord)
    (hnojump : S.residueOrder < S.grids S.newCoord) :
    (S.next.primitive.mZ (S.next.grids S.grids) * (S.next.primitive.H : ℝ)) ^
        (P.L0 - 1) * S.next.primitive.mZ (S.next.grids S.grids) ≤
      (S.old.primitive.mZ (S.old.grids S.grids) * (S.old.primitive.H : ℝ)) ^
        (P.L0 - 1) * S.old.primitive.mZ (S.old.grids S.grids) :=
  continuation_moment_step1 P (pairGrids1 S) (pairLattices1 S)
    (S.grids S.newCoord) S.residueOrder
    (Algebra.Reg.Regularize1.rank1_stretch_closed _ _ _ _ _)
    (pair_positive1 S) hwidth (step_identities1 S).1 hnojump
    (step_identities1 S).2.1 (prefix_ceiling_mass1 S) (step_identities1 S).2.2

noncomputable def descentInput {n k r : ℕ} (S : PivotFirstStep 1 n k)
    (M : IntLat (Fin k) r) (K : Matrix (Fin (r+1)) (Fin 1) ℤ)
    (E : Finset (Grid (S.next.grids S.grids))) : Algebra.Trans.TransitionInput k r 1 :=
  ⟨S.next.grids S.grids, M.matrix, S.next.primitive.matrix, K, E⟩

def DescentGeometry1 {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 1 n k)
    (r : ℕ) : Prop :=
  ∃ (M : IntLat (Fin k) r) (K : Matrix (Fin (r+1)) (Fin 1) ℤ)
      (E : Finset (Grid (S.next.grids S.grids))),
    S.old.primitive.carrier ≤ M.carrier ∧
    S.old.primitive.mZ (S.old.grids S.grids) - 2 * P.eps ≤ M.mZ (S.old.grids S.grids) ∧
    Regular P.toVITData (S.old.grids S.grids) M ∧
    S.next.primitive.mZ (S.next.grids S.grids) - P.eps ≤ density (S.next.grids S.grids) E ∧
    Algebra.Trans.TransitionData r 1 P.toVITData (descentInput S M K E)

theorem descentInput_oldGrids {n k r : ℕ} (S : PivotFirstStep 1 n k)
    (M : IntLat (Fin k) r) (K : Matrix (Fin (r+1)) (Fin 1) ℤ)
    (E : Finset (Grid (S.next.grids S.grids))) :
    (descentInput S M K E).oldGrids = S.old.grids S.grids :=
  Algebra.Prefix.step_grids_init S

theorem descent_reset1 {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 1 n k)
    (hG : GridBudget P.toVITData (S.old.grids S.grids))
    (hdomain : P.theta0 - 20 * P.eps ≤ S.next.primitive.mZ (S.next.grids S.grids))
    (hgeometry : DescentGeometry1 P S 2 ∨ DescentGeometry1 P S 3) :
    S.next.primitive.mZ (S.next.grids S.grids) * (S.next.primitive.H : ℝ) ≤
        P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) ∧
      S.next.primitive.mZ (S.next.grids S.grids) ≤ (P.g : ℝ) ^ (-(2 : ℤ)) + 2 * P.eps := by
  have hm : P.toVITData.mu ≤ S.next.primitive.mZ (S.next.grids S.grids) := by
    have h := (Algebra.Reg.Regularize1.rank1_slack P hdomain).1
    linarith [P.eps_pos]
  have hmono : S.next.primitive.mZ (S.next.grids S.grids) ≤
      S.old.primitive.mZ (S.old.grids S.grids) := (step_identities1 S).2.2
  rcases hgeometry with ⟨M, K, E, _hc, hret, hreg, htrim, hData⟩ |
      ⟨M, K, E, _hc, hret, hreg, htrim, hData⟩
  · have hreg' : Regular P.toVITData (descentInput S M K E).oldGrids M := by
      rw [descentInput_oldGrids]; exact hreg
    exact ⟨Algebra.Reg.Return1.le_common_of_return21 P
        (Algebra.Reg.Return1.rank1_return21_of_transition P
          (Algebra.Trans.ChartTransitions.transition21_compat P) Algebra.Reg.Step2.Actual.planar
          Algebra.Reg.Step2.Actual.section3 Algebra.Reg.Step2.Actual.trim
          (descentInput S M K E) hData M S.next.primitive rfl rfl hm htrim hreg'),
      Algebra.Reg.Regularize1.descent_mass_cap P le_rfl _ M hG hret hmono⟩
  · have hreg' : Regular P.toVITData (descentInput S M K E).oldGrids M := by
      rw [descentInput_oldGrids]; exact hreg
    exact ⟨Algebra.Reg.Return1.le_common_of_return31 P
        (Algebra.Reg.Return1.rank1_return31_of_transition P
          (Algebra.Trans.ChartTransitions.transition31_compat P) Algebra.Reg.Step2.Actual.planar
          Algebra.Reg.Step2.Actual.section3 Algebra.Reg.Step2.Actual.trim
          (descentInput S M K E) hData M S.next.primitive rfl rfl hm htrim hreg'),
      Algebra.Reg.Regularize1.descent_mass_cap P (by decide) _ M hG hret hmono⟩

theorem step_recurrence1 {n k : ℕ} (P : VITParameters) (S : PivotFirstStep 1 n k)
    (hGold : GridBudget P.toVITData (S.old.grids S.grids))
    (hwidth : 2 ^ P.L0 ≤ S.grids S.newCoord)
    (hdomain : P.theta0 - 20 * P.eps ≤ S.next.primitive.mZ (S.next.grids S.grids))
    (F0 : Finset (Grid (S.old.grids S.grids))) (F1 : Finset (Grid (S.next.grids S.grids)))
    (t1 : Fin 1 → ℤ)
    (hF1 : F1 ⊆ ordinaryFibre (S.next.grids S.grids) S.next.primitive t1)
    (hret1 : S.next.primitive.mZ (S.next.grids S.grids) - P.eps ≤
      density (S.next.grids S.grids) F1)
    (hgeometry : ordinaryNormals (S.old.grids S.grids) F0 ≠ S.old.primitive.carrier →
      DescentGeometry1 P S 2 ∨ DescentGeometry1 P S 3) :
    ordinaryNormals (S.next.grids S.grids) F1 = S.next.primitive.carrier →
      (ordinaryNormals (S.old.grids S.grids) F0 = S.old.primitive.carrier ∧
        (S.next.primitive.mZ (S.next.grids S.grids) * (S.next.primitive.H : ℝ)) ^
            (P.L0 - 1) * S.next.primitive.mZ (S.next.grids S.grids) ≤
          (S.old.primitive.mZ (S.old.grids S.grids) * (S.old.primitive.H : ℝ)) ^
            (P.L0 - 1) * S.old.primitive.mZ (S.old.grids S.grids)) ∨
      (S.next.primitive.mZ (S.next.grids S.grids) * (S.next.primitive.H : ℝ) ≤
          P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) ∧
        S.next.primitive.mZ (S.next.grids S.grids) ≤ (P.g : ℝ) ^ (-(2 : ℤ)) + 2 * P.eps) := by
  intro hn
  by_cases ho : ordinaryNormals (S.old.grids S.grids) F0 = S.old.primitive.carrier
  · left
    refine ⟨ho, ?_⟩
    have hne : F1.Nonempty := by
      apply Algebra.Reg.nonempty_of_density_pos (S.next.grids S.grids) F1
      have hs := (Algebra.Reg.Regularize1.rank1_slack P hdomain).1
      linarith [P.eps_pos, Algebra.Reg.threshold_pos P]
    exact continuation1 P S hwidth (continuing_order_lt_width1 S t1 F1 hne hF1 hn)
  · right
    exact descent_reset1 P S hGold hdomain (hgeometry ho)

end Algebra.Reg.Step1

end Praxis.Lift
