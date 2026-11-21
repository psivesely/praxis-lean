import Praxis.Lift.Algebra.Reg.Rank1Model
import Praxis.Lift.Algebra.Reg.Return2
import Praxis.Lift.Algebra.Trans.Definitions
import Praxis.Lift.Record
import Praxis.Lift.Trim
import Praxis.Algebra.Point.Definitions
import Praxis.Algebra.Reg.Rank1Model
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Trans.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Return1

open Praxis.Algebra Praxis.Algebra.Reg

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Lift.Algebra.Reg.Rank1Model

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

open Praxis.Algebra.Reg.Rank1Model hiding Rank1Promotion Rank1Return21 Rank1Return31 Rank1NestedCall

theorem g_pos (P : VITParameters) : (0 : ℝ) < (P.g : ℝ) := by
  have hgNat : 0 < P.g := lt_of_lt_of_le (Nat.two_pow_pos P.L0) P.g_lower
  exact_mod_cast hgNat

theorem rank1_return21 (P : VITParameters) {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G2 : ι → ℕ) (L2 : IntLat ι 2)
    (G1 : κ → ℕ) (L1 : IntLat κ 1) (trimmedDensity : ℝ) :
    Rank1Return21 P G2 L2 G1 L1 trimmedDensity := by
  intro hm htrim hregular htransition
  have hg : (0 : ℝ) < P.g := g_pos P
  have hrestore := Algebra.Reg.Return2.restore_absolute_trim P hm htrim
  have hreg : L2.mZ G2 * (L2.H : ℝ) ≤ P.C2 / (P.g : ℝ)^2 := by
    simpa [Regular, VITData.C] using hregular
  calc
    L1.mZ G1 * (L1.H : ℝ) ≤ (P.A * trimmedDensity) * (L1.H : ℝ) :=
      mul_le_mul_of_nonneg_right hrestore (Nat.cast_nonneg _)
    _ = P.A * (trimmedDensity * (L1.H : ℝ)) := by ring
    _ ≤ P.A * (P.D * (P.g : ℝ) * (L2.H : ℝ) * L2.mZ G2) :=
      mul_le_mul_of_nonneg_left htransition P.A_pos.le
    _ = (P.A * P.D * (P.g : ℝ)) * (L2.mZ G2 * (L2.H : ℝ)) := by ring
    _ ≤ (P.A * P.D * (P.g : ℝ)) * (P.C2 / (P.g : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hreg
        (mul_nonneg (mul_nonneg P.A_pos.le P.D_pos.le) hg.le)
    _ = P.A * P.D * P.C2 / (P.g : ℝ) := by
      field_simp [ne_of_gt hg]

theorem rank1_return31 (P : VITParameters) {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G3 : ι → ℕ) (L3 : IntLat ι 3)
    (G1 : κ → ℕ) (L1 : IntLat κ 1) (trimmedDensity : ℝ) :
    Rank1Return31 P G3 L3 G1 L1 trimmedDensity := by
  intro hm htrim hregular htransition
  have hg : (0 : ℝ) < P.g := g_pos P
  have hrestore := Algebra.Reg.Return2.restore_absolute_trim P hm htrim
  have hreg : L3.mZ G3 * (L3.H : ℝ) ≤ P.C3 / (P.g : ℝ)^3 := by
    simpa [Regular, VITData.C] using hregular
  calc
    L1.mZ G1 * (L1.H : ℝ) ≤ (P.A * trimmedDensity) * (L1.H : ℝ) :=
      mul_le_mul_of_nonneg_right hrestore (Nat.cast_nonneg _)
    _ = P.A * (trimmedDensity * (L1.H : ℝ)) := by ring
    _ ≤ P.A * (P.E * (P.g : ℝ)^2 * (L3.H : ℝ) * L3.mZ G3) :=
      mul_le_mul_of_nonneg_left htransition P.A_pos.le
    _ = (P.A * P.E * (P.g : ℝ)^2) * (L3.mZ G3 * (L3.H : ℝ)) := by ring
    _ ≤ (P.A * P.E * (P.g : ℝ)^2) * (P.C3 / (P.g : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hreg
        (mul_nonneg (mul_nonneg P.A_pos.le P.E_pos.le) (pow_nonneg hg.le 2))
    _ = P.A * P.E * P.C3 / (P.g : ℝ) := by
      field_simp [ne_of_gt hg]

theorem le_common_of_return21 (P : VITParameters) {x : ℝ}
    (h : x ≤ P.A * P.D * P.C2 / (P.g : ℝ)) :
    x ≤ P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) := by
  refine h.trans ?_
  rw [mul_assoc P.A P.D P.C2]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_max_left _ _) P.A_pos.le) (g_pos P).le

theorem le_common_of_return31 (P : VITParameters) {x : ℝ}
    (h : x ≤ P.A * P.E * P.C3 / (P.g : ℝ)) :
    x ≤ P.A * max (P.D * P.C2) (P.E * P.C3) / (P.g : ℝ) := by
  refine h.trans ?_
  rw [mul_assoc P.A P.E P.C3]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_max_right _ _) P.A_pos.le) (g_pos P).le

theorem newHeight_eq {n r q : ℕ} (T : Algebra.Trans.TransitionInput n r q)
    (L : IntLat (Fin (n + 1)) q) (hnew : T.normal = L.matrix) :
    T.newHeight = L.H := by
  show Algebra.Inverse.Definitions.height T.normal = Algebra.Inverse.Definitions.height L.matrix
  rw [hnew]

theorem oldHeight_eq {n r q : ℕ} (T : Algebra.Trans.TransitionInput n r q)
    (L : IntLat (Fin n) r) (hold : T.old = L.matrix) :
    T.oldHeight = L.H := by
  show Algebra.Inverse.Definitions.height T.old = Algebra.Inverse.Definitions.height L.matrix
  rw [hold]

theorem oldMass_eq {n r q : ℕ} (T : Algebra.Trans.TransitionInput n r q)
    (L : IntLat (Fin n) r) (hold : T.old = L.matrix) :
    T.oldMass = L.mZ T.oldGrids := by
  show Algebra.Inverse.Definitions.mass T.oldGrids
      (Algebra.Inverse.Definitions.imageZ T.oldGrids T.old) =
    Algebra.Inverse.Definitions.mass T.oldGrids
      (Algebra.Inverse.Definitions.imageZ T.oldGrids L.matrix)
  rw [hold]

theorem transition21_raw (P : VITParameters)
    (hT : Algebra.Trans.Transition21 P) (hPlanar : Algebra.Point.PlanarCount)
    (hSection : Algebra.Point.SectionCount3) (hTrim : Algebra.Trim.TrimForIntLat)
    {n : ℕ} (T : Algebra.Trans.TransitionInput n 2 1)
    (hData : Algebra.Trans.TransitionData 2 1 P.toVITData T)
    (L2 : IntLat (Fin n) 2) (L1 : IntLat (Fin (n + 1)) 1)
    (hold : T.old = L2.matrix) (hnew : T.normal = L1.matrix) :
    T.density * (L1.H : ℝ) ≤
      P.D * (P.g : ℝ) * (L2.H : ℝ) * L2.mZ T.oldGrids := by
  have h := hT hPlanar hSection hTrim n T hData
  rw [newHeight_eq T L1 hnew, oldHeight_eq T L2 hold, oldMass_eq T L2 hold] at h
  exact h

theorem transition31_raw (P : VITParameters)
    (hT : Algebra.Trans.Transition31 P) (hPlanar : Algebra.Point.PlanarCount)
    (hSection : Algebra.Point.SectionCount3) (hTrim : Algebra.Trim.TrimForIntLat)
    {n : ℕ} (T : Algebra.Trans.TransitionInput n 3 1)
    (hData : Algebra.Trans.TransitionData 3 1 P.toVITData T)
    (L3 : IntLat (Fin n) 3) (L1 : IntLat (Fin (n + 1)) 1)
    (hold : T.old = L3.matrix) (hnew : T.normal = L1.matrix) :
    T.density * (L1.H : ℝ) ≤
      P.E * (P.g : ℝ)^2 * (L3.H : ℝ) * L3.mZ T.oldGrids := by
  have h := hT hPlanar hSection hTrim n T hData
  rw [newHeight_eq T L1 hnew, oldHeight_eq T L3 hold, oldMass_eq T L3 hold] at h
  exact h

theorem rank1_return21_of_transition (P : VITParameters)
    (hT : Algebra.Trans.Transition21 P) (hPlanar : Algebra.Point.PlanarCount)
    (hSection : Algebra.Point.SectionCount3) (hTrim : Algebra.Trim.TrimForIntLat)
    {n : ℕ} (T : Algebra.Trans.TransitionInput n 2 1)
    (hData : Algebra.Trans.TransitionData 2 1 P.toVITData T)
    (L2 : IntLat (Fin n) 2) (L1 : IntLat (Fin (n + 1)) 1)
    (hold : T.old = L2.matrix) (hnew : T.normal = L1.matrix)
    (hm : P.toVITData.mu ≤ L1.mZ T.grids)
    (htrim : L1.mZ T.grids - P.eps ≤ T.density)
    (hreg : Regular P.toVITData T.oldGrids L2) :
    L1.mZ T.grids * (L1.H : ℝ) ≤ P.A * P.D * P.C2 / (P.g : ℝ) :=
  rank1_return21 P T.oldGrids L2 T.grids L1 T.density hm htrim hreg
    (transition21_raw P hT hPlanar hSection hTrim T hData L2 L1 hold hnew)

theorem rank1_return31_of_transition (P : VITParameters)
    (hT : Algebra.Trans.Transition31 P) (hPlanar : Algebra.Point.PlanarCount)
    (hSection : Algebra.Point.SectionCount3) (hTrim : Algebra.Trim.TrimForIntLat)
    {n : ℕ} (T : Algebra.Trans.TransitionInput n 3 1)
    (hData : Algebra.Trans.TransitionData 3 1 P.toVITData T)
    (L3 : IntLat (Fin n) 3) (L1 : IntLat (Fin (n + 1)) 1)
    (hold : T.old = L3.matrix) (hnew : T.normal = L1.matrix)
    (hm : P.toVITData.mu ≤ L1.mZ T.grids)
    (htrim : L1.mZ T.grids - P.eps ≤ T.density)
    (hreg : Regular P.toVITData T.oldGrids L3) :
    L1.mZ T.grids * (L1.H : ℝ) ≤ P.A * P.E * P.C3 / (P.g : ℝ) :=
  rank1_return31 P T.oldGrids L3 T.grids L1 T.density hm htrim hreg
    (transition31_raw P hT hPlanar hSection hTrim T hData L3 L1 hold hnew)

end Algebra.Reg.Return1

end Praxis.Lift
