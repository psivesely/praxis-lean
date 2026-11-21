import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Lift.Record
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg.Return2

open Praxis.Algebra Praxis.Algebra.Reg

open Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

theorem restore_absolute_trim (P : VITParameters) {m t : ℝ}
    (hm : P.toVITData.mu ≤ m) (htrim : m - P.eps ≤ t) :
    m ≤ P.A * t := by
  have hmu : 0 < P.toVITData.mu - P.eps := sub_pos.mpr P.eps_lt_mu
  have hmpos : 0 < m - P.eps :=
    lt_of_lt_of_le hmu (sub_le_sub_right hm P.eps)
  have hratio : m / (m - P.eps) ≤
      P.toVITData.mu / (P.toVITData.mu - P.eps) := by
    apply (div_le_div_iff₀ hmpos hmu).mpr
    nlinarith [mul_nonneg P.eps_pos.le (sub_nonneg.mpr hm)]
  exact ((div_le_iff₀ hmpos).mp (hratio.trans P.A_restore)).trans
    (mul_le_mul_of_nonneg_left htrim P.A_pos.le)

theorem rank2_return {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (P : VITParameters)
    (G3 : ι → ℕ) (L3 : IntLat ι 3)
    (G2 : κ → ℕ) (L2 : IntLat κ 2) (trimmedDensity : ℝ) :
    Rank2Return P G3 L3 G2 L2 trimmedDensity := by
  intro hm htrim hregular htransition
  have hgNat : 0 < P.g := lt_of_lt_of_le (Nat.two_pow_pos P.L0) P.g_lower
  have hg : (0 : ℝ) < P.g := by exact_mod_cast hgNat
  have hrestore := restore_absolute_trim P hm htrim
  have hreg : L3.mZ G3 * (L3.H : ℝ) ≤ P.C3 / (P.g : ℝ)^3 := by
    simpa [Regular, VITData.C] using hregular
  calc
    L2.mZ G2 * (L2.H : ℝ) ≤ (P.A * trimmedDensity) * (L2.H : ℝ) :=
      mul_le_mul_of_nonneg_right hrestore (Nat.cast_nonneg _)
    _ = P.A * (trimmedDensity * (L2.H : ℝ)) := by ring
    _ ≤ P.A * (P.D * (P.g : ℝ) * (L3.H : ℝ) * L3.mZ G3) :=
      mul_le_mul_of_nonneg_left htransition P.A_pos.le
    _ = (P.A * P.D * (P.g : ℝ)) * (L3.mZ G3 * (L3.H : ℝ)) := by ring
    _ ≤ (P.A * P.D * (P.g : ℝ)) * (P.C3 / (P.g : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hreg
        (mul_nonneg (mul_nonneg P.A_pos.le P.D_pos.le) hg.le)
    _ = P.A * P.D * P.C3 / (P.g : ℝ)^2 := by
      field_simp [ne_of_gt hg]

end Algebra.Reg.Return2

end Praxis.Lift
