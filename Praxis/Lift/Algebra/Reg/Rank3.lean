import Praxis.Lift.Algebra.Reg.Definitions
import Praxis.Algebra.Prefix.Definitions
import Praxis.Lift.Record
import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

set_option linter.ambiguousOpen false

namespace Praxis.Lift

namespace Algebra.Reg

open Praxis.Algebra Praxis.Algebra.Reg

open Finset Praxis.Algebra.Inverse.Definitions Praxis.Lift.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions

open Praxis.Algebra.Reg.Definitions hiding Rank3Height Regularize2 Regularize1 Rank2Promotion Rank2Return

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem height_pos {d : ℕ} (L : IntLat ι d) : 0 < L.H := by
  obtain ⟨r, hdet, hmax⟩ :=
    Algebra.VectorInverse.exists_maximal_basis_minor L.carrier L.saturated L.basis
  have heq : L.H = (L.matrix.submatrix r id).det.natAbs :=
    Algebra.VectorInverse.largestMinor_eq_pivot L.matrix r hmax
  rw [heq]
  exact Int.natAbs_pos.mpr hdet

private theorem height_and_mass_bound {g xi mu C m H : ℝ}
    (hg : 0 < g) (hH : 0 < H) (hxi : 0 ≤ xi)
    (hden : 0 < g^3 * mu - xi/g)
    (hC3 : xi * (1 + (xi / (g^3 * mu - xi/g))/g) ≤ C)
    (hm : mu ≤ m)
    (hchain : m ≤ (1/g^3) * xi * (1/H + 1/g)) :
    H ≤ xi / (g^3 * mu - xi/g) ∧ m * H ≤ C / g^3 := by
  have hg3 : 0 < g^3 := pow_pos hg 3
  have hscaled : g^3 * m ≤ xi * (1/H + 1/g) := by
    have hc : m ≤ (xi * (1/H + 1/g)) / g^3 := by
      simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm,
        mul_left_comm] using hchain
    simpa only [mul_comm] using (le_div_iff₀ hg3).mp hc
  have hproduct : g^3 * m * H ≤ xi * (1 + H/g) := by
    calc
      _ ≤ (xi * (1/H + 1/g)) * H :=
        mul_le_mul_of_nonneg_right hscaled hH.le
      _ = _ := by field_simp [ne_of_gt hH, ne_of_gt hg]
  have hheavy : g^3 * mu * H ≤ g^3 * m * H :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hg3.le) hH.le
  have hheight : H ≤ xi / (g^3 * mu - xi/g) := by
    apply (le_div_iff₀ hden).mpr
    have heq : xi * (1 + H/g) = xi + (xi/g) * H := by ring
    rw [heq] at hproduct
    nlinarith only [hproduct, hheavy]
  refine ⟨hheight, (le_div_iff₀ hg3).mpr ?_⟩
  have hC : g^3 * m * H ≤ C := by
    calc
      _ ≤ xi * (1 + H/g) := hproduct
      _ ≤ xi * (1 + (xi / (g^3 * mu - xi/g))/g) := by
        apply mul_le_mul_of_nonneg_left _ hxi
        linarith only [div_le_div_of_nonneg_right hheight hg.le]
      _ ≤ C := hC3
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hC

theorem rank3_height (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 3)
    (hIntegerMassHeight : IntegerMassHeight L G P.g) : Rank3Height P G L := by
  intro hG hm
  have hpow : 2 ^ 7 ≤ 2 ^ P.L0 := Nat.pow_le_pow_right (by decide) P.L0_lower
  have hg : 2 ≤ P.g := by
    have := P.g_lower
    norm_num at hpow
    omega
  have hgpos : (0 : ℝ) < P.g := by exact_mod_cast (by omega : 0 < P.g)
  have hH : (0 : ℝ) < L.H := by exact_mod_cast height_pos L
  have hxi : 0 ≤ P.toVITData.xi := by unfold VITData.xi; positivity
  exact height_and_mass_bound hgpos hH hxi P.denominator_pos P.C3_height hm
    (hIntegerMassHeight (by decide) (by decide) hg P.g_upper hG.1)

end Algebra.Reg

end Praxis.Lift
