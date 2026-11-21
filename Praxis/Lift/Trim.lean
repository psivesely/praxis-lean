import Praxis.Algebra.Trim.Assemble
import Praxis.Constants
import Praxis.Algebra.Trim.Definitions
import Praxis.Algebra.TrimAnalysis.CovarianceTrim
import Praxis.Algebra.TrimAnalysis.GaussianMoment
import Praxis.Algebra.TrimAnalysis.GridTrim
import Praxis.Algebra.TrimAnalysis.NumericTrim

set_option autoImplicit false

noncomputable section

open Finset Matrix

namespace Praxis.Lift

def TrimBound (R eps : ℝ) : Prop :=
  1000 * Real.exp (-(99/100 : ℝ) * R^2 / 2) ≤ eps

def TrimSide (R eps : ℝ) : Prop :=
  20 ≤ R ∧ TrimBound R eps

theorem numerical_trim_bound {R eps : ℝ} (h : TrimBound R eps) (d : ℕ) (hd : d ≤ 3) :
    (1-(99/100 : ℝ))^(-(d:ℝ)/2) * Real.exp (-(99/100 : ℝ)*R^2/2) ≤ eps := by
  have hbase : (1-(99/100 : ℝ))^(-(d:ℝ)/2) = (10 : ℝ)^d := by
    rw [show (1-(99/100 : ℝ)) = (10 : ℝ)^(-2 : ℝ) by norm_num]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    rw [show (-2 : ℝ)*(-(d:ℝ)/2) = (d : ℝ) by ring]
    exact Real.rpow_natCast _ _
  have hp : (10 : ℝ)^d ≤ 1000 := by
    calc
      _ ≤ (10 : ℝ)^3 := pow_le_pow_right₀ (by norm_num) hd
      _ = 1000 := by norm_num
  rw [hbase]
  exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans h

variable {Ω : Type*} [Fintype Ω] {d : ℕ}

theorem absolute_trim_covariance (P : Analysis.FiniteLaw Ω) (X : Ω → Fin d → ℝ)
    (m : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (hd : 1 ≤ d ∧ d ≤ 3) (hmgf : Analysis.DirectionalMGF P X m S)
    {R eps : ℝ} (h : TrimBound R eps) :
    P.prob {s | R^2 < Analysis.mahalanobisSq S m (X s)} ≤ eps :=
  (Analysis.ellipsoid_tail P X m S hS hmgf (99/100) R (by norm_num)).trans
    (numerical_trim_bound h d hd.2)

theorem event_absolute_trim (P : Analysis.FiniteLaw Ω) (X : Ω → Fin d → ℝ)
    (m : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (hd : 1 ≤ d ∧ d ≤ 3) (hmgf : Analysis.DirectionalMGF P X m S)
    {R eps : ℝ} (h : TrimBound R eps) (E : Set Ω) :
    P.prob E - eps ≤
      P.prob (E ∩ {s | Analysis.mahalanobisSq S m (X s) ≤ R^2}) := by
  apply P.event_trim
  simpa only [Set.compl_ofPred, not_le] using
    absolute_trim_covariance P X m S hS hd hmgf h

namespace GridImage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {G : ι → ℕ} {B : Matrix ι (Fin d) ℝ}

theorem absolute_trim (T : Analysis.GridImage d G B)
    (hd : 1 ≤ d ∧ d ≤ 3) (hmgf : T.DirectionalMGF) {R eps : ℝ}
    (h : TrimBound R eps) :
    T.probOutsideEllipsoid R ≤ eps := by
  simpa only [Analysis.GridImage.probOutsideEllipsoid, Analysis.GridImage.ellipsoid,
    Set.compl_ofPred, not_le] using
    absolute_trim_covariance T.law (Analysis.gridImage G B) T.center
      (Analysis.gridCovariance G B) T.sigma_pos hd hmgf h

theorem event_trim (T : Analysis.GridImage d G B)
    (hd : 1 ≤ d ∧ d ≤ 3) (hmgf : T.DirectionalMGF) {R eps : ℝ}
    (h : TrimBound R eps) (E : Set (Analysis.Grid G)) :
    T.law.prob E - eps ≤ T.law.prob (E ∩ T.ellipsoid R) :=
  event_absolute_trim T.law (Analysis.gridImage G B) T.center
    (Analysis.gridCovariance G B) T.sigma_pos hd hmgf h E

end GridImage

namespace Algebra.Trim

open Praxis.Analysis

def TrimForIntLat : Prop :=
  ∀ (R eps : ℝ), TrimBound R eps →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (G : ι → ℕ) (_hG : ∀ i, 0 < G i) (B : Matrix ι (Fin d) ℤ),
    (1 ≤ d ∧ d ≤ 3) → LinearIndependent ℤ B.col →
    ∃ T : GridImage d G (B.map (Int.castRingHom ℝ)),
      T.probOutsideEllipsoid R ≤ eps ∧
      ∀ E : Set (Grid G),
        T.law.prob E - eps ≤ T.law.prob (E ∩ T.ellipsoid R)

theorem trimForIntLat (hmgf : Praxis.Algebra.Trim.GridDirectionalMGF) : TrimForIntLat := by
  intro R eps h ι _ _ d G hG B hd hB
  let T : GridImage d G (B.map (Int.castRingHom ℝ)) :=
    ⟨hG, Praxis.Algebra.Trim.gridCovariance_posDef G hG B hB⟩
  have hdir : T.DirectionalMGF := hmgf ι d G T.grid_pos _
  exact ⟨T, Praxis.Lift.GridImage.absolute_trim T hd hdir h,
    Praxis.Lift.GridImage.event_trim T hd hdir h⟩

end Algebra.Trim

theorem two_pow_310_le_exp : (2 : ℝ)^310 ≤ Real.exp (43659/200) := by
  calc
    (2 : ℝ)^310 ≤ (Real.exp (347/500))^310 :=
      pow_le_pow_left₀ (by norm_num) Analysis.two_lt_exp_694.le _
    _ = Real.exp ((310 : ℕ) * (347/500 : ℝ)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (43659/200) := Real.exp_le_exp.mpr (by norm_num)

set_option exponentiation.threshold 400 in

theorem trimSide_main :
    TrimSide ((Praxis.Constants.lift_R_trim : ℕ) : ℝ) ((Praxis.Constants.lift_eps_trim : ℚ) : ℝ) := by
  refine ⟨by norm_num [Praxis.Constants.lift_R_trim], ?_⟩
  unfold TrimBound
  have hR : -(99/100 : ℝ) * ((Praxis.Constants.lift_R_trim : ℕ) : ℝ)^2 / 2 = -(43659/200) := by
    norm_num [Praxis.Constants.lift_R_trim]
  rw [hR, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have heps : (0 : ℝ) ≤ ((Praxis.Constants.lift_eps_trim : ℚ) : ℝ) := by
    norm_num [Praxis.Constants.lift_eps_trim]
  have he : ((Praxis.Constants.lift_eps_trim : ℚ) : ℝ) * 2^310 = 1024 := by
    norm_num [Praxis.Constants.lift_eps_trim]
  have hm := mul_le_mul_of_nonneg_left two_pow_310_le_exp heps
  linarith

end Praxis.Lift

end
