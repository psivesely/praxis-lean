import Praxis.Algebra.Reg.Rank1Model
import Praxis.Algebra.Reg.Stretch2
import Praxis.Algebra.Power.Definitions
import Praxis.Algebra.Power.Stretch
import Praxis.Algebra.Power.Ceiling
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

namespace Praxis.Algebra.Reg.Stretch1

open Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Reg.Rank1Model Praxis.Algebra.Prefix.Definitions

theorem rank1_stretch (hStretch : Algebra.Power.StretchEstimate)
    (L0 : ℕ) {n : ℕ} {κ : Fin (n + 1) → Type*}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 1)
    (width order : Fin n → ℕ) : Rank1Stretch L0 G L width order := by
  intro hL0 hG hwidth horder hheight hmass
  have hs (k : Fin n) :
      (((L k.succ).mZ (G k.succ) * ((L k.succ).H : ℝ)) ^ (L0 - 1)) *
          (L k.succ).mZ (G k.succ) ≤
        (((L k.castSucc).mZ (G k.castSucc) * ((L k.castSucc).H : ℝ)) ^ (L0 - 1)) *
          (L k.castSucc).mZ (G k.castSucc) := by
    apply hStretch L0 1 (fun _ => width k) (fun _ => order k)
      (fun j => if j = 0 then (L k.castSucc).H else (L k.succ).H)
      (fun j => if j = 0 then (L k.castSucc).mZ (G k.castSucc)
        else (L k.succ).mZ (G k.succ)) hL0
      (fun _ _ => hwidth k) (fun _ _ => le_trans (by decide : 1 ≤ 2) (horder k).1)
      (fun _ _ => (horder k).2)
    · intro j _
      dsimp only
      split_ifs
      · exact Algebra.Reg.integer_mass_nonneg _ _ (hG k.castSucc)
      · exact Algebra.Reg.integer_mass_nonneg _ _ (hG k.succ)
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa only [ite_true, ite_false, Nat.zero_add, Nat.one_ne_zero, mul_div_assoc]
        using hmass k
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa only [ite_true, ite_false, Nat.zero_add, Nat.one_ne_zero, Nat.mul_comm]
        using hheight k
  have hb (i : Fin (n + 1)) :
      (((L i).mZ (G i) * ((L i).H : ℝ)) ^ (L0 - 1)) * (L i).mZ (G i) ≤
        (((L 0).mZ (G 0) * ((L 0).H : ℝ)) ^ (L0 - 1)) * (L 0).mZ (G 0) := by
    induction i using Fin.induction with
    | zero => exact le_rfl
    | succ k hk => exact (hs k).trans hk
  exact hb (Fin.last n)

end Praxis.Algebra.Reg.Stretch1
