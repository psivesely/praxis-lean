import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Power.Definitions
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

namespace Praxis.Algebra.Reg

open Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Reg.Definitions

theorem integer_mass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (G : ι → ℕ) (L : IntLat ι d) (hG : ∀ i, 0 < G i) :
    0 ≤ L.mZ G := by
  let : Nonempty (Grid G) := ⟨fun i => ⟨0, hG i⟩⟩
  exact Algebra.FiniteProbability.atomMass_nonneg (imageZ G L.matrix)

theorem rank2_stretch_of_estimate (hStretch : Algebra.Power.StretchEstimate)
    (L0 : ℕ) {n : ℕ} {κ : Fin (n + 1) → Type*}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 2)
    (width order : Fin n → ℕ) : Rank2Stretch L0 G L width order := by
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
      · exact integer_mass_nonneg _ _ (hG k.castSucc)
      · exact integer_mass_nonneg _ _ (hG k.succ)
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

end Praxis.Algebra.Reg
