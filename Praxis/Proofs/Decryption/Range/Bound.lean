import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler

namespace Praxis.Proofs.Decryption.Bound

open Praxis.Algebra (Vec dot centerA centeredZ)

theorem core (N g : ℕ) (hN : 0 < N) (hg : 0 < g) (A : ℤ) (h : ℕ) (hh : h < g)
    (a t : Fin N → ℤ) (ha : ∀ i, a i = 0 ∨ a i = 1)
    (ht : ∀ i, 2 ≤ t i ∧ t i ≤ (g : ℤ) + 1) :
    |(A + (2 + (h : ℤ)) - (∑ i, t i) / 2 + ∑ i, a i * t i) -
        ⌊(A : ℚ) + (((g : ℚ) + 1) / 2 + 1) +
          ∑ i, ((a i : ℚ) - 1 / 2) * (((g : ℚ) + 1) / 2 + 1)⌋| ≤
      (((N + 1) * (g + 1) : ℕ) : ℤ) := by
  generalize hS : ∑ i, t i = S
  generalize hd : S / 2 = d
  generalize hm : (A : ℚ) + (((g : ℚ) + 1) / 2 + 1) +
          ∑ i, ((a i : ℚ) - 1 / 2) * (((g : ℚ) + 1) / 2 + 1) = m
  have hS2 : 2 * d ≤ S ∧ S ≤ 2 * d + 1 := by omega
  have hS2q : 2 * (d : ℚ) ≤ (S : ℚ) ∧ (S : ℚ) ≤ 2 * (d : ℚ) + 1 := by
    constructor <;> exact_mod_cast (by omega : _)
  have hSq : (S : ℚ) = ∑ i, (t i : ℚ) := by
    rw [← hS]; push_cast; rfl
  have hgq : (0 : ℚ) < g := by exact_mod_cast hg
  have hg1 : (1 : ℚ) ≤ g := by exact_mod_cast hg
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hhq : (h : ℚ) + 1 ≤ g := by exact_mod_cast hh
  have hh0 : (0 : ℚ) ≤ h := by positivity
  set c : ℚ := ((g : ℚ) + 1) / 2 + 1 with hc
  have hsum : ∑ i : Fin N, ((a i : ℚ) * (t i : ℚ)) -
      ∑ i : Fin N, (((a i : ℤ) : ℚ) - 1 / 2) * c =
      ∑ i : Fin N, (((a i : ℚ) - 1 / 2) * ((t i : ℚ) - c)) + (S : ℚ) / 2 := by
    rw [hSq, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hterm : ∀ i : Fin N,
      |((a i : ℚ) - 1 / 2) * ((t i : ℚ) - c)| ≤ ((g : ℚ) + 1) / 4 := by
    intro i
    obtain ⟨t1, t2⟩ := ht i
    have t1q : (2 : ℚ) ≤ (t i : ℚ) := by exact_mod_cast t1
    have t2q : (t i : ℚ) ≤ (g : ℚ) + 1 := by exact_mod_cast t2
    rw [abs_le]
    rcases ha i with h' | h'
    · have : (a i : ℚ) = 0 := by exact_mod_cast h'
      rw [this]
      constructor <;> nlinarith
    · have : (a i : ℚ) = 1 := by exact_mod_cast h'
      rw [this]
      constructor <;> nlinarith
  have hsumb : |∑ i : Fin N, (((a i : ℚ) - 1 / 2) * ((t i : ℚ) - c))| ≤
      (N : ℚ) * (((g : ℚ) + 1) / 4) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    simp
  rw [abs_le] at hsumb
  have hrq : ((A + (2 + (h : ℤ)) - d + ∑ i, a i * t i : ℤ) : ℚ) - m =
      (2 + (h : ℚ) - c) - (d : ℚ) +
        ((∑ i : Fin N, (((a i : ℚ) - 1 / 2) * ((t i : ℚ) - c))) + (S : ℚ) / 2) := by
    rw [← hm]
    push_cast
    linarith
  have hfl1 := Int.floor_le m
  have hfl2 := Int.lt_floor_add_one m
  generalize hF : ⌊m⌋ = F at hfl1 hfl2 ⊢
  generalize hR : A + (2 + (h : ℤ)) - d + ∑ i, a i * t i = R at hrq ⊢
  rw [abs_le]
  have hT : (((N + 1) * (g + 1) : ℕ) : ℚ) = ((N : ℚ) + 1) * ((g : ℚ) + 1) := by push_cast; ring
  have hNg : (0 : ℚ) ≤ (N : ℚ) * ((g : ℚ) + 1) := by positivity
  constructor
  · have : -(((N + 1) * (g + 1) : ℕ) : ℚ) ≤ (R : ℚ) - (F : ℚ) := by
      rw [hT]
      nlinarith [hsumb.1, hsumb.2]
    exact_mod_cast this
  · have : (R : ℚ) - (F : ℚ) ≤ (((N + 1) * (g + 1) : ℕ) : ℚ) := by
      rw [hT]
      nlinarith [hsumb.1, hsumb.2]
    exact_mod_cast this

theorem range_general (P : Params) (hq : 1 < P.q) (hN : 0 < P.N) (hg : 0 < P.g)
    (hT : P.tBound = (P.N + 1) * (P.g + 1)) (x : Vec (Fq P) P.N) (hx0 : x 0 = 1)
    (hb : ∀ j : Fin P.N, x j.succ = 0 ∨ x j.succ = 1) (w : SearchSample P) :
    |rOf (toInt x) (rInt w) - cX (toInt x)| ≤ (P.tBound : ℤ) := by
  haveI : Fact (1 < P.q) := ⟨hq⟩
  obtain ⟨h, k⟩ := w
  have h0 : toInt x 0 = 1 := by
    simp only [toInt, hx0, ZMod.val_one, Nat.cast_one]
  have ha : ∀ i : Fin P.N, toInt x i.succ = 0 ∨ toInt x i.succ = 1 := by
    intro i
    rcases hb i with h | h
    · left
      simp only [toInt, h, ZMod.val_zero, Nat.cast_zero]
    · right
      simp only [toInt, h, ZMod.val_one, Nat.cast_one]
  have hr : rOf (toInt x) (rInt (h, k)) =
      centerA (widths P) + (2 + (h.val : ℤ)) - (∑ i, (2 + ((k i).val : ℤ))) / 2 +
        ∑ i : Fin P.N, toInt x i.succ * (2 + ((k i).val : ℤ)) := by
    unfold rOf
    rw [Fin.sum_univ_succ, h0]
    simp [rInt, centeredZ]
  have hkb : ∀ i, (2 : ℤ) ≤ 2 + ((k i).val : ℤ) ∧ 2 + ((k i).val : ℤ) ≤ (P.g : ℤ) + 1 := by
    intro i
    have h1 : (k i).val < P.g := by
      have := (k i).isLt
      simpa [widths] using this
    omega
  rw [hT, hr]
  have := core P.N P.g hN hg (centerA (widths P)) h.val h.isLt
    (fun i => toInt x i.succ) (fun i => 2 + ((k i).val : ℤ)) ha hkb
  unfold cX muX
  convert this using 6

end Praxis.Proofs.Decryption.Bound
