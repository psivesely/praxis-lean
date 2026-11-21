import Praxis.Algebra.Trans.AlgModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Praxis.Algebra.Trans

private theorem multiset_esymm_one {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

private theorem multiset_esymm_cons {R : Type*} [CommSemiring R]
    (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
    Multiset.sum_map_mul_left]

private theorem multiset_esymm_two_identity {R : Type*} [CommRing R]
    (s : Multiset R) :
    2 * s.esymm 2 = s.sum ^ 2 - (s.map (fun a => a ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | @cons a s ih =>
      rw [multiset_esymm_cons a s 1, multiset_esymm_one]
      simp only [Multiset.sum_cons, Multiset.map_cons]
      rw [mul_add, ih]
      ring

private theorem multiset_esymm_bounds {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] (s : Multiset R)
    (h : ∀ a ∈ s, 0 ≤ a) :
    0 ≤ s.sum ∧ 2 * s.esymm 2 ≤ s.sum ^ 2 ∧
      3 * s.esymm 3 ≤ s.sum * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | @cons a s ih =>
      have ha : 0 ≤ a := h a (Multiset.mem_cons_self a s)
      have hs : ∀ b ∈ s, 0 ≤ b :=
        fun b hb => h b (Multiset.mem_cons_of_mem hb)
      obtain ⟨hsum, htwo, hthree⟩ := ih hs
      rw [multiset_esymm_cons a s 1, multiset_esymm_cons a s 2,
        multiset_esymm_one, Multiset.sum_cons]
      refine ⟨add_nonneg ha hsum, ?_, ?_⟩
      · nlinarith [sq_nonneg a]
      · have hmul := mul_le_mul_of_nonneg_left htwo ha
        have hsq := mul_nonneg (sq_nonneg a) hsum
        nlinarith

section OrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

variable {ι : Type*} [Fintype ι]

theorem elementarySymmetric_two_eq (w : ι → R) :
    elementarySymmetric w 2 = ((∑ i, w i) ^ 2 - ∑ i, w i ^ 2) / 2 := by
  have hid := multiset_esymm_two_identity ((Finset.univ : Finset ι).val.map w)
  simp only [Multiset.map_map, Function.comp_def, Finset.sum_map_val] at hid
  change 2 * elementarySymmetric w 2 = _ at hid
  linarith

theorem elementarySymmetric_three_mul_le (w : ι → R) (hw : ∀ i, 0 ≤ w i) :
    3 * elementarySymmetric w 3 ≤ (∑ i, w i) * elementarySymmetric w 2 := by
  have hb := multiset_esymm_bounds ((Finset.univ : Finset ι).val.map w) (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
    exact hw i)
  simpa only [elementarySymmetric, Finset.sum_map_val] using hb.2.2

theorem esymBounds [DecidableEq ι] (w : ι → R) (S : R) : ESymBounds w S := by
  intro hw hS
  have hnonneg : 0 ≤ S := hS ▸ Finset.sum_nonneg (fun i _ => hw i)
  have hsquares : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  have hid := elementarySymmetric_two_eq w
  have hthree := elementarySymmetric_three_mul_le w hw
  rw [hS] at hid hthree
  have htwo : elementarySymmetric w 2 ≤ S ^ 2 / 2 := by linarith
  refine ⟨htwo, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left htwo hnonneg
  nlinarith

end OrderedField

end Praxis.Algebra.Trans
