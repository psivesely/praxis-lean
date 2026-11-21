import Praxis.Algebra.InverseBranches.JumpFree
import Praxis.Algebra.ChainLemma.UnequalChain
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Praxis.Combinatorics.Chain

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.VectorInverse

open Finset Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

open scoped BigOperators Matrix

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [DecidableEq A]

theorem adjoin_relIndex (H : AddSubgroup A) (x : A) :
    H.relIndex (H ⊔ AddSubgroup.zmultiples x) = addOrderOf (QuotientAddGroup.mk' H x) := by
  let q := QuotientAddGroup.mk' H
  have hker : q.ker = H := QuotientAddGroup.ker_mk' H
  have hmap : H.map q = ⊥ := by
    apply le_antisymm _ bot_le
    rw [AddSubgroup.map_le_iff_le_comap]
    change H ≤ q.ker
    exact le_of_eq hker.symm
  calc
    _ = q.ker.relIndex (H ⊔ AddSubgroup.zmultiples x) := by rw [hker]
    _ = Nat.card ((H ⊔ AddSubgroup.zmultiples x).map q) := AddSubgroup.relIndex_ker _ q
    _ = _ := by
      rw [AddSubgroup.map_sup, hmap, AddMonoidHom.map_zmultiples]
      rw [bot_sup_eq]
      change Nat.card (AddSubgroup.zmultiples (q x)) = addOrderOf (q x)
      exact Nat.card_zmultiples (q x)

theorem quotient_residue_step {G : ι → ℕ} {y : ι → A} {S : Finset ι} {ρ : ℝ}
    (hb : FibBd G y S ρ) (H : AddSubgroup A) (hS : ∀ i ∈ S, y i ∈ H)
    {j : ι} (hj : j ∉ S) (hG : 0 < G j)
    (hv : 0 < H.relIndex (H ⊔ AddSubgroup.zmultiples (y j))) :
    FibBd G y (insert j S) (ρ * ((((G j + H.relIndex (H ⊔ AddSubgroup.zmultiples (y j)) - 1) /
      H.relIndex (H ⊔ AddSubgroup.zmultiples (y j)) : ℕ) : ℝ) / G j)) := by
  intro k₀ t
  let v := H.relIndex (H ⊔ AddSubgroup.zmultiples (y j))
  let q := QuotientAddGroup.mk' H
  let R := (fib G y (insert j S) k₀ t).image fun k => k j
  have hsum (k : (i : ι) → Fin (G i)) : q (∑ i ∈ S, y i * ((k i : ℕ) : A)) = 0 := by
    rw [map_sum]
    apply sum_eq_zero
    intro i hi
    have hy : q (y i) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr (hS i hi)
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, hy, nsmul_zero]
  have hval {k : (i : ι) → Fin (G i)} (hk : k ∈ fib G y (insert j S) k₀ t) :
      (k j : ℕ) • q (y j) = q t := by
    have he := (mem_fib.mp hk).2
    rw [sum_insert hj] at he
    have := congrArg q he
    rw [map_add, hsum, add_zero, mul_comm, ← nsmul_eq_mul, map_nsmul] at this
    exact this
  have hmod : ∀ a ∈ R, ∀ b ∈ R, (a : ℕ) ≡ b [MOD v] := by
    intro a ha b hb'
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
    obtain ⟨k', hk', rfl⟩ := mem_image.mp hb'
    apply Nat.modEq_iff_dvd.mpr
    rw [show v = addOrderOf (q (y j)) from adjoin_relIndex H (y j)]
    apply addOrderOf_dvd_iff_zsmul_eq_zero.mpr
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hval hk', hval hk]
    simp
  have hc : #R ≤ (G j + v - 1) / v := card_le_ceil hv R hmod
  have hc' := card_fib_insert_le hj hb k₀ t R (fun k hk => mem_image_of_mem _ hk)
  have hnn := hb.nonneg k₀
  have hG0 : (G j : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  calc
    (#(fib G y (insert j S) k₀ t) : ℝ) ≤ #R * ((∏ i ∈ S, (G i : ℝ)) * ρ) := hc'
    _ ≤ ((G j + v - 1) / v : ℕ) * ((∏ i ∈ S, (G i : ℝ)) * ρ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hnn
    _ = _ := by rw [prod_insert hj]; dsimp [v]; field_simp

end Praxis.Algebra.VectorInverse
