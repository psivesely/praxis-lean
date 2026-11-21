import Praxis.Algebra.ChainLemma.UnequalChain
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Praxis.Combinatorics.Chain

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.RankThree

open Finset Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing A] [DecidableEq A]

theorem relIndex_adjoin (H : AddSubgroup A) (x : A) :
    H.relIndex (H ⊔ AddSubgroup.zmultiples x) =
      addOrderOf (QuotientAddGroup.mk' H x) := by
  let q := QuotientAddGroup.mk' H
  have hker : q.ker = H := QuotientAddGroup.ker_mk' H
  have hmap : H.map q = ⊥ := by
    apply le_antisymm _ bot_le
    rw [AddSubgroup.map_le_iff_le_comap]
    change H ≤ q.ker
    exact le_of_eq hker.symm
  calc
    _ = q.ker.relIndex (H ⊔ AddSubgroup.zmultiples x) := by rw [hker]
    _ = Nat.card ((H ⊔ AddSubgroup.zmultiples x).map q) :=
      AddSubgroup.relIndex_ker _ q
    _ = _ := by
      rw [AddSubgroup.map_sup, hmap, AddMonoidHom.map_zmultiples]
      rw [bot_sup_eq, Nat.card_zmultiples]

theorem residue_step {G : ι → ℕ} {y : ι → A} {S : Finset ι} {ρ : ℝ}
    (hb : FibBd G y S ρ) (H : AddSubgroup A)
    (hS : ∀ i ∈ S, y i ∈ H) {j : ι} (hj : j ∉ S)
    (hG : 0 < G j) (hv : 0 < H.relIndex (H ⊔ AddSubgroup.zmultiples (y j))) :
    FibBd G y (insert j S)
      (ρ * ((((G j + H.relIndex (H ⊔ AddSubgroup.zmultiples (y j)) - 1) /
        H.relIndex (H ⊔ AddSubgroup.zmultiples (y j)) : ℕ) : ℝ) / G j)) := by
  intro k₀ t
  let v := H.relIndex (H ⊔ AddSubgroup.zmultiples (y j))
  let q := QuotientAddGroup.mk' H
  let R := (fib G y (insert j S) k₀ t).image fun k => k j
  have hsum (k : (i : ι) → Fin (G i)) :
      q (∑ i ∈ S, y i * ((k i : ℕ) : A)) = 0 := by
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
    rw [show v = addOrderOf (q (y j)) from relIndex_adjoin H (y j)]
    apply addOrderOf_dvd_iff_zsmul_eq_zero.mpr
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hval hk', hval hk]
    exact add_neg_cancel (q t)
  have hc : #R ≤ (G j + v - 1) / v := card_le_ceil hv R hmod
  have hc' := card_fib_insert_le hj hb k₀ t R (fun k hk => mem_image_of_mem _ hk)
  have hnn := hb.nonneg k₀
  have hG0 : (G j : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  calc
    (#(fib G y (insert j S) k₀ t) : ℝ) ≤ #R * ((∏ i ∈ S, (G i : ℝ)) * ρ) := hc'
    _ ≤ ((G j + v - 1) / v : ℕ) * ((∏ i ∈ S, (G i : ℝ)) * ρ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hnn
    _ = _ := by rw [prod_insert hj]; dsimp [v]; field_simp

structure ChainState (G : ι → ℕ) (y : ι → A) (g M : ℕ) (D : ℝ)
    (S : Finset ι) (H : AddSubgroup A) (T k : ℕ) (ρ : ℝ) : Prop where
  contains : ∀ i ∈ S, y i ∈ H
  indexpos : 0 < H.index
  tpos : 0 < T
  product : H.index * T = M
  bd : FibBd G y S ρ
  merged : ρ ≤ D * correction g ^ k * (1 / (T : ℝ) + 1 / (g : ℝ))
  coarse : ρ ≤ D * (correction g / 2) ^ k

theorem ChainState.step {G : ι → ℕ} {y : ι → A} {g M : ℕ} {D : ℝ}
    {S : Finset ι} {H : AddSubgroup A} {T k : ℕ} {ρ : ℝ}
    (st : ChainState G y g M D S H T k ρ)
    (hg : 0 < g) (hG : ∀ j, g ≤ G j) (hD : 0 ≤ D)
    {j : ι} (hj : y j ∉ H) :
    ∃ (H' : AddSubgroup A) (v : ℕ),
      ChainState G y g M D (insert j S) H' (T * v) (k + 1)
        (ρ * ((((G j + v - 1) / v : ℕ) : ℝ) / G j)) := by
  let H' := H ⊔ AddSubgroup.zmultiples (y j)
  let v := H.relIndex H'
  have hprod : v * H'.index = H.index := AddSubgroup.relIndex_mul_index le_sup_left
  have hv0 : 0 < v := by have := st.indexpos; nlinarith
  have hv1 : v ≠ 1 := by
    intro h
    have hh : H' ≤ H := AddSubgroup.relIndex_eq_one.mp h
    exact hj (hh ((show AddSubgroup.zmultiples (y j) ≤ H' from le_sup_right)
      (AddSubgroup.mem_zmultiples (y j))))
  have hv2 : 2 ≤ v := by omega
  have hH' : 0 < H'.index := by have := st.indexpos; nlinarith
  have hjS : j ∉ S := fun h => hj (st.contains j h)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
  have hvR2 : (2 : ℝ) ≤ v := by exact_mod_cast hv2
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast st.tpos
  have hc0 : 0 ≤ correction g := by unfold correction; positivity
  have hq := ceil_factor_le hg (hG j) hv0
  have hm := merging_reciprocal hg0 hTR hvR
  have hhalf : 1 / (v : ℝ) + 1 / (g : ℝ) ≤ correction g / 2 := by
    have hh : 1 / (v : ℝ) ≤ 1 / (2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hvR2
    calc
      _ ≤ 1 / (2 : ℝ) + 1 / (g : ℝ) := add_le_add hh le_rfl
      _ = _ := by unfold correction; ring
  have hq0 : 0 ≤ ((((G j + v - 1) / v : ℕ) : ℝ) / G j) := by positivity
  refine ⟨H', v, ?_⟩
  exact {
    contains := by
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact (show AddSubgroup.zmultiples (y i) ≤ H' from le_sup_right)
          (AddSubgroup.mem_zmultiples _)
      · exact (show H ≤ H' from le_sup_left) (st.contains i hi)
    indexpos := hH'
    tpos := Nat.mul_pos st.tpos hv0
    product := by rw [← st.product]; dsimp [v] at hprod; nlinarith [hprod]
    bd := residue_step st.bd H st.contains hjS (lt_of_lt_of_le hg (hG j)) hv0
    merged := by
      calc
        ρ * _ ≤ (D * correction g ^ k * (1 / (T : ℝ) + 1 / (g : ℝ))) *
            (1 / (v : ℝ) + 1 / (g : ℝ)) :=
          mul_le_mul st.merged hq hq0 (by positivity)
        _ ≤ (D * correction g ^ k) *
            ((1 + 2 / (g : ℝ)) * (1 / ((T : ℝ) * v) + 1 / (g : ℝ))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hm (by positivity)
        _ = _ := by rw [pow_succ]; push_cast; unfold correction; ring
    coarse := by
      calc
        ρ * _ ≤ (D * (correction g / 2) ^ k) * (correction g / 2) :=
          mul_le_mul st.coarse (hq.trans hhalf) hq0 (by positivity)
        _ = _ := by rw [pow_succ]; ring }

theorem finish_chain {G : ι → ℕ} {y : ι → A} {g M N : ℕ} {D : ℝ}
    (hg : 0 < g) (hG : ∀ j, g ≤ G j) (hpow : g ≤ 2 ^ N) (hD : 0 ≤ D)
    (hprimitive : AddSubgroup.closure (Set.range y) = ⊤)
    (n : ℕ) {S : Finset ι} {H : AddSubgroup A} {T k : ℕ} {ρ : ℝ}
    (hk : k + n = N) (st : ChainState G y g M D S H T k ρ) :
    FibBd G y univ (D * correction g ^ N * (1 / (M : ℝ) + 1 / (g : ℝ))) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hc : 1 ≤ correction g := by unfold correction; linarith [show 0 ≤ 2 / (g : ℝ) by positivity]
  induction n generalizing S H T k ρ with
  | zero =>
    have hkN : k = N := by omega
    have htwo : (g : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hpow
    have hinv : 1 / (2 : ℝ) ^ N ≤ 1 / (g : ℝ) := one_div_le_one_div_of_le hg0 htwo
    apply (st.bd.extend (subset_univ S)).mono
    calc
      ρ ≤ D * (correction g / 2) ^ k := st.coarse
      _ = D * correction g ^ N * (1 / (2 : ℝ) ^ N) := by rw [hkN, div_pow]; ring
      _ ≤ D * correction g ^ N * (1 / (g : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  | succ n ih =>
    by_cases hh : H.index = 1
    · have hT : T = M := by simpa [hh] using st.product
      apply (st.bd.extend (subset_univ S)).mono
      calc
        ρ ≤ D * correction g ^ k * (1 / (T : ℝ) + 1 / (g : ℝ)) := st.merged
        _ ≤ D * correction g ^ N * (1 / (T : ℝ) + 1 / (g : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc (by omega)) hD
        _ = _ := by rw [hT]
    · have hj : ∃ j, y j ∉ H := by
        by_contra! h
        have hle : AddSubgroup.closure (Set.range y) ≤ H :=
          (AddSubgroup.closure_le H).mpr (by rintro _ ⟨j, rfl⟩; exact h j)
        rw [hprimitive] at hle
        exact hh (AddSubgroup.index_eq_one.mpr (top_le_iff.mp hle))
      obtain ⟨j, hj⟩ := hj
      obtain ⟨H', v, hs⟩ := st.step hg hG hD hj
      exact ih (by omega) hs

end Praxis.Algebra.RankThree
