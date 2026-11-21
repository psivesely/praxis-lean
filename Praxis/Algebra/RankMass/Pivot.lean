import Praxis.Algebra.RankMass.PivotZero
import Praxis.Combinatorics.Mass
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler
import Praxis.Algebra.Definitions.Stack
import Praxis.Algebra.Stmt.RankMass

set_option autoImplicit false

namespace Praxis.Algebra.RankMass

open Finset Matrix Praxis.Combinatorics.Mass

open scoped BigOperators

theorem rho_injective {p g : ℕ} [Fact p.Prime] (hgp : g ≤ p) :
    Function.Injective (fun h : Fin g => (((2 + (h.val : ℤ)) : ℤ) : ZMod p)) := by
  intro a b hab
  apply gridInj_zmod p (fun _ : Fin 1 => g) (fun _ => hgp) 0 a b
  simpa only [Int.cast_add, Int.cast_ofNat, Int.cast_natCast, add_right_inj] using hab

theorem centeredF_injective {p N g : ℕ} [Fact p.Prime] {G : Fin N → ℕ}
    (hgp : g ≤ p) (hG : ∀ i, G i ≤ p) :
    Function.Injective (fun x : GridSample g G => (centeredF x : Vec (ZMod p) N)) := by
  rintro ⟨a, k⟩ ⟨b, l⟩ hab
  have hkl : k = l := by
    funext i
    apply gridInj_zmod p G hG i
    have hi := congrFun hab i.succ
    simpa [centeredF, centeredZ] using hi
  subst l
  refine Prod.ext ?_ rfl
  have h0 := congrFun hab 0
  simp only [centeredF, centeredZ, Fin.cases_zero, Int.cast_sub, Int.cast_add] at h0
  apply rho_injective hgp
  simpa only [Int.cast_add, sub_left_inj, add_right_inj] using h0

theorem sampled_count_mul_prod_le {F I J : Type*} [Field F] [DecidableEq F]
    [Fintype I] [DecidableEq I] [Fintype J]
    (H : I → ℕ) (R : ((i : I) → Fin (H i)) → I → F)
    (hinj : Function.Injective R) (A : Matrix J I F) (α : J → F) (S : Finset I)
    (hlocal : ∀ k l, (∀ i, i ∉ S → k i = l i) → ∀ i, i ∉ S → R k i = R l i)
    (hS : ∀ d : I → F, (∀ i, i ∉ S → d i = 0) →
      (∀ j, ∑ i, A j i * d i = 0) → ∀ i, d i = 0) :
    cnt (fun k => A *ᵥ R k) α * ∏ i ∈ S, H i ≤ ∏ i, H i := by
  classical
  unfold cnt
  have h1 : ∏ i ∈ S, H i = #(univ : Finset ((i : S) → Fin (H i))) := by
    rw [card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact (prod_coe_sort S H).symm
  have h2 : ∏ i, H i = #(univ : Finset ((i : I) → Fin (H i))) := by
    simp [Fintype.card_pi]
  rw [h1, h2, ← card_product]
  refine card_le_card_of_injOn
    (fun q i => if h : i ∈ S then q.2 ⟨i, h⟩ else q.1 i)
    (fun _ _ => mem_univ _) ?_
  rintro ⟨k, s⟩ hq ⟨l, t⟩ hq' he
  have hk := (mem_product.mp hq).1
  have hl := (mem_product.mp hq').1
  simp only [mem_filter, mem_univ, true_and] at hk hl
  have hoff : ∀ i, i ∉ S → k i = l i := fun i hi => by
    simpa [hi] using congrFun he i
  have hon : ∀ i : S, s i = t i := fun i => by
    simpa [i.2] using congrFun he i.1
  have hd := hS (fun i => R k i - R l i)
    (fun i hi => sub_eq_zero.mpr (hlocal k l hoff i hi)) (fun j => by
      simp only [mul_sub, sum_sub_distrib]
      change (A *ᵥ R k) j - (A *ᵥ R l) j = 0
      rw [hk, hl, sub_self])
  exact Prod.ext (hinj (funext fun i => sub_eq_zero.mp (hd i))) (funext hon)

theorem sampled_count_mul_rank_le {F I J : Type*} [Field F] [DecidableEq F]
    [Fintype I] [DecidableEq I] [Fintype J]
    (H : I → ℕ) (R : ((i : I) → Fin (H i)) → I → F)
    (hinj : Function.Injective R) (A : Matrix J I F) (α : J → F)
    (i₀ : I) (hcol : A.col i₀ ≠ 0)
    (hlocal : ∀ k l i, i ≠ i₀ → k i = l i → R k i = R l i)
    (b : ℕ) (hb : ∀ i, b ≤ H i) :
    cnt (fun k => A *ᵥ R k) α * b ^ A.rank ≤ ∏ i, H i := by
  classical
  let v : I → J → F := A.col
  obtain ⟨s, -, hs, hspan, hli⟩ := exists_linearIndepOn_extension
    ((linearIndepOn_singleton_iff F).mpr hcol) (Set.subset_univ {i₀})
  have hsp : Submodule.span F (Set.range (fun i : s => v i)) =
      Submodule.span F (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have := hspan ⟨j, Set.mem_univ j, rfl⟩
      simpa only [Set.image_eq_range] using this
  have hr : A.rank = #s.toFinset := by
    rw [Matrix.rank_eq_finrank_span_cols, Set.toFinset_card,
      ← finrank_span_eq_card hli, hsp]
  have hi₀ : i₀ ∈ s.toFinset := by simpa using hs (Set.mem_singleton i₀)
  have hmain := sampled_count_mul_prod_le H R hinj A α s.toFinset
    (fun k l hoff i hi => hlocal k l i (fun he => hi (he.symm ▸ hi₀)) (hoff i hi))
    (fun d hd h0 i => by
      have hsum : ∑ j : s, d j • v j = 0 := by
        have hall : ∑ j : I, d j • v j = 0 := by
          ext a
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          rw [← h0 a]
          exact sum_congr rfl fun _ _ => mul_comm _ _
        rw [← hall]
        exact (Finset.sum_congr_set s _ _ (fun _ _ => rfl)
          (fun j hj => by simp [hd j (by simpa using hj)])).symm
      by_cases hi : i ∈ s
      · exact Fintype.linearIndependent_iff.mp hli _ hsum ⟨i, hi⟩
      · exact hd i (by simpa using hi))
  have hpow : b ^ #s.toFinset ≤ ∏ i ∈ s.toFinset, H i := by
    rw [← prod_const]
    exact prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => hb i
  rw [hr]
  exact (Nat.mul_le_mul_left _ hpow).trans hmain

theorem centered_rank_bound_nonzero {p N d rows g : ℕ} [Fact p.Prime]
    (G : Fin N → ℕ) (hg : 0 < g) (hG : ∀ i, g ≤ G i ∧ G i ≤ p) (hgp : g ≤ p)
    (W : Stack (ZMod p) N d rows) (hnonzero : ∃ v ∈ stackSpace W, v 0 ≠ 0) :
    RankBoundAt g G W := by
  classical
  let H : Fin (N + 1) → ℕ := Fin.cases g G
  let e : GridSample g G ≃ ((i : Fin (N + 1)) → Fin (H i)) :=
    Fin.consEquiv (fun i => Fin (H i))
  let R := fun k => (centeredF (e.symm k) : Vec (ZMod p) N)
  let A : Matrix (Cell d rows × Fin (N + 1)) (Fin (N + 1)) (ZMod p) :=
    Matrix.of (stackRows W)
  have hcol : A.col 0 ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := hnonzero
    apply hv0
    apply coord0_zero_of_rows W _ v hv
    exact fun ki => congrFun h ki
  unfold RankBoundAt stackMass maxAtom
  apply ciSup_le
  intro α
  have hc := sampled_count_mul_rank_le H R
    ((centeredF_injective hgp (fun i => (hG i).2)).comp e.symm.injective)
    A α 0 hcol (fun k l i hi h => by
      refine Fin.cases (fun hi => False.elim (hi rfl)) (fun j _ h => ?_) i hi h
      change (((2 + ((k j.succ).val : ℤ)) : ℤ) : ZMod p) =
        (((2 + ((l j.succ).val : ℤ)) : ℤ) : ZMod p)
      rw [h]) g (by intro i; exact Fin.cases (le_refl g) (fun j => (hG j).1) i)
  rw [rank_stackRows W] at hc
  have hcard : Fintype.card ((i : Fin (N + 1)) → Fin (H i)) = ∏ i, H i := by
    simp [Fintype.card_pi]
  have heq : atom (fun x : GridSample g G =>
      fun ki => dot (stackRows W ki) (centeredF x)) α = atom (fun k => A *ᵥ R k) α := by
    exact (atom_comp_equiv_holds _ _ _ (e.symm) _ α).symm
  rw [heq, atom_eq_cnt, hcard]
  apply (div_le_div_iff₀ (by
    exact_mod_cast prod_pos (fun i _ => Fin.cases hg
      (fun j => lt_of_lt_of_le hg (hG j).1) i))
    (pow_pos (by exact_mod_cast hg) _)).mpr
  simpa only [one_mul, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_prod] using
    (show ((cnt (fun k => A *ᵥ R k) α * g ^ stackRank W : ℕ) : ℝ) ≤
      ((∏ i, H i : ℕ) : ℝ) by exact_mod_cast hc)

theorem centered_rank_bound_holds : centered_rank_bound := by
  intro p _ N d rows g G hg hG hgp W
  classical
  by_cases hz : ∀ v ∈ stackSpace W, v 0 = 0
  · exact centered_rank_bound_zero G hg hG hgp W hz
  · push Not at hz
    exact centered_rank_bound_nonzero G hg hG hgp W hz

end Praxis.Algebra.RankMass
