import Praxis.Algebra.RankMass.ZeroCoord
import Praxis.Combinatorics.Mass
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler
import Praxis.Algebra.Definitions.Stack
import Praxis.Algebra.Stmt.RankMass

set_option autoImplicit false

namespace Praxis.Algebra.RankMass

open Finset Matrix Praxis.Combinatorics.Mass

open scoped BigOperators

theorem rank_tail_of_zero {F J : Type*} [Field F] [Fintype J] {N : ℕ}
    (A : Matrix J (Fin (N + 1)) F) (hzero : ∀ j, A j 0 = 0) :
    (Matrix.of (fun j (i : Fin N) => A j i.succ)).rank = A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have hspan : Submodule.span F (Set.range (Matrix.of (fun j (i : Fin N) => A j i.succ)).col) =
      Submodule.span F (Set.range A.col) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.succ, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · have hz : A.col 0 = 0 := funext hzero
        rw [hz]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨j, rfl⟩
  rw [hspan]

theorem rank_stackRows {F : Type*} [Field F] {N d rows : ℕ}
    (W : Stack F N d rows) : (Matrix.of (stackRows W)).rank = stackRank W := by
  rw [Matrix.rank_eq_finrank_span_row]
  rfl

theorem rank_tail_stackRows {F : Type*} [Field F] {N d rows : ℕ}
    (W : Stack F N d rows) (hzero : ∀ v ∈ stackSpace W, v 0 = 0) :
    (Matrix.of (fun ki (i : Fin N) => stackRows W ki i.succ)).rank = stackRank W := by
  exact (rank_tail_of_zero (Matrix.of (stackRows W))
    (fun ki => hzero _ (Submodule.subset_span ⟨ki, rfl⟩))).trans (rank_stackRows W)

theorem stackMass_eq_tail_matMass {p N d rows g : ℕ} [Fact p.Prime]
    (G : Fin N → ℕ) (hg : 0 < g) (W : Stack (ZMod p) N d rows)
    (hzero : ∀ ki, stackRows W ki 0 = 0) :
    stackMass g G W =
      matMass G (fun _ => 2) (fun ki i => stackRows W ki i.succ) := by
  classical
  have : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  unfold stackMass maxAtom matMass
  congr 1
  funext α
  have heq : (fun (w : GridSample g G) ki => dot (stackRows W ki) (centeredF w)) =
      (fun (w : GridSample g G) ki =>
        ∑ i, stackRows W ki i.succ * gval (fun _ => (2 : ZMod p)) w.2 i) := by
    funext w ki
    rw [dot_centeredF_of_zero _ (hzero ki)]
    simp [tailForm, gval]
  rw [heq, atom_prod_snd (fun (k : TailSample G) ki =>
    ∑ i, stackRows W ki i.succ * gval (fun _ => (2 : ZMod p)) k i) α, atom_eq_count]
  unfold matProb matCount
  simp only [Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
  congr 3
  ext k
  simp only [mem_filter, mem_univ, true_and, funext_iff]

theorem centered_rank_bound_split_zero {p N d rows g b : ℕ} [Fact p.Prime]
    (G : Fin N → ℕ) (hg : 0 < g) (hb : 0 < b)
    (hG : ∀ i, b ≤ G i ∧ G i ≤ p) (W : Stack (ZMod p) N d rows)
    (hzero : ∀ v ∈ stackSpace W, v 0 = 0) :
    stackMass g G W ≤ 1 / (b : ℝ) ^ stackRank W := by
  rw [stackMass_eq_tail_matMass G hg W
    (fun ki => hzero _ (Submodule.subset_span ⟨ki, rfl⟩))]
  apply ciSup_le
  intro α
  have hc := matCount_mul_rank_le G (gridInj_zmod p G (fun i => (hG i).2))
    b (fun i => (hG i).1) (fun _ => (2 : ZMod p))
    (fun ki i => stackRows W ki i.succ) α
  rw [rank_tail_stackRows W hzero] at hc
  simpa only [Nat.cast_pow] using
    matProb_le_of_prod G (fun i => lt_of_lt_of_le hb (hG i).1)
      (pow_pos hb (stackRank W)) hc

theorem centered_rank_bound_zero {p N d rows g : ℕ} [Fact p.Prime]
    (G : Fin N → ℕ) (hg : 0 < g) (hG : ∀ i, g ≤ G i ∧ G i ≤ p) (_hgp : g ≤ p)
    (W : Stack (ZMod p) N d rows) (hzero : ∀ v ∈ stackSpace W, v 0 = 0) :
    RankBoundAt g G W :=
  centered_rank_bound_split_zero G hg hg hG W hzero

end Praxis.Algebra.RankMass
