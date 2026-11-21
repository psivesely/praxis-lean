import Praxis.Proofs.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification.GateGeometry

variable {k I : Type*} [Field k]

def cut (V : Submodule k (I → k)) (i : I) : Submodule k (I → k) :=
  V ⊓ LinearMap.ker (LinearMap.proj i)

lemma cut_mem (V : Submodule k (I → k)) (i : I) (x : I → k) :
    x ∈ cut V i ↔ x ∈ V ∧ x i = 0 := Iff.rfl

lemma cut_lt (V : Submodule k (I → k)) (i : I)
    (h : ∃ x ∈ V, x i ≠ 0) : cut V i < V := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro heq
  obtain ⟨x, hx, hxi⟩ := h
  have : x ∈ cut V i := heq.symm ▸ hx
  exact hxi this.2

lemma exists_cut_lt [Fintype I] (V : Submodule k (I → k)) (h : V ≠ ⊥) :
    ∃ i, Module.finrank k (cut V i) < Module.finrank k V := by
  obtain ⟨x, hx, hx0⟩ := V.ne_bot_iff.mp h
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! hn
    exact hx0 (funext hn)
  exact ⟨i, Submodule.finrank_lt_finrank_of_lt (cut_lt V i ⟨x, hx, hi⟩)⟩

lemma two_coordinates [Fintype I] (V : Submodule k (I → k)) (o : I)
    (hd : Module.finrank k V ≤ 3) (h : ∃ x ∈ V, x o ≠ 0) :
    ∃ i j : I, ∀ x ∈ V, x o = 0 → x i = 0 → x j = 0 → x = 0 := by
  have h0 : Module.finrank k (cut V o) ≤ 2 := by
    have := Submodule.finrank_lt_finrank_of_lt (cut_lt V o h)
    omega
  by_cases hbot : cut V o = ⊥
  · refine ⟨o, o, fun x hx hxo _ _ => ?_⟩
    exact (Submodule.mem_bot k).mp (hbot ▸ (cut_mem V o x).mpr ⟨hx, hxo⟩)
  obtain ⟨i, hi⟩ := exists_cut_lt (cut V o) hbot
  have h1 : Module.finrank k (cut (cut V o) i) ≤ 1 := by omega
  by_cases hbot1 : cut (cut V o) i = ⊥
  · refine ⟨i, o, fun x hx hxo hxi _ => ?_⟩
    exact (Submodule.mem_bot k).mp (hbot1 ▸
      (cut_mem _ i x).mpr ⟨(cut_mem V o x).mpr ⟨hx, hxo⟩, hxi⟩)
  obtain ⟨j, hj⟩ := exists_cut_lt (cut (cut V o) i) hbot1
  have h2 : cut (cut (cut V o) i) j = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  refine ⟨i, j, fun x hx hxo hxi hxj => ?_⟩
  exact (Submodule.mem_bot k).mp (h2 ▸
    (cut_mem _ j x).mpr ⟨(cut_mem _ i x).mpr
      ⟨(cut_mem V o x).mpr ⟨hx, hxo⟩, hxi⟩, hxj⟩)

lemma square_sum_pair (xs : Finset (I → k)) (e : (I → k) → k)
    (h : ∀ i j, ∑ x ∈ xs, e x * x i * x j = 0)
    (o i j : I) (a b c d : k) :
    ∑ x ∈ xs, e x * (a * x o + b * x i) * (c * x o + d * x j) = 0 := by
  calc
    _ = (a*c) * (∑ x ∈ xs, e x * x o * x o) +
        (a*d) * (∑ x ∈ xs, e x * x o * x j) +
        (b*c) * (∑ x ∈ xs, e x * x i * x o) +
        (b*d) * (∑ x ∈ xs, e x * x i * x j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = 0 := by rw [h, h, h, h]; ring

set_option maxHeartbeats 1000000 in
lemma boolean_squares [Fintype I] (V : Submodule k (I → k)) (o : I)
    (hd : Module.finrank k V ≤ 3) (xs : Finset (I → k))
    (hx : ∀ x ∈ xs, x ∈ V ∧ x o = 1 ∧ ∀ i, x i = 0 ∨ x i = 1)
    (e : (I → k) → k) (he : ∀ i j, ∑ x ∈ xs, e x * x i * x j = 0) :
    ∀ x ∈ xs, e x = 0 := by
  classical
  let : DecidableEq k := Classical.decEq k
  intro x hxx
  obtain ⟨i, j, hij⟩ := two_coordinates V o hd ⟨x, (hx x hxx).1, by
    rw [(hx x hxx).2.1]; exact one_ne_zero⟩
  have hsep : ∀ y ∈ xs, y i = x i → y j = x j → y = x := by
    intro y hy hi hj
    apply sub_eq_zero.mp
    exact hij (y-x) (V.sub_mem (hx y hy).1 (hx x hxx).1)
      (by simp [(hx y hy).2.1, (hx x hxx).2.1]) (by simp [hi]) (by simp [hj])
  let a : k := if x i = 0 then 1 else 0
  let b : k := if x i = 0 then -1 else 1
  let c : k := if x j = 0 then 1 else 0
  let d : k := if x j = 0 then -1 else 1
  have hi : ∀ y ∈ xs, a*y o+b*y i = if y i = x i then 1 else 0 := by
    intro y hy
    rcases (hx x hxx).2.2 i with hxi | hxi <;>
      rcases (hx y hy).2.2 i with hyi | hyi <;>
      simp [a, b, hxi, hyi, (hx y hy).2.1]
  have hj : ∀ y ∈ xs, c*y o+d*y j = if y j = x j then 1 else 0 := by
    intro y hy
    rcases (hx x hxx).2.2 j with hxj | hxj <;>
      rcases (hx y hy).2.2 j with hyj | hyj <;>
      simp [c, d, hxj, hyj, (hx y hy).2.1]
  have hsum : (∑ y ∈ xs, e y * (a*y o+b*y i) * (c*y o+d*y j)) = e x := by
    rw [Finset.sum_eq_single x]
    · rw [hi x hxx, hj x hxx]; simp
    · intro y hy hyx
      rw [hi y hy, hj y hy]
      by_cases hyi : y i = x i <;> by_cases hyj : y j = x j <;> simp [hyi, hyj]
      exact (hyx (hsep y hy hyi hyj)).elim
    · exact fun hn => (hn hxx).elim
  rw [← hsum]
  exact square_sum_pair xs e he o i j a b c d

lemma transport_squares {R : Type*} [Fintype R]
    (xs : Finset (I → k)) (e : (I → k) → k) (u : (I → k) → R → k)
    (B : R → I → k)
    (hu : ∀ r s, ∑ x ∈ xs, e x * u x r * u x s = 0)
    (hx : ∀ x ∈ xs, ∀ i, x i = ∑ r, u x r * B r i) :
    ∀ i j, ∑ x ∈ xs, e x * x i * x j = 0 := by
  intro i j
  calc
    _ = ∑ x ∈ xs, ∑ r, ∑ s, (B r i * B s j) * (e x * u x r * u x s) := by
      apply Finset.sum_congr rfl
      intro x hxx
      rw [hx x hxx i, hx x hxx j]
      conv_lhs => lhs; rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ r, ∑ s, ∑ x ∈ xs, (B r i * B s j) * (e x * u x r * u x s) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ s, (B r i * B s j) * (∑ x ∈ xs, e x * u x r * u x s) := by
      simp only [Finset.mul_sum]
    _ = 0 := by simp only [hu, mul_zero, Finset.sum_const_zero]

end Praxis.Proofs.Classification.GateGeometry
