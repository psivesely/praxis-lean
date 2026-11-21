import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.NormNum

namespace Praxis.Algebra.Short

open scoped BigOperators

def castVector {N : ℕ} (p : ℕ) (w : Fin N → ℤ) : Fin N → ZMod p :=
  fun i => (w i : ZMod p)

def VerifiedMultiple {N : ℕ} (p B : ℕ) (z : Fin N → ZMod p)
    (w : Fin N → ℤ) : Prop :=
  castVector p w ≠ 0 ∧
    (∃ a : ZMod p, a ≠ 0 ∧ ∀ i, (w i : ZMod p) = a * z i) ∧
      (∀ i, |w i| ≤ (B : ℤ))

instance {N p B : ℕ} [NeZero p] (z : Fin N → ZMod p) (w : Fin N → ℤ) :
    Decidable (VerifiedMultiple p B z w) :=
  inferInstanceAs (Decidable (castVector p w ≠ 0 ∧
    (∃ a : ZMod p, a ≠ 0 ∧ ∀ i, (w i : ZMod p) = a * z i) ∧
      (∀ i, |w i| ≤ (B : ℤ))))

def ShortMultiple {N : ℕ} (p B : ℕ) (z : Fin N → ZMod p) : Prop :=
  ∃ w, VerifiedMultiple p B z w

def boxList : (N B : ℕ) → List (Fin N → ℤ)
  | 0, _ => [fun i => Fin.elim0 i]
  | N + 1, B => (List.range (2 * B + 1)).flatMap fun (x : ℕ) =>
      (boxList N B).map fun v => Fin.cons ((x : ℤ) - B) v

def bruteForce {N : ℕ} (p B : ℕ) [NeZero p] (z : Fin N → ZMod p) :
    Option (Fin N → ℤ) :=
  (boxList N B).find? (fun w => decide (VerifiedMultiple p B z w))

theorem mem_boxList {N B : ℕ} (w : Fin N → ℤ) :
    w ∈ boxList N B ↔ ∀ i, |w i| ≤ (B : ℤ) := by
  induction N with
  | zero => simp [boxList, Subsingleton.elim w (fun i => Fin.elim0 i)]
  | succ N ih =>
    simp only [boxList, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨x, hx, v, hv, rfl⟩
      have hb := ih v |>.mp hv
      rw [Fin.forall_fin_succ]
      constructor
      · simp only [Fin.cons_zero, abs_le]
        constructor <;> omega
      · intro i
        simpa only [Fin.cons_succ] using hb i
    · intro hw
      have h0 := hw 0
      rw [abs_le] at h0
      have hx : (w 0 + B).toNat < 2 * B + 1 := by omega
      have he : ((w 0 + B).toNat : ℤ) - B = w 0 := by omega
      refine ⟨(w 0 + B).toNat, hx, Fin.tail w,
        (ih (Fin.tail w)).mpr (fun i => hw i.succ), ?_⟩
      rw [he]
      exact Fin.cons_self_tail w

theorem bruteForce_none_iff {N p B : ℕ} [NeZero p] (z : Fin N → ZMod p) :
    bruteForce p B z = none ↔ ¬ ShortMultiple p B z := by
  unfold bruteForce
  simp only [List.find?_eq_none, Bool.not_eq_true, decide_eq_false_iff_not]
  constructor
  · intro h ⟨w, hw⟩
    exact h w ((mem_boxList w).mpr hw.2.2) hw
  · intro h w _ hw
    exact h ⟨w, hw⟩

set_option maxRecDepth 10000

end Praxis.Algebra.Short
