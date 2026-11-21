import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Constants
import Praxis.Games
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Catalog

def candidateOffset (n : ℕ) : ℕ := n * (Constants.L + 2) + 3 * n.choose 2

lemma candidateOffset_succ (n : ℕ) :
    candidateOffset (n+1) = candidateOffset n + (Constants.L + 3*n + 2) := by
  simp only [candidateOffset, Nat.choose_succ_succ, Nat.choose_one_right]
  ring

lemma candidateOffset_mono {n m : ℕ} (h : n ≤ m) : candidateOffset n ≤ candidateOffset m := by
  exact Nat.add_le_add (Nat.mul_le_mul_right _ h)
    (Nat.mul_le_mul_left _ (Nat.choose_le_choose 2 h))

private lemma choose_two_identity (n : ℕ) : 2 * n.choose 2 + n = n*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

lemma candidate_quota (Q : ℕ) (i : Kind)
    (hi : i = .light ∨ i = .field ∨ i = .guess) :
    candidateOffset Q + 2 * (Constants.L + 3*Q) < quota (simBudget Q) i := by
  have hchoose := choose_two_identity Q
  have hL : 4 ≤ Constants.L := by norm_num [Constants.L]
  have hoff : 2 * candidateOffset Q + 3*Q =
      2*Q*(Constants.L+2) + 3*Q*Q := by
    dsimp [candidateOffset]
    nlinarith
  have hdiv : (simBudget Q * (simBudget Q + 1)) / 2 = (Q+1)*(2*Q+3) := by
    have he : simBudget Q * (simBudget Q + 1) = 2 * ((Q+1)*(2*Q+3)) := by
      simp only [simBudget, Constants.LT]
      ring
    rw [he, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rcases hi with rfl | rfl | rfl
  · change _ < simBudget Q * Constants.L + (simBudget Q * (simBudget Q + 1)) / 2
    rw [hdiv]
    simp only [simBudget, Constants.LT]
    nlinarith [Nat.mul_le_mul_left Q hL]
  · change _ < simBudget Q * Constants.L + (simBudget Q * (simBudget Q + 1)) / 2
    rw [hdiv]
    simp only [simBudget, Constants.LT]
    nlinarith [Nat.mul_le_mul_left Q hL]
  · have hc := choose_two_identity (Constants.L + 3*simBudget Q)
    simp only [quota, simBudget, Constants.LT] at hc ⊢
    nlinarith [Nat.mul_self_le_mul_self hL]

lemma candidate_row_lt (Q n j : ℕ) (hn : n < Q)
    (hj : j < Constants.L + 3*n + 2) :
    candidateOffset n + j < candidateOffset Q := by
  have hm := candidateOffset_mono (Nat.succ_le_of_lt hn)
  rw [candidateOffset_succ] at hm
  omega

inductive CandidateSlot (Q : ℕ)
  | operation (n : Fin Q) (j : Fin (Constants.L + 3*n.val + 2))
  | key (j : Fin (Constants.L + 3*Q)) (sign : Fin 2)

namespace CandidateSlot

def encode {Q : ℕ} : CandidateSlot Q → ℕ
  | .operation n j => candidateOffset n.val + j.val
  | .key j sign => candidateOffset Q + 2*j.val + sign.val

lemma encode_lt {Q : ℕ} (a : CandidateSlot Q) (i : Kind)
    (hi : i = .light ∨ i = .field ∨ i = .guess) : a.encode < quota (simBudget Q) i := by
  have hq := candidate_quota Q i hi
  cases a with
  | operation n j =>
    have h := candidate_row_lt Q n.val j.val n.isLt j.isLt
    simp only [encode]
    omega
  | key j sign =>
    have hj := j.isLt
    have hs := sign.isLt
    simp only [encode]
    omega

lemma encode_injective (Q : ℕ) : Function.Injective (encode (Q := Q)) := by
  intro a b he
  cases a with
  | operation n j =>
    cases b with
    | operation m k =>
      have hj := j.isLt
      have hk := k.isLt
      have hnm : n = m := by
        apply Fin.ext
        by_contra hn
        rcases lt_or_gt_of_ne hn with h | h
        · have hrow := candidate_row_lt m.val n.val j.val h hj
          simp only [encode] at he
          omega
        · have hrow := candidate_row_lt n.val m.val k.val h hk
          simp only [encode] at he
          omega
      subst m
      have hjk : j = k := Fin.ext (Nat.add_left_cancel he)
      subst k
      rfl
    | key k sign =>
      have hrow := candidate_row_lt Q n.val j.val n.isLt j.isLt
      simp only [encode] at he
      omega
  | key j sign =>
    cases b with
    | operation n k =>
      have hrow := candidate_row_lt Q n.val k.val n.isLt k.isLt
      simp only [encode] at he
      omega
    | key k sign' =>
      have hs := sign.isLt
      have hs' := sign'.isLt
      simp only [encode] at he
      have hjk : j = k := Fin.ext (by omega)
      have hss : sign = sign' := Fin.ext (by omega)
      subst k
      subst sign'
      rfl

def embedding (Q : ℕ) (i : Kind) (hi : i = .light ∨ i = .field ∨ i = .guess) :
    CandidateSlot Q ↪ Fin (quota (simBudget Q) i) where
  toFun a := ⟨a.encode, a.encode_lt i hi⟩
  inj' _ _ h := encode_injective Q (Fin.val_eq_of_eq h)

end CandidateSlot

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Catalog
