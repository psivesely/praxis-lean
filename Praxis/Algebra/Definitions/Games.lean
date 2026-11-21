import Praxis.Encryption.GroupModel
import Praxis.Encryption.BN254
import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Totient
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Algebra

open OracleComp OracleSpec GroupModel.Sorted

noncomputable def decodeLabel {p n : ℕ} (σ : ZMod p ↪ BitVec n) (l : BitVec n) :
    Option (ZMod p) := by
  classical
  exact if h : ∃ x, σ x = l then some h.choose else none

theorem ofNat_val_injective {p n : ℕ} [NeZero p] (h : p ≤ 2 ^ n) :
    Function.Injective fun x : ZMod p => BitVec.ofNat n x.val := by
  intro a b hab
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have e := congrArg BitVec.toNat hab
  simp only [BitVec.toNat_ofNat] at e
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
  exact ZMod.val_injective p e

end Praxis.Algebra
