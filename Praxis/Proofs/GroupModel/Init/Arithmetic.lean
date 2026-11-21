import Praxis.Proofs.Basic
import Praxis.Constants
import Praxis.Ledger

namespace Praxis.Proofs.GroupModel

theorem initial_ledger_bound :
    ((Nat.choose Constants.L1 2 : ℝ) + (Nat.choose Constants.L2 2 : ℝ) + 1) *
      (Constants.eps_f : ℝ) ≤ (ledgerInit : ℝ) := by
  norm_num [ledgerInit, choose2, Nat.choose_two_right, Constants.L1, Constants.L2,
    Constants.LT, Constants.L, Constants.eps_f]

end Praxis.Proofs.GroupModel
