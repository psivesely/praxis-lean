import Praxis.Proofs.Basic
import Praxis.Ledger

namespace Praxis.Proofs.Ledger

theorem ledger_split (w : ℕ) :
    ledgerE w = ledgerInit + ledgerCmp w + ledgerName + ledgerRec w := by
  unfold ledgerE ledgerInit ledgerCmp ledgerName ledgerRec
  ring

end Praxis.Proofs.Ledger
