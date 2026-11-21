import Praxis.Proofs.Basic
import Praxis.Constants

namespace Praxis.Proofs.MonitorBounds

open Praxis.Constants

theorem monfit (w : ℕ) :
    2 * eps_f + extractor_recovery_failure_per_sector ≤ ledgerRec w := by
  have he : 0 ≤ eps_f := by norm_num [eps_f]
  have hfail : extractor_recovery_failure_per_sector ≤ 6 * eps_f := by
    norm_num [extractor_recovery_failure_per_sector, eps_f]
  have hw : (0 : ℚ) ≤ w := Nat.cast_nonneg w
  unfold ledgerRec
  nlinarith

end Praxis.Proofs.MonitorBounds
