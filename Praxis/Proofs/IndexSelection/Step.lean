import Praxis.Proofs.IndexSelection.Step.Bounds
import Praxis.Constants
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Relation
import Praxis.Units

namespace Praxis.Proofs.IndexSelection

theorem jset_step (P : Params) (hP : P = P0) (S : Relation P) (hS : InShape P S)
    (st : ExState P) (op : TrOp P) :
    WithinUnits (exStepC (sparseOf S) st op)
      (Constants.running_time_extractor_per_operation + 1 +
        2 * 2 * (Constants.running_time_extractor_per_sector_test +
          Constants.running_time_extractor_per_sector_test_per_S * size S)) := by
  exact step_bound P hP S hS st op

end Praxis.Proofs.IndexSelection
