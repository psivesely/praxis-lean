import Praxis.Proofs.Injectivity.Book
import Praxis.Proofs.Injectivity.Sampling
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Proofs.Basic
import Praxis.Relation
import Praxis.Units

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec

theorem jse_law (S : Relation P0) (pub : PubView P0) (tr : List (TrOp P0)) :
    evalSPMF (runUnits (extractorC (sparseOf S) pub tr)) = evalSPMF (extractorRef S pub tr) := by
  exact extractor_law S pub tr

end Praxis.Proofs.Injectivity
