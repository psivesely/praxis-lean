import Praxis.Proofs.Pack.Kernel
import Praxis.Constants
import Praxis.Packing.Coefficients
import Praxis.Algebra.Definitions.Forms
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Pack

theorem pack_nonzero (w : Algebra.Vec ℤ Constants.N) (h0 : w 0 = 0) :
    Algebra.castVec (p := Constants.q) w ≠ 0 ↔ Algebra.NonzeroModP Constants.q (Praxis.Packing.packCoeffs w) :=
  Praxis.Packing.pack_nonzero w h0

end Praxis.Proofs.Pack
