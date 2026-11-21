import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.Append
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.BilinearMap

open OracleComp OracleSpec

namespace GroupModel.Sorted

inductive PSort
  | g₁ | g₂ | gₜ
  deriving DecidableEq

end GroupModel.Sorted
