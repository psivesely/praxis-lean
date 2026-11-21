import Praxis.Algebra.Trans.Definitions
import Praxis.Combinatorics.Mass
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

noncomputable section

open Praxis.Algebra.Point Praxis.Algebra.Inverse.Definitions

namespace Praxis.Algebra.Trans

namespace TransitionInput

theorem grid_card_split {n r q : ℕ} (T : TransitionInput n r q) :
    Fintype.card (Grid T.grids) =
      Fintype.card (Grid T.oldGrids) * T.grids (Fin.last n) := by
  simp only [Grid, Combinatorics.Mass.Grid, Fintype.card_pi, Fintype.card_fin]
  exact Fin.prod_univ_castSucc T.grids

end TransitionInput

end Praxis.Algebra.Trans
