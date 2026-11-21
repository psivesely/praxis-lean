import Praxis.Constants
import Mathlib.Tactic.NormNum

namespace Praxis.Bounds.Degree

theorem degree_bound :
    Praxis.Constants.view_degree_d1 + Praxis.Constants.view_degree_d2 =
      Praxis.Constants.view_degree_total ∧
    Praxis.Constants.view_degree_total ≤ Praxis.Constants.d_star := by
  norm_num [Praxis.Constants.view_degree_d1, Praxis.Constants.view_degree_d2,
    Praxis.Constants.view_degree_total, Praxis.Constants.d_star]

end Praxis.Bounds.Degree
