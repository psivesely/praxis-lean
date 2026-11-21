import Praxis.Proofs.Basic
import Praxis.Bounds.Degree
import Praxis.Constants

namespace Praxis.Proofs.Degree

open Praxis.Constants

theorem degree_bound :
    view_degree_d1 + view_degree_d2 = view_degree_total ∧ view_degree_total ≤ d_star :=
  Praxis.Bounds.Degree.degree_bound

theorem degree_le_eps :
    (view_degree_total : ℝ) / ((q : ℝ) - D) ≤ (eps_f : ℝ) ∧
      (d_star : ℝ) / ((q : ℝ) - D) ≤ (eps_f : ℝ) := by
  norm_num [view_degree_total, d_star, q, D, eps_f]

end Praxis.Proofs.Degree
