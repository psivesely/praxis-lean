import Praxis.Algebra.RankMass.Pivot
import Praxis.Algebra.Stmt.RankMass

set_option autoImplicit false

namespace Praxis.Algebra.RankMass

theorem rank_ge_four_light_holds : rank_ge_four_light := by
  intro p _ N d rows g G hg hG hgp W hr
  apply (centered_rank_bound_holds p N d rows g G hg hG hgp W).trans
  apply one_div_le_one_div_of_le
  · exact pow_pos (by exact_mod_cast hg) 4
  · exact_mod_cast Nat.pow_le_pow_right hg hr

end Praxis.Algebra.RankMass
