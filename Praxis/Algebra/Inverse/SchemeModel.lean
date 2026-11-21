import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.Definitions.Sampler
import Praxis.Algebra.Probability.FiniteLaw

set_option autoImplicit false

namespace Praxis.Algebra

open scoped BigOperators

theorem productMass_eq_vitMass {p N : ℕ} (G : Fin N → ℕ) (z : Fin N → ZMod p) :
    productMass G z = Inverse.Definitions.mass G (Inverse.Definitions.scalar G z) := by
  classical
  let c : ZMod p := ∑ i, z i * 2
  have he (k : Inverse.Definitions.Grid G) :
      (∑ i, z i * (((2 + ((k i).val : ℤ)) : ℤ) : ZMod p)) =
        Inverse.Definitions.scalar G z k + c := by
    simp only [Int.cast_add, Int.cast_ofNat, Int.cast_natCast, mul_add,
      Finset.sum_add_distrib, Inverse.Definitions.scalar, c]
    exact add_comm _ _
  have ha (t : ZMod p) :
      atom (fun k : Inverse.Definitions.Grid G =>
        ∑ i, z i * (((2 + ((k i).val : ℤ)) : ℤ) : ZMod p)) t =
      Inverse.Definitions.atom G (Inverse.Definitions.scalar G z) (t - c) := by
    rw [atom_eq_count]
    unfold Inverse.Definitions.atom FiniteProbability.pointProb FiniteProbability.fibreCount
    congr 3
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact eq_sub_iff_add_eq.symm
  unfold productMass maxAtom Inverse.Definitions.mass FiniteProbability.atomMass
  simp_rw [ha]
  exact (Equiv.subRight c).iSup_congr (fun _ => rfl)

end Praxis.Algebra
