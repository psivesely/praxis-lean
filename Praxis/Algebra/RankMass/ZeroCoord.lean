import Praxis.Algebra.Stmt.RankMass
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler

set_option autoImplicit false

namespace Praxis.Algebra.RankMass

open Finset

open scoped BigOperators

theorem atom_prod_snd {A B Y : Type*} [Fintype A] [Nonempty A] [Fintype B]
    (f : B → Y) (y : Y) : atom (fun x : A × B => f x.2) y = atom f y := by
  classical
  rw [atom_eq_count, atom_eq_count, Fintype.card_prod,
    ← Finset.univ_product_univ, Finset.filter_product_right (fun b => f b = y),
    Finset.card_product,
    Finset.card_univ, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast Fintype.card_ne_zero (α := A))

theorem dot_centeredF_of_zero {p N g : ℕ} {G : Fin N → ℕ}
    (z : Vec (ZMod p) N) (hz : z 0 = 0) (w : GridSample g G) :
    dot z (centeredF w) = tailForm G (fun i => z i.succ) w.2 := by
  simp [dot, Fin.sum_univ_succ, hz, centeredF, centeredZ, tailForm]

theorem atom_tailForm_of_zero {p N g : ℕ} {G : Fin N → ℕ} (hg : 0 < g)
    (z : Vec (ZMod p) N) (hz : z 0 = 0) (t : ZMod p) :
    atom (fun w : GridSample g G => dot z (centeredF w)) t =
      atom (tailForm G (fun i => z i.succ)) t := by
  have : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  simp_rw [dot_centeredF_of_zero z hz]
  exact atom_prod_snd _ _

theorem scalarMass_eq_productMass_of_zero {p N g : ℕ} {G : Fin N → ℕ} (hg : 0 < g)
    (z : Vec (ZMod p) N) (hz : z 0 = 0) :
    scalarMass g G z = productMass G (fun i => z i.succ) := by
  unfold scalarMass productMass maxAtom
  congr 1
  funext t
  exact atom_tailForm_of_zero hg z hz t

end Praxis.Algebra.RankMass
