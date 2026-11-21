import Praxis.Algebra.Prefix.Definitions
import Praxis.Combinatorics.Chain
import Praxis.Combinatorics.Mass
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.ChainLemma.UnequalChain
import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.InverseBranches.AdditiveChain
import Praxis.Algebra.InverseBranches.IntegerLift
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Praxis.Algebra.Prefix

open Finset Module Praxis.Combinatorics Praxis.Combinatorics.UnequalChain

open Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Prefix.Definitions Praxis.Algebra.VectorInverse

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mass_le_of_fibBd {d : ℕ} {G : ι → ℕ} {B : Matrix ι (Fin d) ℤ}
    {ρ : ℝ} (hG : ∀ i, 0 < G i)
    (hb : FibBd G (fun i => B i) univ ρ) : mass G (imageZ G B) ≤ ρ := by
  classical
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  let k₀ : Grid G := fun i => ⟨0, hG i⟩
  have he : (fun r : Grid G => ∑ i, B i * ((r i : ℕ) : Fin d → ℤ)) =
      imageZ G B := by
    funext r j
    simp [imageZ, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
  have hc : Algebra.FiniteProbability.fibreCount (imageZ G B) t =
      #(fib G (fun i => B i) univ k₀ t) := by
    rw [fib_univ]
    unfold Algebra.FiniteProbability.fibreCount
    simp only [← he]
  have hd : (Fintype.card (Grid G) : ℝ) = ∏ i, (G i : ℝ) := by
    simp [Grid, Combinatorics.Mass.Grid, Fintype.card_pi, Nat.cast_prod]
  have hdpos : 0 < ∏ i, (G i : ℝ) :=
    prod_pos fun i _ => by exact_mod_cast hG i
  rw [Algebra.FiniteProbability.pointProb, hc, hd, div_le_iff₀ hdpos]
  simpa only [mul_comm] using hb k₀ t

theorem primitive_rows {d : ℕ} (L : IntLat ι d) : PrimitiveRows L.matrix :=
  primitive_of_saturated_basis L.carrier L.saturated L.basis

theorem integer_mass_pivot {d : ℕ} (L : IntLat ι d) (G : ι → ℕ) (g : ℕ) :
    IntegerMassPivot L G g := by
  intro _ _ hg hG
  obtain ⟨r, hdet, _⟩ := exists_maximal_basis_minor L.carrier L.saturated L.basis
  have hGp : ∀ i, 0 < G i := fun i => lt_of_lt_of_le hg (hG i)
  have hb := (pivot_fibBd G L.matrix r hGp hdet).extend (subset_univ _)
  apply (mass_le_of_fibBd hGp hb).trans
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (g : ℝ)^d = ∏ _ : Fin d, (g : ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => by positivity)
      (fun i _ => by exact_mod_cast hG (r i))

theorem integer_mass_height {d : ℕ} (L : IntLat ι d) (G : ι → ℕ) (g : ℕ) :
    IntegerMassHeight L G g := by
  intro _ _ hg hgcap hG
  obtain ⟨r, hdet, hmax⟩ := exists_maximal_basis_minor L.carrier L.saturated L.basis
  have hp : L.H = (L.matrix.submatrix r id).det.natAbs :=
    largestMinor_eq_pivot L.matrix r hmax
  have hb := integer_fibBd_additive (by omega : 0 < g) hG
    (Nat.le_of_lt hgcap) (primitive_rows L) r hdet
  have hm := mass_le_of_fibBd (fun i => lt_of_lt_of_le (by omega : 0 < g) (hG i)) hb
  simpa only [IntLat.mZ, hp, correction] using hm

theorem height_pos {d : ℕ} (L : IntLat ι d) : 0 < L.H := by
  obtain ⟨r, hdet, hmax⟩ := exists_maximal_basis_minor L.carrier L.saturated L.basis
  change 0 < largestMinor L.matrix
  rw [largestMinor_eq_pivot L.matrix r hmax]
  exact Int.natAbs_pos.mpr hdet

end Praxis.Algebra.Prefix
