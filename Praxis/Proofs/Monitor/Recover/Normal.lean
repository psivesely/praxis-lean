import Praxis.Proofs.Monitor.Recover.Nuisance
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Recover.Boundary
import Praxis.Proofs.Monitor.Recover.Collect
import Praxis.Proofs.Monitor.Recover.Identity
import Praxis.Proofs.Monitor.Recover.Quadratic
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open Praxis.Proofs.View Praxis.Proofs.View.SZ

noncomputable section

attribute [local irreducible] keys1 keys2

lemma gradient_left (pp : PublicParams P0) (D : ExprT P0) (ω : Assign P0)
    (σ : Sector) (l : Leg P0) (j : I) (hV : ∀ cl, vc D σ cl = 0) :
    ((keys1 P0).map fun a => e1At pp ω a *
      (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l)))).sum =
      (∑ k : Fin P0.K1, piAt ω.coins k.val * ∑ i : I,
        exprStack D σ (k,l) i j * ω.coins.1 i) + nuisance D ω.coins σ l j := by
  rw [expand_left_sum D σ l j _
    (by intro k; simp only [e1At, g1Exp]) (by intro k; simp only [e1At, g1Exp])]
  rw [keys1_sum]
  have hL2 (k : Fin P0.K1) (i : I) : bc D σ l j (some (.L2 k i)) = 0 := by
    exact congrFun (congrFun (hV (k,l)) i) j
  have hL1 (k : Fin P0.K1) (i : I) :
      bc D σ l j (some (.L1 k i)) = exprStack D σ (k,l) i j := bc_W D σ (k,l) i j
  simp only [e1At, g1Exp, hL2, hL1, bc_totL1, bc_totL2, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, nuisance, Finset.mul_sum]
  have hW : (∑ k : Fin P0.K1, ∑ i : I,
      (piAt ω.coins k.val * ω.coins.1 i) * exprStack D σ (k,l) i j) =
      ∑ k : Fin P0.K1, ∑ i : I,
        piAt ω.coins k.val * (exprStack D σ (k,l) i j * ω.coins.1 i) := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hW]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

lemma normal_collect (D : ExprT P0) (ω : Assign P0) (σ : Sector) (j : I) :
    (∑ l : Leg P0, sectorScale ω.coins σ * legScale ω.coins l *
      (∑ k : Fin P0.K1, piAt ω.coins k.val * ∑ i : I,
        exprStack D σ (k,l) i j * ω.coins.1 i)) =
      (sectorScale ω.coins σ • ∑ cl : Cell P0, gamma ω.coins cl •
        ((exprStack D σ cl).transpose.mulVec ω.coins.1)) j := by
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.mul_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  simp only [gamma]
  ring

theorem recovery_normal (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Vec F P0.N) (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : IdentityAtR pp v r D ι) (ω : Assign P0) (hc : ValidCoins pp.qap ω.coins)
    (σ : Sector) : rGrad pp ω D σ = sectorScale ω.coins σ •
      ∑ cl : Cell P0, gamma ω.coins cl • ((exprStack D σ cl).transpose.mulVec ω.coins.1) := by
  have hp := recovery_polynomial_zero pp S hD v r D ι h
  have hV := vc_zero pp S hD v r D ι hp σ
  ext j
  unfold rGrad
  rw [View.legList_sum]
  simp only [gradient_left pp D ω σ _ _ hV,
    nuisance_zero pp S hD v r D ι hp ω.coins hc σ, add_zero]
  exact normal_collect D ω σ j

end

end Praxis.Proofs.Monitor
