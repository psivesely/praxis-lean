import Praxis.Proofs.Monitor.Recover.Boundary
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open Praxis.Proofs.View Praxis.Proofs.View.SZ

noncomputable section

def bc (D : ExprT P0) (σ : Sector) (l : Leg P0) (j : I)
    (a : Option (G1Idx P0)) : F :=
  expand1C (fun a => D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l))) a

lemma bc_totL1 (D : ExprT P0) (σ : Sector) (l : Leg P0) (j : I) (k : Fin P0.K1) :
    bc D σ l j (some (.totL1 k)) = 0 := rfl

lemma bc_totL2 (D : ExprT P0) (σ : Sector) (l : Leg P0) (j : I) (k : Fin P0.K1) :
    bc D σ l j (some (.totL2 k)) = 0 := rfl

lemma bc_W (D : ExprT P0) (σ : Sector) (cl : Cell P0) (i j : I) :
    bc D σ cl.2 j (some (.L1 cl.1 i)) = exprStack D σ cl i j := by
  simp only [bc, expand1C, exprStack]
  ring

def vc (D : ExprT P0) (σ : Sector) (cl : Cell P0) (i j : I) : F :=
  bc D σ cl.2 j (some (.L2 cl.1 i))

lemma expand_left_sum (D : ExprT P0) (σ : Sector) (l : Leg P0) (j : I)
    (f : Option (G1Idx P0) → F)
    (h1 : ∀ k, f (some (.totL1 k)) = ∑ i, f (some (.L1 k i)))
    (h2 : ∀ k, f (some (.totL2 k)) = ∑ i, f (some (.L2 k i))) :
    ((keys1 P0).map fun a => f a *
      (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l)))).sum =
    ((keys1 P0).map fun a => f a * bc D σ l j a).sum := by
  simpa only [bc, mul_comm] using (sum_expand1
    (fun a => D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l))) f h1 h2).symm

lemma list_sum_fintype {α β M : Type*} [Fintype β] [AddCommMonoid M]
    (l : List α) (f : α → β → M) :
    (l.map fun a => ∑ b, f a b).sum = ∑ b, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

lemma contraction_collect (pp : PublicParams P0) (c : Coins P0) (D : ExprT P0)
    (f : Option (G1Idx P0) → F) :
    ((keys1 P0).map fun a => f a * rightOne pp c D a).sum =
      boundaryFactor c * ∑ σ : Sector, sectorScale c σ *
        ∑ l : Leg P0, legScale c l * ∑ j : I,
          ((keys1 P0).map fun a => f a *
            (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l)))).sum *
            ((pp.qap.B j).eval (coin c .tau) - c.1 j) := by
  simp only [rightOne_eq, rightBoundary, Finset.mul_sum, list_sum_fintype]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  simp only [← List.sum_map_mul_left, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  ring

lemma slope_collect (D : ExprT P0) (c : Coins P0) (σ : Sector) (l : Leg P0) (j : I) :
    ((keys1 P0).map fun a => leftSlope c a *
      (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l)))).sum =
      ∑ k : Fin P0.K1, piAt c k.val * ∑ i : I, vc D σ (k,l) i j * c.1 i := by
  rw [expand_left_sum D σ l j _ (by intro k; simp [leftSlope])
    (by intro k; rfl), keys1_sum]
  simp only [leftSlope, bc, expand1C, vc, zero_mul, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

def nuisance (D : ExprT P0) (c : Coins P0) (σ : Sector) (l : Leg P0) (j : I) : F :=
  bc D σ l j none +
    coin c .zeta * ∑ s : Fin P0.E1, bc D σ l j (some (.QP s)) * coin c .tau ^ s.val +
    coin c .zeta' * ∑ s : RemExp P0, bc D σ l j (some (.RP s)) * coin c .tau ^ s.1.val +
    coin c .zeta4 * ∑ i : I, bc D σ l j (some (.GY i)) * c.1 i

lemma base_collect (pp : PublicParams P0) (D : ExprT P0) (c : Coins P0)
    (σ : Sector) (l : Leg P0) (j : I) :
    ((keys1 P0).map fun a => leftBase pp c a *
      (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l)))).sum =
      (∑ k : Fin P0.K1, piAt c k.val * ∑ i : I, exprStack D σ (k,l) i j * c.1 i) +
        nuisance D c σ l j := by
  rw [expand_left_sum D σ l j _ (by intro k; rfl) (by intro k; simp [leftBase]), keys1_sum]
  simp only [leftBase, bc, expand1C, zero_mul, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, nuisance, Finset.mul_sum]
  have hW : (∑ k : Fin P0.K1, ∑ i : I,
      piAt c k.val * c.1 i *
        (D.1 (some (.L1 k i), some (.ZeroCoordinate σ l j)) +
          D.1 (some (.L1 k i), some (.totR1 σ l)) +
          (D.1 (some (.totL1 k), some (.ZeroCoordinate σ l j)) +
            D.1 (some (.totL1 k), some (.totR1 σ l))))) =
      ∑ k : Fin P0.K1, ∑ i : I, piAt c k.val * (exprStack D σ (k,l) i j * c.1 i) := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    simp only [exprStack]
    ring
  rw [hW]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

end

end Praxis.Proofs.Monitor
