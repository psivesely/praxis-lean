import Praxis.Proofs.View.ForwardCoins
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Proofs.View.ForwardSeparation
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open Polynomial

def tagProject {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) : ExprT P :=
  project .omega 2 (project .zeta4 2 (project .zeta' 2 (project .zeta 2 (project .pi 3 D))))

def mainProject {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector) : ExprT P :=
  project .alpha (if σ = .plain then 2 else 3) (tagProject (expandTot D))

lemma tagProject_identity (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0) (h : IdentityAtR pp v r D ι) :
    IdentityAtR pp v r (tagProject D) ι := by
  have hp := project_identity .pi (by decide) pp v r D ι h 3
  have hz := project_identity .zeta (by decide) pp v r _ ι hp 2
  have hz' := project_identity .zeta' (by decide) pp v r _ ι hz 2
  have hz4 := project_identity .zeta4 (by decide) pp v r _ ι hz' 2
  exact project_identity .omega (by decide) pp v r _ ι hz4 2

lemma mainProject_identity (pp : PublicParams P0) (v : Fin P0.n → Vec (Fq P0) P0.N)
    (r : Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0) (h : IdentityAtR pp v r D ι)
    (σ : Sector) : IdentityAtR pp v r (mainProject D σ) (if σ = .plain then ι else 0) := by
  have hE : IdentityAtR pp v r (expandTot D) ι := by
    intro c hc
    rw [valT_expandTot]
    exact h c hc
  have hm := tagProject_identity pp v r _ ι hE
  cases σ <;> exact project_identity .alpha (by decide) pp v r _ ι hm _

def classCoeff {P : Params} (E : ExprT P) (σ : Sector)
    (a : Option (G1Idx P)) (b : Option (G2Idx P)) : Fq P :=
  match a, b with
  | some (.L1 _ _), none => if σ = .plain then E.1 (a,b) else 0
  | some (.L1 _ _), some (.ZeroCoordinate σ' _ _) | some (.L1 _ _), some (.SC σ' _) |
      some (.L2 _ _), some (.R2 σ' _ _) | some (.QP _), some (.QB σ' _ _) |
      some (.RP _), some (.RB σ' _ _) | some (.GY _), some (.GB σ' _ _) |
      some (.GY _), some (.GM σ' _ _) => if σ' = σ then E.1 (a,b) else 0
  | _, _ => 0

def classExpr {P : Params} (E : ExprT P) (σ : Sector) : ExprT P :=
  (fun ab => classCoeff E σ ab.1 ab.2, if σ = .alpha then E.2 else 0)

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_none {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
     (b : Option (G2Idx P)) :
    (mainProject D σ).1 (none, b) = classCoeff (expandTot D) σ (none) b := by
  cases b <;> casesm* G2Idx _, Sector <;> rfl

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_L1 {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
    (k : Fin P.K1) (i : Fin (P.N+1)) (b : Option (G2Idx P)) :
    (mainProject D σ).1 (some (.L1 k i), b) = classCoeff (expandTot D) σ (some (.L1 k i)) b := by
  cases b <;> casesm* G2Idx _, Sector <;> rfl

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_L2 {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
    (k : Fin P.K1) (i : Fin (P.N+1)) (b : Option (G2Idx P)) :
    (mainProject D σ).1 (some (.L2 k i), b) = classCoeff (expandTot D) σ (some (.L2 k i)) b := by
  cases b <;> casesm* G2Idx _, Sector <;> rfl

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_totL1 {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
    (k : Fin P.K1) (b : Option (G2Idx P)) :
    (mainProject D σ).1 (some (.totL1 k), b) = classCoeff (expandTot D) σ (some (.totL1 k)) b := by
  cases b <;> casesm* G2Idx _, Sector <;>
    first | rfl | simp only [mainProject, tagProject, project, restrictW, ViewScale.weight1,
      ViewScale.weight2, ViewScale.weightT, g2Sector, classCoeff, expandTot, expand1,
      expand1C, expand2, expand2C, ite_true, ite_false, add_zero, zero_add, ite_self]

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_totL2 {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
    (k : Fin P.K1) (b : Option (G2Idx P)) :
    (mainProject D σ).1 (some (.totL2 k), b) = classCoeff (expandTot D) σ (some (.totL2 k)) b := by
  cases b <;> casesm* G2Idx _, Sector <;>
    first | rfl | simp only [mainProject, tagProject, project, restrictW, ViewScale.weight1,
      ViewScale.weight2, ViewScale.weightT, g2Sector, classCoeff, expandTot, expand1,
      expand1C, expand2, expand2C, ite_true, ite_false, add_zero, zero_add, ite_self]

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_QP {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
    (a : Fin P.E1) (b : Option (G2Idx P)) :
    (mainProject D σ).1 (some (.QP a), b) = classCoeff (expandTot D) σ (some (.QP a)) b := by
  cases b <;> casesm* G2Idx _, Sector <;> rfl

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_RP {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
    (a : RemExp P) (b : Option (G2Idx P)) :
    (mainProject D σ).1 (some (.RP a), b) = classCoeff (expandTot D) σ (some (.RP a)) b := by
  cases b <;> casesm* G2Idx _, Sector <;> rfl

set_option maxHeartbeats 1000000 in
lemma mainProject_coeff_GY {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector)
    (i : Fin (P.N+1)) (b : Option (G2Idx P)) :
    (mainProject D σ).1 (some (.GY i), b) = classCoeff (expandTot D) σ (some (.GY i)) b := by
  cases b <;> casesm* G2Idx _, Sector <;> rfl

lemma mainProject_eq_classExpr {P : Params} [Fact (Nat.Prime P.q)] (D : ExprT P) (σ : Sector) :
    mainProject D σ = classExpr (expandTot D) σ := by
  apply Prod.ext
  · funext ab
    rcases ab with ⟨a,b⟩
    cases a with
    | none => exact mainProject_coeff_none D σ b
    | some a =>
      cases a with
      | L1 k i => exact mainProject_coeff_L1 D σ k i b
      | L2 k i => exact mainProject_coeff_L2 D σ k i b
      | totL1 k => exact mainProject_coeff_totL1 D σ k b
      | totL2 k => exact mainProject_coeff_totL2 D σ k b
      | QP a => exact mainProject_coeff_QP D σ a b
      | RP a => exact mainProject_coeff_RP D σ a b
      | GY i => exact mainProject_coeff_GY D σ i b
  · cases σ <;> rfl

section Coefficients

variable {P : Params}

def aC (E : ExprT P) (σ : Sector) (cl : Cell P) (i j : Fin (P.N + 1)) : Fq P :=
  E.1 (some (.L1 cl.1 i), some (.ZeroCoordinate σ cl.2 j))

def dC (E : ExprT P) (σ : Sector) (cl : Cell P) (i j : Fin (P.N + 1)) : Fq P :=
  E.1 (some (.L2 cl.1 i), some (.R2 σ cl.2 j))

def sC (E : ExprT P) (σ : Sector) (cl : Cell P) (i : Fin (P.N + 1)) : Fq P :=
  E.1 (some (.L1 cl.1 i), some (.SC σ cl.2))

def lC (E : ExprT P) (σ : Sector) (k : Fin P.K1) (i : Fin (P.N + 1)) : Fq P :=
  if σ = .plain then E.1 (some (.L1 k i), none) else 0

noncomputable def hC (E : ExprT P) (σ : Sector) (cl : Cell P) : Polynomial (Fq P) :=
  ∑ a : Fin P.E1, ∑ j : Fin P.Mq,
    monomial (a.val + P.E1 * j.val) (E.1 (some (.QP a), some (.QB σ cl j)))

noncomputable def RC (E : ExprT P) (σ : Sector) (cl : Cell P) : Polynomial (Fq P) :=
  ∑ a : RemExp P, ∑ j : Fin P.Wr,
    monomial (a.1.val + P.U * P.E1p * j.val) (E.1 (some (.RP a), some (.RB σ cl j)))

def gbC (E : ExprT P) (σ : Sector) (i : Fin (P.N + 1)) (g : CrossIdx)
    (e : Fin (2 * P.n - 1)) : Fq P := E.1 (some (.GY i), some (.GB σ g e))

def gmC (E : ExprT P) (σ : Sector) (i : Fin (P.N + 1)) (s : TieIdx)
    (e : Fin (P.n - 1)) : Fq P := E.1 (some (.GY i), some (.GM σ s e))

lemma aC_expandTot (D : ExprT P) (σ : Sector) : aC (expandTot D) σ = exprStack D σ := by
  ext cl i j
  simp only [aC, exprStack, expandTot, expand2, expand2C, expand1, expand1C]
  ring

lemma sC_expandTot (D : ExprT P) (σ : Sector) (cl : Cell P) :
    sC (expandTot D) σ cl = -exprSC D σ cl := by
  ext i
  simp [sC, exprSC, expandTot, expand2, expand2C, expand1, expand1C]

end Coefficients

end Praxis.Proofs.View
