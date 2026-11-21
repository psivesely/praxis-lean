import Praxis.Proofs.Monitor.Recover.Identity
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.ForwardHelpers
import Praxis.Proofs.View.SZ.Grid
import Praxis.Proofs.View.SZ.Model
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open Praxis.Proofs.View Praxis.Proofs.View.SZ

open Polynomial

noncomputable section

attribute [local irreducible] keys1 keys2

abbrev F := Fq P0

abbrev I := Fin (P0.N + 1)

def boundaryVar (c : Coins P0) : CoinVar P0 → Polynomial F
  | .inl i => C (c.1 i)
  | .inr .Om12 => X
  | .inr .Om22 => 0
  | .inr s => C (coin c s)

def boundary (c : Coins P0) : SZ.Poly →+* Polynomial F :=
  MvPolynomial.eval₂Hom C (boundaryVar c)

@[simp] lemma boundary_C (c : Coins P0) (x : F) : boundary c (MvPolynomial.C x) = C x := by simp [boundary]

@[simp] lemma boundary_xy (c : Coins P0) (i : I) : boundary c (xy i) = C (c.1 i) := by
  simp [boundary, xy, boundaryVar]

@[simp] lemma boundary_xs (c : Coins P0) (s : ScalarCoin) :
    boundary c (xs s) = boundaryVar c (.inr s) := by simp [boundary, xs]

@[simp] lemma boundary_tau (c : Coins P0) (p : Polynomial F) :
    boundary c (tauP p) = C (p.eval (coin c .tau)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [tauP, Polynomial.eval₂_add, map_add] at *; rw [hp, hq, eval_add, map_add]
  | monomial n a => simp [tauP, Polynomial.eval₂_monomial, boundaryVar, eval_monomial]

@[simp] lemma boundary_pi (c : Coins P0) (k : ℕ) :
    boundary c (piP k) = C (piAt c k) := by
  simp [piP, boundaryVar, piAt, thetaAt, map_mul, map_add, map_pow]

@[simp] lemma boundary_leg (c : Coins P0) (l : Leg P0) :
    boundary c (legP l) = C (legScale c l) := by
  rcases l with ⟨k,j⟩
  cases k <;> simp [legP, bP, boundaryVar, legScale, legScaleAt, bOf, legExp]

@[simp] lemma boundary_sector (c : Coins P0) (σ : Sector) :
    boundary c (sectorP σ) = C (sectorScale c σ) := by
  cases σ <;> simp [sectorP, sectorScale, boundaryVar]

@[simp] lemma boundary_denom (c : Coins P0) : boundary c denomP = 0 := by
  simp [denomP, boundaryVar]

def leftBase (pp : PublicParams P0) (c : Coins P0) : Option (G1Idx P0) → F
  | none => 1
  | some (.L1 k i) => piAt c k.val * c.1 i
  | some (.L2 _ _) => 0
  | some (.totL1 k) => ∑ i, piAt c k.val * c.1 i
  | some (.totL2 _) => 0
  | some (.QP s) => coin c .zeta * coin c .tau ^ s.val
  | some (.RP s) => coin c .zeta' * coin c .tau ^ s.1.val
  | some (.GY i) => coin c .zeta4 * c.1 i

def leftSlope (c : Coins P0) : Option (G1Idx P0) → F
  | some (.L2 k i) => piAt c k.val * c.1 i
  | some (.totL2 k) => ∑ i, piAt c k.val * c.1 i
  | _ => 0

lemma sum_C_X {R α : Type*} [CommRing R] [Fintype α] (f : α → R) :
    (∑ i, C (f i) * X : Polynomial R) = C (∑ i, f i) * X := by
  rw [← Finset.sum_mul, ← map_sum]

lemma sum_neg_C_X {R α : Type*} [CommRing R] [Fintype α] (f : α → R) :
    (∑ i, -C (f i) * X : Polynomial R) = -C (∑ i, f i) * X := by
  rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← map_sum]

lemma boundary_L2 (pp : PublicParams P0) (c : Coins P0) (k : Fin P0.K1) (i : I) :
    boundary c (e1P pp (some (.L2 k i))) = C (piAt c k.val * c.1 i)*X := by
  simp only [e1P, map_mul, map_add, boundary_pi, boundary_xs, boundary_xy,
    boundaryVar, zero_mul, add_zero]
  ring

lemma boundary_totL2 (pp : PublicParams P0) (c : Coins P0) (k : Fin P0.K1) :
    boundary c (e1P pp (some (.totL2 k))) = C (∑ i : I, piAt c k.val * c.1 i)*X := by
  have he : e1P pp (some (.totL2 k)) = ∑ i : I, e1P pp (some (.L2 k i)) := rfl
  rw [he, map_sum]
  simp_rw [boundary_L2]
  exact sum_C_X _

lemma boundary_L1 (pp : PublicParams P0) (c : Coins P0) (k : Fin P0.K1) (i : I) :
    boundary c (e1P pp (some (.L1 k i))) = C (piAt c k.val * c.1 i) := by
  simp only [e1P, map_mul, boundary_pi, boundary_xy]

lemma boundary_totL1 (pp : PublicParams P0) (c : Coins P0) (k : Fin P0.K1) :
    boundary c (e1P pp (some (.totL1 k))) = C (∑ i : I, piAt c k.val * c.1 i) := by
  have he : e1P pp (some (.totL1 k)) = ∑ i : I, e1P pp (some (.L1 k i)) := rfl
  rw [he, map_sum]
  simp_rw [boundary_L1]
  exact (map_sum C _ _).symm

lemma boundary_QP (pp : PublicParams P0) (c : Coins P0) (s : Fin P0.E1) :
    boundary c (e1P pp (some (.QP s))) = C (coin c .zeta * coin c .tau ^ s.val) := by
  simp only [e1P, map_mul, map_pow, boundary_xs, boundaryVar]

lemma boundary_RP (pp : PublicParams P0) (c : Coins P0) (s : RemExp P0) :
    boundary c (e1P pp (some (.RP s))) = C (coin c .zeta' * coin c .tau ^ s.1.val) := by
  simp only [e1P, map_mul, map_pow, boundary_xs, boundaryVar]

lemma boundary_GY (pp : PublicParams P0) (c : Coins P0) (i : I) :
    boundary c (e1P pp (some (.GY i))) = C (coin c .zeta4 * c.1 i) := by
  simp only [e1P, map_mul, boundary_xy, boundary_xs, boundaryVar]

lemma boundary_left (pp : PublicParams P0) (c : Coins P0) (a : Option (G1Idx P0)) :
    boundary c (e1P pp a) = C (leftBase pp c a) + C (leftSlope c a) * X := by
  cases a with
  | none => simp only [e1P, leftBase, leftSlope, map_one, map_zero, zero_mul, add_zero]
  | some a =>
    cases a with
    | L2 k i => simpa only [leftBase, leftSlope, map_zero, zero_add] using boundary_L2 pp c k i
    | totL2 k => simpa only [leftBase, leftSlope, map_zero, zero_add] using boundary_totL2 pp c k
    | L1 k i => simpa only [leftBase, leftSlope, map_zero, zero_mul, add_zero] using boundary_L1 pp c k i
    | totL1 k => simpa only [leftBase, leftSlope, map_zero, zero_mul, add_zero] using boundary_totL1 pp c k
    | QP t => simpa only [leftBase, leftSlope, map_zero, zero_mul, add_zero] using boundary_QP pp c t
    | RP t => simpa only [leftBase, leftSlope, map_zero, zero_mul, add_zero] using boundary_RP pp c t
    | GY i => simpa only [leftBase, leftSlope, map_zero, zero_mul, add_zero] using boundary_GY pp c i

def boundaryFactor (c : Coins P0) : F :=
  coin c .zeta * coin c .zeta' * coin c .zeta4 * coin c .eps

def rightBoundary (pp : PublicParams P0) (c : Coins P0) (σ : Sector)
    (l : Leg P0) (j : I) : F :=
  boundaryFactor c * sectorScale c σ * legScale c l *
    ((pp.qap.B j).eval (coin c .tau) - c.1 j)

lemma boundary_r1 (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (l : Leg P0) (j : I) :
    boundary c (r1P pp v r l j) =
      -C (boundaryFactor c * legScale c l * ((pp.qap.B j).eval (coin c .tau) - c.1 j)) * X := by
  simp [r1P, boundaryVar, boundaryFactor]
  ring

lemma boundary_r2 (pp : PublicParams P0) (c : Coins P0) (l : Leg P0) (j : I) :
    boundary c (r2P pp l j) =
      C (boundaryFactor c * legScale c l * ((pp.qap.B j).eval (coin c .tau) - c.1 j)) := by
  simp [r2P, boundaryVar, boundaryFactor]

def rightLin (pp : PublicParams P0) (c : Coins P0) : Option (G2Idx P0) → F
  | some (.ZeroCoordinate σ l j) => rightBoundary pp c σ l j
  | some (.totR1 σ l) => ∑ j, rightBoundary pp c σ l j
  | _ => 0

def rightConst (pp : PublicParams P0) (c : Coins P0) : Option (G2Idx P0) → F
  | some (.R2 σ l j) => rightBoundary pp c σ l j
  | some (.totR2 σ l) => ∑ j, rightBoundary pp c σ l j
  | _ => 0

lemma boundary_R1 (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (σ : Sector) (l : Leg P0) (j : I) :
    boundary c (e2P pp v r (some (.ZeroCoordinate σ l j))) = -C (rightBoundary pp c σ l j)*X := by
  simp only [e2P, map_mul, boundary_sector, boundary_r1, rightBoundary, map_mul]
  ring

lemma boundary_R2 (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (σ : Sector) (l : Leg P0) (j : I) :
    boundary c (e2P pp v r (some (.R2 σ l j))) = C (rightBoundary pp c σ l j) := by
  simp only [e2P, map_mul, boundary_sector, boundary_r2, rightBoundary, map_mul]
  ring

lemma boundary_totR1 (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (σ : Sector) (l : Leg P0) :
    boundary c (e2P pp v r (some (.totR1 σ l))) = -C (∑ j, rightBoundary pp c σ l j)*X := by
  have he : e2P pp v r (some (.totR1 σ l)) = ∑ j, e2P pp v r (some (.ZeroCoordinate σ l j)) := by
    simp only [e2P, Finset.mul_sum]
  rw [he, map_sum]
  simp_rw [boundary_R1]
  exact sum_neg_C_X _

lemma boundary_totR2 (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (σ : Sector) (l : Leg P0) :
    boundary c (e2P pp v r (some (.totR2 σ l))) = C (∑ j, rightBoundary pp c σ l j) := by
  have he : e2P pp v r (some (.totR2 σ l)) = ∑ j, e2P pp v r (some (.R2 σ l j)) := by
    simp only [e2P, Finset.mul_sum]
  rw [he, map_sum]
  simp only [boundary_R2, map_sum]

lemma boundary_e2 (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (b : Option (G2Idx P0)) :
    boundary c (e2P pp v r b) = C (rightConst pp c b) - C (rightLin pp c b)*X := by
  cases b with
  | none => simp [e2P, rightConst, rightLin]
  | some b =>
    cases b with
    | ZeroCoordinate σ l j => simp only [boundary_R1, rightConst, rightLin, map_zero, zero_sub, neg_mul]
    | R2 σ l j => simp only [boundary_R2, rightConst, rightLin, map_zero, zero_mul, sub_zero]
    | totR1 σ l => simp only [boundary_totR1, rightConst, rightLin, map_zero, zero_sub, neg_mul]
    | totR2 σ l => simp only [boundary_totR2, rightConst, rightLin, map_zero, zero_mul, sub_zero]
    | QB σ cl j | RB σ cl j | SC σ l | GB σ g e | GM σ g e =>
      simp only [e2P, map_mul, boundary_denom, boundary_xs, boundaryVar,
        mul_zero, zero_mul, rightConst, rightLin, map_zero, sub_zero]

lemma list_sum_neg {R α : Type*} [AddCommGroup R] (l : List α) (f : α → R) :
    (l.map fun a => -f a).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, neg_add_rev]; abel

lemma affine_coeff_two (a b c d : F) :
    ((C a + C b * X) * (C c - C d * X)).coeff 2 = -(b*d) := by
  have he : (C a + C b * X) * (C c - C d * X) =
      C (a*c) + C (b*c-a*d)*X - C (b*d)*X^2 := by simp only [map_mul, map_sub]; ring
  rw [he]
  simp only [coeff_sub, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
    ite_true, ite_false, show ¬(2 : ℕ) = 0 by decide, show ¬(2 : ℕ) = 1 by decide, show ¬(1 : ℕ) = 0 by decide, show ¬(1 : ℕ) = 2 by decide, add_zero, zero_add, zero_sub, sub_zero]

lemma affine_coeff_one (a b c d : F) :
    ((C a + C b * X) * (C c - C d * X)).coeff 1 = b*c-a*d := by
  have he : (C a + C b * X) * (C c - C d * X) =
      C (a*c) + C (b*c-a*d)*X - C (b*d)*X^2 := by simp only [map_mul, map_sub]; ring
  rw [he]
  simp only [coeff_sub, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
    ite_true, ite_false, show ¬(2 : ℕ) = 0 by decide, show ¬(2 : ℕ) = 1 by decide, show ¬(1 : ℕ) = 0 by decide, show ¬(1 : ℕ) = 2 by decide, add_zero, zero_add, zero_sub, sub_zero]

def rightOne (pp : PublicParams P0) (c : Coins P0) (D : ExprT P0)
    (a : Option (G1Idx P0)) : F :=
  ((keys2 P0).map fun b => D.1 (a,b) * rightLin pp c b).sum

def rightTwo (pp : PublicParams P0) (c : Coins P0) (D : ExprT P0)
    (a : Option (G1Idx P0)) : F :=
  ((keys2 P0).map fun b => D.1 (a,b) * rightConst pp c b).sum

lemma rightOne_def (pp : PublicParams P0) (c : Coins P0) (D : ExprT P0)
    (a : Option (G1Idx P0)) : rightOne pp c D a =
    ((keys2 P0).map fun b => D.1 (a,b) * rightLin pp c b).sum := rfl

lemma rightTwo_def (pp : PublicParams P0) (c : Coins P0) (D : ExprT P0)
    (a : Option (G1Idx P0)) : rightTwo pp c D a =
    ((keys2 P0).map fun b => D.1 (a,b) * rightConst pp c b).sum := rfl

lemma rightOne_eq (pp : PublicParams P0) (c : Coins P0) (D : ExprT P0)
    (a : Option (G1Idx P0)) : rightOne pp c D a =
    ∑ σ : Sector, ∑ l : Leg P0, ∑ j : I,
      (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l))) * rightBoundary pp c σ l j := by
  simp only [rightOne, keys2_sum, rightLin, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, add_mul, Finset.sum_add_distrib]

lemma clearing_zero {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (l : List R) (d a b k t : R) (hd : f d = 0)
    (h : l.sum + a*d*t*k - b*d*k = 0) : f l.sum = 0 := by
  have hh := congrArg f h
  simpa only [map_sub, map_add, map_mul, hd, mul_zero, zero_mul, add_zero,
    sub_zero, map_zero] using hh

set_option maxRecDepth 4096 in
lemma pairing_boundary_zero (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) :
    boundary c (((keys1 P0).map fun a => ((keys2 P0).map fun b =>
      MvPolynomial.C (D.1 (a,b)) * (e1P pp a * e2P pp v r b)).sum).sum) = 0 := by
  exact clearing_zero (boundary c) _ denomP (MvPolynomial.C D.2)
    (MvPolynomial.C ι) (kappaP pp) (xs .alpha) (boundary_denom c) h

def boundaryCoeff (c : Coins P0) (n : ℕ) : SZ.Poly →+ F :=
  (Polynomial.lcoeff F n).toAddMonoidHom.comp (boundary c).toAddMonoidHom

lemma boundaryCoeff_apply (c : Coins P0) (n : ℕ) (p : SZ.Poly) :
    boundaryCoeff c n p = (boundary c p).coeff n := rfl

lemma pair_coeff_two (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (D : ExprT P0)
    (a : Option (G1Idx P0)) (b : Option (G2Idx P0)) :
    boundaryCoeff c 2 (MvPolynomial.C (D.1 (a,b)) * (e1P pp a * e2P pp v r b)) =
      -(D.1 (a,b) * leftSlope c a * rightLin pp c b) := by
  rw [boundaryCoeff_apply, map_mul, boundary_C, map_mul, boundary_left, boundary_e2,
    coeff_C_mul, affine_coeff_two]
  ring

lemma pair_coeff_one (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (c : Coins P0) (D : ExprT P0)
    (a : Option (G1Idx P0)) (b : Option (G2Idx P0)) :
    boundaryCoeff c 1 (MvPolynomial.C (D.1 (a,b)) * (e1P pp a * e2P pp v r b)) =
      D.1 (a,b) * (leftSlope c a * rightConst pp c b - leftBase pp c a * rightLin pp c b) := by
  rw [boundaryCoeff_apply, map_mul, boundary_C, map_mul, boundary_left, boundary_e2,
    coeff_C_mul, affine_coeff_one]

lemma map_nested_eq {R S α β : Type*} [AddCommMonoid R] [AddCommMonoid S]
    (f : R →+ S) (l : List α) (k : List β) (g : α → β → R) (z : α → β → S)
    (h : ∀ a b, f (g a b) = z a b) :
    f ((l.map fun a => (k.map (g a)).sum).sum) = (l.map fun a => (k.map (z a)).sum).sum := by
  simp only [map_list_sum, List.map_map, Function.comp_def, h]

lemma inner_coeff_two {R α : Type*} [CommRing R] (l : List α) (d y : α → R) (x : R) :
    (l.map fun a => -(d a*x*y a)).sum = -x*(l.map fun a => d a*y a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma inner_coeff_one {R α : Type*} [CommRing R] (l : List α) (d y z : α → R) (s t : R) :
    (l.map fun a => d a*(s*y a-t*z a)).sum =
      s*(l.map fun a => d a*y a).sum - t*(l.map fun a => d a*z a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma rcv_quadratic_sum_zero {R S α β : Type*} [CommRing R] [AddCommMonoid S]
    (f : S →+ R) (l : List α) (k : List β) (d : α → β → R)
    (s : α → R) (t : β → R) (g : α → β → S)
    (hg : ∀ a b, f (g a b) = -(d a b * s a * t b))
    (hz : f ((l.map fun a => (k.map (g a)).sum).sum) = 0) :
    (l.map fun a => s a * (k.map fun b => d a b * t b).sum).sum = 0 := by
  have hcoef := (map_nested_eq f l k g
    (fun a b => -(d a b * s a * t b)) hg).symm.trans hz
  have he : (l.map fun a => (k.map fun b => -(d a b * s a * t b)).sum).sum =
      -(l.map fun a => s a * (k.map fun b => d a b * t b).sum).sum := by
    simp only [inner_coeff_two, neg_mul, list_sum_neg]
  exact neg_eq_zero.mp (he.symm.trans hcoef)

lemma boundary_quadratic (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (c : Coins P0) :
    ((keys1 P0).map fun a => leftSlope c a * rightOne pp c D a).sum = 0 := by
  change ((keys1 P0).map fun a => leftSlope c a *
    ((keys2 P0).map fun b => D.1 (a,b) * rightLin pp c b).sum).sum = 0
  apply rcv_quadratic_sum_zero (boundaryCoeff c 2) (keys1 P0) (keys2 P0)
    (fun a b => D.1 (a,b)) (leftSlope c) (rightLin pp c)
    (fun a b => MvPolynomial.C (D.1 (a,b)) * (e1P pp a * e2P pp v r b))
    (pair_coeff_two pp v r c D)
  rw [boundaryCoeff_apply, pairing_boundary_zero pp v r c D ι h, coeff_zero]

lemma boundary_linear (pp : PublicParams P0) (v : Fin P0.n → Vec F P0.N)
    (r : Vec F P0.N) (D : ExprT P0) (ι : F)
    (h : differenceP pp v r D ι = 0) (c : Coins P0) :
    ((keys1 P0).map fun a => leftSlope c a * rightTwo pp c D a -
      leftBase pp c a * rightOne pp c D a).sum = 0 := by
  have hz := pairing_boundary_zero pp v r c D ι h
  have hcoef : boundaryCoeff c 1 (((keys1 P0).map fun a => ((keys2 P0).map fun b =>
      MvPolynomial.C (D.1 (a,b)) * (e1P pp a * e2P pp v r b)).sum).sum) = 0 := by
    rw [boundaryCoeff_apply, hz, coeff_zero]
  rw [map_nested_eq (boundaryCoeff c 1) (keys1 P0) (keys2 P0)
    (fun a b => MvPolynomial.C (D.1 (a,b)) * (e1P pp a * e2P pp v r b))
    (fun a b => D.1 (a,b) * (leftSlope c a * rightConst pp c b - leftBase pp c a * rightLin pp c b))
    (pair_coeff_one pp v r c D)] at hcoef
  simpa only [inner_coeff_one, rightOne_def, rightTwo_def] using hcoef

end

end Praxis.Proofs.Monitor
