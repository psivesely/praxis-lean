import Praxis.Proofs.View.ForwardLines
import Praxis.Proofs.View.ForwardEpsilon
import Praxis.Proofs.View.ForwardTieDivision
import Praxis.Dec
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Proofs.Ties.Origin
import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardMain
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Scheme
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

set_option maxRecDepth 2048

lemma sum_tieIdx {M : Type*} [AddCommMonoid M] (f : TieIdx → M) :
    ∑ s, f s = f .t1 + f .t2 + f .t3 := by
  change ({.t1,.t2,.t3} : Finset TieIdx).sum f = _
  simp [add_assoc]

lemma sum_crossIdx {M : Type*} [AddCommMonoid M] (f : CrossIdx → M) :
    ∑ g, f g = f .c1eps + f .c2eps + f .c3eps + f .c2div + f .c3div := by
  change ({.c1eps,.c2eps,.c3eps,.c2div,.c3div} : Finset CrossIdx).sum f = _
  simp [add_assoc]

section Definitions

variable {P : Params} [Fact (Nat.Prime P.q)]

noncomputable def tieCancel (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P) (σ : Sector)
    (s : TieIdx) (i : Fin (P.N+1)) (u : Fq P) : Fq P :=
  (∑ t ∈ Finset.range (2*P.n-1), u^t * tiePoly v (aC E σ) s t i) +
    (u^P.n - c0F P) * ∑ e : Fin (P.n-1), gmC E σ i s e * u^e.val

noncomputable def crossCancel (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P) (σ : Sector)
    (g : CrossIdx) (i : Fin (P.N+1)) (u : Fq P) : Fq P :=
  (∑ t ∈ Finset.range (2*P.n-1), u^t * crossPoly v (aC E σ) g t i) +
    ∑ e : Fin (2*P.n-1), gbC E σ i g e * u^e.val

noncomputable def maskPhi (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P) (σ : Sector)
    (i : Fin (P.N+1)) (c : Coins P) : Fq P :=
  (∑ s, cTie c s * tieCancel v E σ s i (coin c .u)) +
    (∑ g, crossVal c g * crossCancel v E σ g i (coin c .u)) +
    ∑ k, lC E σ k i * coin c .u ^ (2*k.val) * (1 + coin c .eps * thetaAt k.val)

noncomputable def tieCrossE (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P) (σ : Sector)
    (s : TieIdx) (i : Fin (P.N+1)) (u : Fq P) : Fq P :=
  match s with
  | .t1 => crossCancel v E σ .c1eps i u
  | .t2 => crossCancel v E σ .c2eps i u
  | .t3 => crossCancel v E σ .c3eps i u

noncomputable def tieCrossD (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P) (σ : Sector)
    (s : TieIdx) (i : Fin (P.N+1)) (u : Fq P) : Fq P :=
  match s with
  | .t1 => 0
  | .t2 => crossCancel v E σ .c2div i u
  | .t3 => crossCancel v E σ .c3div i u

def tieCoin : TieIdx → ScalarCoin
  | .t1 => .c1
  | .t2 => .c2
  | .t3 => .c3

end Definitions

set_option maxHeartbeats 1000000 in
lemma maskTerm_phi (v : Fin P0.n → Vec (Fq P0) P0.N) (E : ExprT P0) (σ : Sector)
    (c : Coins P0) (hε : coin c .eps ≠ 0) :
    maskTerm v E σ c = coin c .pi * ∑ i, c.1 i * maskPhi v E σ i c := by
  have hl : (∑ k, ∑ i, lC E σ k i * piAt c k.val * c.1 i) =
      coin c .pi * ∑ i, c.1 i * ∑ k, lC E σ k i * coin c .u ^ (2*k.val) *
        (1 + coin c .eps * thetaAt k.val) := by
    rw [Finset.sum_comm]
    simp only [piAt, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold maskTerm
  rw [Ties.mask_origin v (aC E σ) c hε, hl]
  simp only [maskPhi, tieCancel, crossCancel, kummerAtU, mul_add, add_mul,
    Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
  abel

lemma maskPhi_zero (Dm : QAPData P0) (v : Fin P0.n → Vec (Fq P0) P0.N) (E : ExprT P0)
    (σ : Sector) (h : ∀ c, ValidCoins Dm c → maskTerm v E σ c = 0)
    (c : Coins P0) (hc : ValidCoins Dm c) (i : Fin (P0.N+1)) : maskPhi v E σ i c = 0 := by
  classical
  let cy : Coins P0 := (Pi.single i 1, c.2.1, c.2.2)
  have hcy : ValidCoins Dm cy := hc
  have hh := h cy hcy
  rw [maskTerm_phi _ _ _ _ hcy.2.2.1] at hh
  have he : (coin cy .pi * ∑ j, cy.1 j * maskPhi v E σ j cy) =
      coin c .pi * maskPhi v E σ i c := by
    change coin c .pi * (∑ j, (Pi.single i (1 : Fq P0) : Vec (Fq P0) P0.N) j * maskPhi v E σ j c) = _
    simp [Pi.single_apply, ite_mul]
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (hc.2.1 .pi rfl)

section TieCoin

variable {P : Params} [Fact (Nat.Prime P.q)]

lemma maskPhi_tie_scale (v : Fin P.n → Vec (Fq P) P.N) (E : ExprT P) (σ : Sector)
    (i : Fin (P.N+1)) (c : Coins P) (s : TieIdx) :
    maskPhi v E σ i (setCoin c (tieCoin s) (2*cTie c s)) - maskPhi v E σ i c =
      cTie c s * (tieCancel v E σ s i (coin c .u) +
        coin c .eps * tieCrossE v E σ s i (coin c .u) +
        tieCrossD v E σ s i (coin c .u) / coin c .eps) := by
  cases s <;> simp [maskPhi, sum_tieIdx, sum_crossIdx, tieCoin, cTie, crossVal,
    tieCrossE, tieCrossD, div_eq_mul_inv] <;> ring

lemma cTie_ne_zero (Dm : QAPData P) (c : Coins P) (hc : ValidCoins Dm c) (s : TieIdx) :
    cTie c s ≠ 0 := by
  cases s
  · exact hc.2.1 .c1 rfl
  · exact hc.2.1 .c2 rfl
  · exact hc.2.1 .c3 rfl

end TieCoin

lemma tie_coin_equation (Dm : QAPData P0) (v : Fin P0.n → Vec (Fq P0) P0.N) (E : ExprT P0)
    (σ : Sector) (h : ∀ c, ValidCoins Dm c → maskTerm v E σ c = 0)
    (c : Coins P0) (hc : ValidCoins Dm c) (s : TieIdx) (i : Fin (P0.N+1)) :
    tieCancel v E σ s i (coin c .u) + coin c .eps * tieCrossE v E σ s i (coin c .u) +
      tieCrossD v E σ s i (coin c .u) / coin c .eps = 0 := by
  have hv : ValidCoins Dm (setCoin c (tieCoin s) (2*cTie c s)) := by
    apply setCoin_valid Dm c hc _ _
    · cases s <;> decide
    · cases s <;> decide
    · intro _
      exact mul_ne_zero (by decide) (cTie_ne_zero Dm c hc s)
  have hh := maskPhi_tie_scale v E σ i c s
  rw [maskPhi_zero Dm v E σ h _ hv i, maskPhi_zero Dm v E σ h c hc i, sub_self] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (cTie_ne_zero Dm c hc s)

lemma tieCancel_zero (Dm : QAPData P0) (v : Fin P0.n → Vec (Fq P0) P0.N) (E : ExprT P0)
    (σ : Sector) (h : ∀ c, ValidCoins Dm c → maskTerm v E σ c = 0)
    (s : TieIdx) (i : Fin (P0.N+1)) (u : Fq P0) (hu : u ≠ 0) : tieCancel v E σ s i u = 0 := by
  obtain ⟨c, hc⟩ := (main_validCoins_nonempty Dm).some
  have hcu := setCoin_valid Dm c hc .u u (by decide) (by decide) (fun _ => hu)
  apply eps_affine_sep (tieCancel v E σ s i u) (tieCrossE v E σ s i u) (tieCrossD v E σ s i u)
  intro ε hε hf
  have hce := setEps_valid Dm _ hcu ε hε hf
  have hh := tie_coin_equation Dm v E σ h _ hce s i
  simpa only [coin_setCoin, reduceCtorEq, ite_true, ite_false] using hh

lemma mask_ties (Dm : QAPData P0) (v : Fin P0.n → Vec (Fq P0) P0.N) (E : ExprT P0)
    (σ : Sector) (h : ∀ c, ValidCoins Dm c → maskTerm v E σ c = 0) : Ties v (aC E σ) := by
  intro s
  ext e i
  exact tie_reduction_of_cancel v (aC E σ) s i (gmC E σ i s)
    (fun u hu => tieCancel_zero Dm v E σ h s i u hu) e

end Praxis.Proofs.View
