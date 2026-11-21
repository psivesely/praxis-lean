import Praxis.Proofs.View.ForwardCoins
import Praxis.Proofs.View.ForwardCells
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.Ties.Grid
import Praxis.Proofs.View.ForwardSeparation
import Praxis.Params
import Praxis.QAP
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

set_option maxRecDepth 2048

def bCoin : LegKind → ScalarCoin
  | .E => .bE
  | .O => .bO
  | .V => .bV

lemma bCoin_ne_tau (X : LegKind) : bCoin X ≠ .tau := by cases X <;> decide

lemma bCoin_ne_eps (X : LegKind) : bCoin X ≠ .eps := by cases X <;> decide

section Gamma

variable {P : Params} [Fact (Nat.Prime P.q)]

lemma bOf_ne_zero (Dm : QAPData P) (c : Coins P) (hc : ValidCoins Dm c) (X : LegKind) :
    bOf c X ≠ 0 := by
  cases X
  · exact hc.2.1 .bE rfl
  · exact hc.2.1 .bO rfl
  · exact hc.2.1 .bV rfl

lemma bOf_set_b (c : Coins P) (X Y : LegKind) (x : Fq P) :
    bOf (setCoin c (bCoin X) x) Y = if Y = X then x else bOf c Y := by
  cases X <;> cases Y <;> simp [bOf, bCoin]

lemma gamma_monomial (c : Coins P) (cl : Cell P) :
    gamma c cl = coin c .pi * bOf c cl.2.1 * (1 + coin c .eps * thetaAt cl.1.val) *
      coin c .u ^ cellExp cl := by
  simp only [gamma, piAt, legScale, legScaleAt, cellExp, legExp, pow_add]
  ring

lemma gamma_set_u (c : Coins P) (u : Fq P) (cl : Cell P) :
    gamma (setCoin c .u u) cl =
      coin c .pi * bOf c cl.2.1 * (1 + coin c .eps * thetaAt cl.1.val) * u ^ cellExp cl := by
  rw [gamma_monomial]
  cases cl.2.1 <;> simp [bOf]

lemma gamma_set_b (c : Coins P) (X : LegKind) (cl : Cell P) (x : Fq P) :
    gamma (setCoin c (bCoin X) x) cl =
      coin c .pi * (if cl.2.1 = X then x else bOf c cl.2.1) *
        (1 + coin c .eps * thetaAt cl.1.val) * coin c .u ^ cellExp cl := by
  rw [gamma_monomial, bOf_set_b]
  cases X <;> simp [bCoin]

lemma valid_pi_factor_ne_zero (Dm : QAPData P) (c : Coins P) (hc : ValidCoins Dm c)
    (k : Fin P.K1) : 1 + coin c .eps * thetaAt k.val ≠ 0 := by
  intro hz
  by_cases hθ : (thetaAt k.val : Fq P) = 0
  · simp [hθ] at hz
  · apply hc.2.2.2 k
    change coin c .eps = -(thetaAt k.val)⁻¹
    field_simp [hθ]
    linear_combination hz

end Gamma

lemma cellExp_lt (cl : Cell P0) : cellExp cl < P0.n := by
  by_cases hu : IsUCell cl
  · exact Ties.uCell_exp_bijOn.mapsTo hu
  · exact (Ties.vCell_exp_bijOn.mapsTo hu).1

lemma cellExp_injective_kind (X : LegKind) :
    Set.InjOn (fun cl : Cell P0 => cellExp cl) {cl | cl.2.1 = X} := by
  intro a ha b hb he
  change a.2.1 = X at ha
  change b.2.1 = X at hb
  by_cases hx : X = .V
  · exact Ties.vCell_exp_bijOn.injOn (by simp [IsUCell, ha, hx]) (by simp [IsUCell, hb, hx]) he
  · exact Ties.uCell_exp_bijOn.injOn (by simpa [IsUCell, ha] using hx)
      (by simpa [IsUCell, hb] using hx) he

section CellSeparation

variable (Dm : QAPData P0) (y : Vec (Fq P0) P0.N) (τ : Fq P0)
  (a : Cell P0 → Fq P0)
  (h : ∀ c, ValidCoins Dm c → c.1 = y → coin c .tau = τ → ∑ cl, gamma c cl * a cl = 0)

include h

lemma gamma_family_zero (c : Coins P0) (hc : ValidCoins Dm c) (hy : c.1 = y)
    (hτ : coin c .tau = τ) (X : LegKind) :
    ∑ cl ∈ Finset.univ.filter (fun cl : Cell P0 => cl.2.1 = X), gamma c cl * a cl = 0 := by
  classical
  have htwo : (2 : Fq P0) ≠ 0 := by decide
  have hv : ValidCoins Dm (setCoin c (bCoin X) (2 * bOf c X)) := by
    apply setCoin_valid Dm c hc _ _ (bCoin_ne_tau X) (bCoin_ne_eps X)
    intro _
    exact mul_ne_zero htwo (bOf_ne_zero Dm c hc X)
  have hτ' : coin (setCoin c (bCoin X) (2 * bOf c X)) .tau = τ := by
    cases X <;> simpa [bCoin] using hτ
  have hs := h _ hv hy hτ'
  have h0 := h c hc hy hτ
  have he : (∑ cl, gamma (setCoin c (bCoin X) (2 * bOf c X)) cl * a cl) =
      (∑ cl, gamma c cl * a cl) +
        ∑ cl, if cl.2.1 = X then gamma c cl * a cl else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro cl _
    rw [gamma_set_b, gamma_monomial]
    by_cases hx : cl.2.1 = X
    · simp only [hx, ite_true]
      ring
    · simp [hx]
  rw [he, h0, zero_add] at hs
  simpa only [Finset.sum_filter] using hs

lemma cell_sep (hτ : ∀ k, τ ≠ Dm.point k) : a = 0 := by
  classical
  obtain ⟨c, hc, hy, hcτ⟩ := validCoins_at_y_tau Dm y τ hτ
  have hf (X : LegKind) : ∀ cl, cl.2.1 = X →
      (coin c .pi * bOf c cl.2.1 * (1 + coin c .eps * thetaAt cl.1.val)) * a cl = 0 := by
    let s := Finset.univ.filter (fun cl : Cell P0 => cl.2.1 = X)
    have hu : ∀ u : Fq P0, u ≠ 0 →
        ∑ cl ∈ s, ((coin c .pi * bOf c cl.2.1 * (1 + coin c .eps * thetaAt cl.1.val)) * a cl) *
          u ^ cellExp cl = 0 := by
      intro u hune
      have hv := setCoin_valid Dm c hc .u u (by decide) (by decide) (fun _ => hune)
      have htau : coin (setCoin c .u u) .tau = τ := by simpa using hcτ
      have hh := gamma_family_zero Dm y τ a h _ hv hy htau X
      simpa only [gamma_set_u, mul_right_comm] using hh
    have hm := mono_sep s (fun cl => cellExp cl)
      (fun cl => (coin c .pi * bOf c cl.2.1 * (1 + coin c .eps * thetaAt cl.1.val)) * a cl)
      (by intro cl hcl cl' hcl' he
          exact cellExp_injective_kind X (Finset.mem_filter.mp hcl).2
            (Finset.mem_filter.mp hcl').2 he)
      (fun cl _ => (cellExp_lt cl).trans (by
        simpa only [ZMod.card] using (show P0.n < P0.q - 1 by decide))) hu
    intro cl hcl
    exact hm cl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩)
  ext cl
  exact (mul_eq_zero.mp (hf cl.2.1 cl rfl)).resolve_left
    (mul_ne_zero (mul_ne_zero (hc.2.1 .pi rfl) (bOf_ne_zero Dm c hc cl.2.1))
      (valid_pi_factor_ne_zero Dm c hc cl.1))

end CellSeparation

end Praxis.Proofs.View
