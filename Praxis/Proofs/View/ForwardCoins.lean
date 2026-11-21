import Praxis.Proofs.View.ForwardSeparation
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Scheme
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

set_option maxRecDepth 2048

inductive ViewScale
  | alpha | pi | zeta | zeta' | zeta4 | omega
  deriving DecidableEq

def ViewScale.flag : ViewScale → ScalarCoin → Bool
  | .alpha, .alpha | .pi, .pi | .zeta, .zeta | .zeta', .zeta' | .zeta4, .zeta4 => true
  | .omega, .Om12 | .omega, .Om22 => true
  | _, _ => false

def scaleCoins {P : Params} (s : ViewScale) (t : Fq P) (c : Coins P) : Coins P :=
  (c.1, c.2.1, fun x => if s.flag x then t * c.2.2 x else c.2.2 x)

def ViewScale.weight1 {P : Params} : ViewScale → Option (G1Idx P) → Fin 3
  | .pi, some (.L1 _ _) | .pi, some (.L2 _ _) | .pi, some (.totL1 _) | .pi, some (.totL2 _) => 2
  | .zeta, some (.QP _) | .zeta', some (.RP _) | .zeta4, some (.GY _) => 2
  | .omega, some (.L2 _ _) | .omega, some (.totL2 _) => 2
  | _, _ => 1

def g2Sector {P : Params} : G2Idx P → Sector
  | .ZeroCoordinate σ _ _ | .R2 σ _ _ | .totR1 σ _ | .totR2 σ _ | .QB σ _ _ | .RB σ _ _ |
      .SC σ _ | .GB σ _ _ | .GM σ _ _ => σ

def ViewScale.weight2 {P : Params} : ViewScale → Option (G2Idx P) → Fin 3
  | .alpha, some b => if g2Sector b = .alpha then 2 else 1
  | .pi, some (.QB _ _ _) | .pi, some (.RB _ _ _) | .pi, some (.GB _ _ _) |
      .pi, some (.GM _ _ _) => 2
  | .zeta, some (.QB _ _ _) | .zeta', some (.RB _ _ _) | .zeta4, some (.GB _ _ _) |
      .zeta4, some (.GM _ _ _) => 0
  | .omega, some (.R2 _ _ _) | .omega, some (.totR2 _ _) => 0
  | _, _ => 1

def ViewScale.weightT : ViewScale → Fin 5
  | .alpha | .pi => 3
  | _ => 2

def ViewScale.weightK : ViewScale → Fin 5
  | .pi => 3
  | _ => 2

section CoinFacts

variable {P : Params} [Fact (Nat.Prime P.q)]

lemma scaleCoins_valid (s : ViewScale) (t : Fq P) (c : Coins P) (Dm : QAPData P)
    (ht : t ≠ 0) (hc : ValidCoins Dm c) : ValidCoins Dm (scaleCoins s t c) := by
  have hτ : s.flag .tau = false := by cases s <;> rfl
  have hε : s.flag .eps = false := by cases s <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [scaleCoins, hτ] using hc.1
  · intro x hx
    change (if s.flag x then t * c.2.2 x else c.2.2 x) ≠ 0
    split
    · exact mul_ne_zero ht (hc.2.1 x hx)
    · exact hc.2.1 x hx
  · simpa [scaleCoins, hε] using hc.2.2.1
  · simpa [scaleCoins, hε] using hc.2.2.2

@[simp] lemma coin_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (x : ScalarCoin) :
    coin (scaleCoins s t c) x = if s.flag x then t * coin c x else coin c x := rfl

@[simp] lemma scaleCoins_fst (s : ViewScale) (t : Fq P) (c : Coins P) :
    (scaleCoins s t c).1 = c.1 := rfl

lemma e1At_scaleCoins (s : ViewScale) (pp : PublicParams P) (r : Vec (Fq P) P.N)
    (t : Fq P) (c : Coins P) (a : Option (G1Idx P)) :
    t * e1At pp ⟨scaleCoins s t c, r⟩ a = t ^ (s.weight1 a).val * e1At pp ⟨c, r⟩ a := by
  cases s <;> cases a with
  | none => simp [e1At, ViewScale.weight1]
  | some a => cases a <;>
      simp [e1At, g1Exp, ViewScale.weight1, piAt, coin_scaleCoins, ViewScale.flag,
        scaleCoins, coin, Finset.mul_sum, Finset.sum_mul, pow_two] <;> ring

lemma sectorScale_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (σ : Sector) :
    sectorScale (scaleCoins s t c) σ =
      (if s = .alpha ∧ σ = .alpha then t else 1) * sectorScale c σ := by
  cases s <;> cases σ <;> simp [sectorScale, ViewScale.flag]

lemma piAt_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (k : ℕ) :
    piAt (scaleCoins s t c) k = (if s = .pi then t else 1) * piAt c k := by
  cases s <;> simp [piAt, ViewScale.flag] <;> ring

lemma legScale_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (l : Leg P) :
    legScale (scaleCoins s t c) l = legScale c l := by
  cases s <;> cases l.1 <;> simp [legScale, legScaleAt, bOf, ViewScale.flag]

lemma legMask_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P)
    (v : Fin P.n → Vec (Fq P) P.N) (l : Leg P) :
    legMask v (scaleCoins s t c) l = legMask v c l := by
  cases s <;> simp [legMask, ViewScale.flag]

lemma H2_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (pp : PublicParams P)
    (l : Leg P) (j : Fin (P.N + 1)) :
    H2 pp (scaleCoins s t c) l j = H2 pp c l j := by
  cases s <;> simp [H2, legScale_scaleCoins, ViewScale.flag]

lemma gamma_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (cl : Cell P) :
    gamma (scaleCoins s t c) cl = (if s = .pi then t else 1) * gamma c cl := by
  simp [gamma, piAt_scaleCoins, legScale_scaleCoins, mul_assoc]

lemma r1ExpAt_scaleCoins (s : ViewScale) (pp : PublicParams P)
    (v : Fin P.n → Vec (Fq P) P.N) (r : Vec (Fq P) P.N)
    (t : Fq P) (c : Coins P) (ht : t ≠ 0) (l : Leg P) (j : Fin (P.N + 1)) :
    r1ExpAt pp v ⟨scaleCoins s t c, r⟩ l j = r1ExpAt pp v ⟨c,r⟩ l j := by
  simp only [r1ExpAt, legScale_scaleCoins, legMask_scaleCoins, H2_scaleCoins, coin_scaleCoins]
  cases s <;> simp [ViewScale.flag, div_eq_mul_inv, mul_inv_rev, ht, mul_assoc,
    mul_comm, mul_left_comm]

lemma crossVal_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (g : CrossIdx) :
    crossVal (scaleCoins s t c) g = crossVal c g := by
  cases s <;> cases g <;> simp [crossVal, ViewScale.flag]

lemma cTie_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) (g : TieIdx) :
    cTie (scaleCoins s t c) g = cTie c g := by
  cases s <;> cases g <;> simp [cTie, ViewScale.flag]

lemma kummerAtU_scaleCoins (s : ViewScale) (t : Fq P) (c : Coins P) :
    kummerAtU (scaleCoins s t c) = kummerAtU c := by
  cases s <;> simp [kummerAtU, ViewScale.flag]

set_option maxHeartbeats 1000000 in
lemma e2At_scaleCoins (s : ViewScale) (pp : PublicParams P)
    (v : Fin P.n → Vec (Fq P) P.N) (r : Vec (Fq P) P.N)
    (t : Fq P) (c : Coins P) (ht : t ≠ 0) (hc : ValidCoins pp.qap c)
    (b : Option (G2Idx P)) :
    t * e2At pp v ⟨scaleCoins s t c, r⟩ b =
      t ^ (s.weight2 b).val * e2At pp v ⟨c, r⟩ b := by
  have hΩ := hc.2.1 .Om22 rfl
  have hz := hc.2.1 .zeta rfl
  have hz' := hc.2.1 .zeta' rfl
  have hz4 := hc.2.1 .zeta4 rfl
  cases b with
  | none => cases s <;> simp [e2At, ViewScale.weight2]
  | some b =>
    cases b <;>
      (first | (rename_i σ l j; change Sector at σ; cases σ) |
        (rename_i σ l; cases σ)) <;>
      simp only [e2At, g2Exp, r2Exp, r1ExpAt_scaleCoins _ _ _ _ _ _ ht,
        sectorScale_scaleCoins, gamma_scaleCoins, H2_scaleCoins, legScale_scaleCoins,
        crossVal_scaleCoins, cTie_scaleCoins, kummerAtU_scaleCoins, coin_scaleCoins] <;>
      cases s <;>
      simp [ViewScale.weight2, ViewScale.flag, g2Sector, Finset.mul_sum, Finset.sum_mul,
        div_eq_mul_inv, mul_inv_rev, ht, mul_assoc, mul_comm, mul_left_comm, pow_succ]

lemma kappa_scaleCoins (s : ViewScale) (pp : PublicParams P) (t : Fq P) (c : Coins P) :
    kappa pp (scaleCoins s t c) = (if s = .pi then t else 1) * kappa pp c := by
  cases s <;> simp [kappa, gammaKey, piAt, legScaleAt, bOf, ViewScale.flag] <;> ring

lemma gtExp_scaleCoins (s : ViewScale) (pp : PublicParams P) (t : Fq P) (c : Coins P) :
    t ^ 2 * gtExp pp (scaleCoins s t c) = t ^ s.weightT.val * gtExp pp c := by
  cases s <;> simp [gtExp, kappa_scaleCoins, ViewScale.weightT, ViewScale.flag] <;> ring

lemma target_scaleCoins (s : ViewScale) (pp : PublicParams P) (t : Fq P) (c : Coins P) (ι : Fq P) :
    t ^ 2 * (ι * kappa pp (scaleCoins s t c)) =
      t ^ s.weightK.val * (ι * kappa pp c) := by
  cases s <;> simp [kappa_scaleCoins, ViewScale.weightK] <;> ring

end CoinFacts

def project {P : Params} [Fact (Nat.Prime P.q)] (s : ViewScale) (k : ℕ) (D : ExprT P) : ExprT P :=
  restrictW s.weight1 s.weight2 s.weightT.val k D

lemma project_identity {P : Params} [Fact (Nat.Prime P.q)] (s : ViewScale) (hcard : 4 < P.q - 1) (pp : PublicParams P)
    (v : Fin P.n → Vec (Fq P) P.N) (r : Vec (Fq P) P.N)
    (D : ExprT P) (ι : Fq P) (h : IdentityAtR pp v r D ι) (k : ℕ) :
    IdentityAtR pp v r (project s k D) (if s.weightK.val = k then ι else 0) := by
  have hh := sep_by_scaling pp v r (scaleCoins s) s.weight1 s.weight2 s.weightT s.weightK
    (fun c => ι * kappa pp c) hcard
    (fun t c ht hc => scaleCoins_valid s t c pp.qap ht hc)
    (fun t c a _ _ => e1At_scaleCoins s pp r t c a)
    (fun t c b ht hc => e2At_scaleCoins s pp v r t c ht hc b)
    (fun t c _ _ => gtExp_scaleCoins s pp t c)
    (fun t c _ _ => target_scaleCoins s pp t c ι) D h k
  intro c hc
  have hr := hh c hc
  change valT pp v ⟨c,r⟩ (project s k D) = _ at hr
  split_ifs at hr ⊢ <;> simpa using hr

section Updates

variable {P : Params}

def setCoin (c : Coins P) (s : ScalarCoin) (x : Fq P) : Coins P :=
  (c.1, c.2.1, Function.update c.2.2 s x)

@[simp] lemma coin_setCoin (c : Coins P) (s t : ScalarCoin) (x : Fq P) :
    coin (setCoin c s x) t = if t = s then x else coin c t := by
  simp [setCoin, coin, Function.update_apply]

@[simp] lemma setCoin_fst (c : Coins P) (s : ScalarCoin) (x : Fq P) : (setCoin c s x).1 = c.1 := rfl

lemma setCoin_valid (Dm : QAPData P) (c : Coins P) (hc : ValidCoins Dm c)
    (s : ScalarCoin) (x : Fq P) (hsτ : s ≠ .tau) (hsε : s ≠ .eps)
    (hx : s.inUnits = true → x ≠ 0) : ValidCoins Dm (setCoin c s x) := by
  have hτ : ScalarCoin.tau ≠ s := Ne.symm hsτ
  have hε : ScalarCoin.eps ≠ s := Ne.symm hsε
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [setCoin, Function.update_of_ne hτ] using hc.1
  · intro t ht
    by_cases hts : t = s
    · subst t
      simpa [setCoin] using hx ht
    · simpa [setCoin, Function.update_of_ne hts] using hc.2.1 t ht
  · simpa [setCoin, Function.update_of_ne hε] using hc.2.2.1
  · simpa [setCoin, Function.update_of_ne hε] using hc.2.2.2

lemma setOm12_valid (Dm : QAPData P) (c : Coins P) (hc : ValidCoins Dm c) (x : Fq P) :
    ValidCoins Dm (setCoin c .Om12 x) :=
  setCoin_valid Dm c hc .Om12 x (by decide) (by decide) (by simp [ScalarCoin.inUnits])

lemma validCoins_at_y_tau (Dm : QAPData P0) (y : Vec (Fq P0) P0.N) (τ : Fq P0)
    (hτ : ∀ k, τ ≠ Dm.point k) :
    ∃ c : Coins P0, ValidCoins Dm c ∧ c.1 = y ∧ coin c .tau = τ := by
  obtain ⟨c0, hc0⟩ := (main_validCoins_nonempty Dm).some
  let c : Coins P0 := (y, c0.2.1, Function.update c0.2.2 .tau τ)
  refine ⟨c, ⟨?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · simpa [c] using hτ
  · intro s hs
    have hst : s ≠ .tau := by intro hh; subst s; contradiction
    simpa [c, Function.update_of_ne hst] using hc0.2.1 s hs
  · simpa [c] using hc0.2.2.1
  · simpa [c] using hc0.2.2.2
  · simp [c, coin]

end Updates

end Praxis.Proofs.View
