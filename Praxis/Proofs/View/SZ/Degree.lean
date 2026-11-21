import Praxis.Proofs.View.SZ.PolyDegree
import Praxis.Constants
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Proofs.Degree
import Praxis.Proofs.View.SZ.Model
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View.SZ

open MvPolynomial

theorem tauP_degree (p : Polynomial (Fq P0)) : (tauP p).totalDegree ≤ p.natDegree := by
  rw [tauP, Polynomial.eval₂_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  calc
    (C (p.coeff i) * xs .tau ^ i).totalDegree ≤
        (C (p.coeff i) : Poly).totalDegree + (xs .tau ^ i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = i := by simp [xs, MvPolynomial.totalDegree_X_pow]
    _ ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

@[simp] theorem xs_degree (s : ScalarCoin) : (xs s).totalDegree = 1 := by
  simp [xs, totalDegree_X]

@[simp] theorem xy_degree (i : Fin (P0.N + 1)) : (xy i).totalDegree = 1 := by
  simp [xy, totalDegree_X]

@[simp] theorem xs_pow_degree (s : ScalarCoin) (n : ℕ) : (xs s ^ n).totalDegree = n := by
  simp [xs, totalDegree_X_pow]

theorem legExp_lt_n (l : Leg P0) : legExp l < P0.n := by
  rcases l with ⟨k, i⟩
  have hi : i.val < 12 := i.isLt
  cases k <;> simp only [legExp, LegKind.base, P0, Params.main,
    Constants.K1, Constants.n] <;> omega

theorem cellExp_lt_n (cl : Cell P0) : cellExp cl < P0.n := by
  rcases cl with ⟨k, l, i⟩
  have hk : k.val < 192 := k.isLt
  have hi : i.val < 12 := i.isLt
  cases l <;> simp only [cellExp, legExp, LegKind.base, P0, Params.main,
    Constants.K1, Constants.n] <;> omega

theorem piP_degree (k : ℕ) : (piP k).totalDegree ≤ 2 * k + 2 := by
  unfold piP
  have h₁ := totalDegree_mul (xs .pi) (xs .u ^ (2 * k))
  have h₂ := totalDegree_mul (xs .eps) (C (betaF P0 ^ (2 * k)))
  have h₃ := totalDegree_add (1 : Poly) (xs .eps * C (betaF P0 ^ (2 * k)))
  have h₄ := totalDegree_mul (xs .pi * xs .u ^ (2 * k))
    (1 + xs .eps * C (betaF P0 ^ (2 * k)))
  simp only [xs_degree, xs_pow_degree, totalDegree_C, totalDegree_one] at h₁ h₂ h₃ h₄
  omega

theorem legP_degree (l : Leg P0) : (legP l).totalDegree ≤ 1 + legExp l := by
  have h := totalDegree_mul (bP l.1) (xs .u ^ legExp l)
  have hb : (bP l.1).totalDegree = 1 := by
    cases l.1 <;> simp [bP]
  simpa only [legP, hb, xs_pow_degree] using h

theorem gammaP_degree (cl : Cell P0) :
    (gammaP cl).totalDegree ≤ 2 * cl.1.val + legExp cl.2 + 3 := by
  have h := totalDegree_mul (piP cl.1.val) (legP cl.2)
  have h₁ := piP_degree cl.1.val
  have h₂ := legP_degree cl.2
  dsimp only [gammaP]
  omega

theorem denomP_degree : denomP.totalDegree ≤ 5 := by
  unfold denomP
  have h₁ := totalDegree_mul (xs .Om22) (xs .zeta)
  have h₂ := totalDegree_mul (xs .Om22 * xs .zeta) (xs .zeta')
  have h₃ := totalDegree_mul (xs .Om22 * xs .zeta * xs .zeta') (xs .zeta4)
  have h₄ := totalDegree_mul (xs .Om22 * xs .zeta * xs .zeta' * xs .zeta4) (xs .eps)
  simp only [xs_degree] at h₁ h₂ h₃ h₄
  omega

theorem sectorP_degree (σ : Sector) : (sectorP σ).totalDegree ≤ 1 := by
  cases σ <;> simp [sectorP]

theorem crossP_degree (g : CrossIdx) : (crossP g).totalDegree ≤ 3 := by
  cases g <;> simp only [crossP]
  all_goals try (simp only [xs_degree]; omega)
  all_goals
    apply (totalDegree_mul _ _).trans
    simp only [xs_degree, xs_pow_degree]
    omega

theorem tieP_degree (s : TieIdx) : (tieP s).totalDegree ≤ 1 := by
  cases s <;> simp [tieP]

theorem r2P_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (l : Leg P0) (j : Fin (P0.N + 1)) :
    (r2P pp l j).totalDegree ≤ legExp l + Constants.D + 4 := by
  have hb : (tauP (pp.qap.B j)).totalDegree < Constants.D :=
    (tauP_degree _).trans_lt (hD.B_degree j)
  have hl := legP_degree l
  have h₁ := totalDegree_mul (xs .zeta) (xs .zeta')
  have h₂ := totalDegree_mul (xs .zeta * xs .zeta') (xs .zeta4)
  have h₃ := totalDegree_mul (xs .zeta * xs .zeta' * xs .zeta4) (xs .eps)
  have h₄ := totalDegree_mul (xs .zeta * xs .zeta' * xs .zeta4 * xs .eps) (legP l)
  have h₅ := totalDegree_sub (tauP (pp.qap.B j)) (xy j)
  have h₆ := totalDegree_mul (xs .zeta * xs .zeta' * xs .zeta4 * xs .eps * legP l)
    (tauP (pp.qap.B j) - xy j)
  simp only [xs_degree, xy_degree] at h₁ h₂ h₃ h₅
  have hD' : 2 ≤ Constants.D := by decide
  dsimp only [r2P]
  omega

theorem e2P_SC_degree (pp : PublicParams P0)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (σ : Sector) (l : Leg P0) :
    (e2P pp v r (some (.SC σ l))).totalDegree ≤ Constants.view_degree_d2 := by
  have h₁ := totalDegree_mul (sectorP σ) denomP
  have h₂ := totalDegree_mul (sectorP σ * denomP) (legP l)
  have hs := sectorP_degree σ
  have hd := denomP_degree
  have hl := legP_degree l
  have hn := legExp_lt_n l
  have hnum : P0.n + 7 ≤ Constants.view_degree_d2 := by decide
  simp only [e2P]
  omega

theorem e2P_R2_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (σ : Sector) (l : Leg P0) (j : Fin (P0.N + 1)) :
    (e2P pp v r (some (.R2 σ l j))).totalDegree ≤ Constants.view_degree_d2 := by
  have h₁ := totalDegree_mul (sectorP σ) (r2P pp l j)
  have hs := sectorP_degree σ
  have hr := r2P_degree pp S hD l j
  have hn := legExp_lt_n l
  have hnum : P0.n + Constants.D + 5 ≤ Constants.view_degree_d2 := by decide
  simp only [e2P]
  omega

theorem e2P_totR2_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (σ : Sector) (l : Leg P0) :
    (e2P pp v r (some (.totR2 σ l))).totalDegree ≤ Constants.view_degree_d2 := by
  have hs := sectorP_degree σ
  have hn := legExp_lt_n l
  have hnum : P0.n + Constants.D + 5 ≤ Constants.view_degree_d2 := by decide
  have hsum : (∑ j, r2P pp l j).totalDegree ≤ legExp l + Constants.D + 4 := by
    apply totalDegree_finsetSum_le
    intro j hj
    exact r2P_degree pp S hD l j
  have h := totalDegree_mul (sectorP σ) (∑ j, r2P pp l j)
  simp only [e2P]
  omega

theorem lamP_degree (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (x : Poly)
    (hx : x.totalDegree ≤ 1) (j : Fin (P0.N + 1)) :
    (lamP v x j).totalDegree ≤ P0.n - 1 := by
  unfold lamP
  apply totalDegree_finsetSum_le
  intro e he
  have h₁ := totalDegree_mul (C (v e j)) (x ^ e.val)
  have h₂ := totalDegree_pow x e.val
  simp only [totalDegree_C, zero_add] at h₁
  have he' := e.isLt
  have hem : e.val ≤ P0.n - 1 := Nat.le_sub_one_of_lt he'
  have hm : e.val * x.totalDegree ≤ e.val := by nlinarith
  omega

theorem maskP_degree (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N)
    (l : Leg P0) (j : Fin (P0.N + 1)) :
    (maskP v l j).totalDegree ≤ legExp l + P0.n + 1 := by
  have hx (a : Fq P0) : (C a * xs .u).totalDegree ≤ 1 := by
    have h := totalDegree_mul (C a) (xs .u)
    simpa using h
  have hn : (-xs .u).totalDegree ≤ 1 := by simp
  have hl1 := lamP_degree v (-xs .u) hn j
  have hl2 := lamP_degree v (C (-betaF P0) * xs .u) (hx _) j
  have hl3 := lamP_degree v (C (betaF P0 ^ (P0.m - 1)) * xs .u) (hx _) j
  have hp := totalDegree_pow (C (-betaF P0) * xs .u) (legExp l)
  have hnum : 0 < P0.n := by decide
  have h₁ := totalDegree_mul (xs .c1) (lamP v (-xs .u) j)
  have h₂ := totalDegree_mul (xs .c2) (lamP v (C (-betaF P0) * xs .u) j)
  have h₃ := totalDegree_mul (xs .c3) (lamP v (C (-betaF P0) * xs .u) j)
  have h₄ := totalDegree_mul (xs .c1) (lamP v (C (betaF P0 ^ (P0.m - 1)) * xs .u) j)
  have h₅ := totalDegree_mul (xs .c2) (lamP v (C (betaF P0 ^ (P0.m - 1)) * xs .u) j)
  have h₆ := totalDegree_mul (xs .c3) (lamP v (-xs .u) j)
  have h₇ := totalDegree_add (xs .c1 * lamP v (-xs .u) j)
    (xs .c2 * lamP v (C (-betaF P0) * xs .u) j)
  have h₈ := totalDegree_sub (xs .c3 * lamP v (C (-betaF P0) * xs .u) j)
    (xs .c1 * lamP v (C (betaF P0 ^ (P0.m - 1)) * xs .u) j)
  have h₉ := totalDegree_add (xs .c2 * lamP v (C (betaF P0 ^ (P0.m - 1)) * xs .u) j)
    (xs .c3 * lamP v (-xs .u) j)
  have h₁₀ := totalDegree_mul (xs .eps) (xs .u ^ legExp l)
  have h₁₁ := totalDegree_mul (xs .eps * xs .u ^ legExp l)
    (xs .c1 * lamP v (-xs .u) j + xs .c2 * lamP v (C (-betaF P0) * xs .u) j)
  have h₁₂ := totalDegree_mul (xs .eps * xs .u ^ legExp l)
    (xs .c3 * lamP v (C (-betaF P0) * xs .u) j -
      xs .c1 * lamP v (C (betaF P0 ^ (P0.m - 1)) * xs .u) j)
  have h₁₃ := totalDegree_mul ((C (-betaF P0) * xs .u) ^ legExp l)
    (xs .c2 * lamP v (C (betaF P0 ^ (P0.m - 1)) * xs .u) j + xs .c3 * lamP v (-xs .u) j)
  have h₁₄ := totalDegree_sub
    (xs .eps * xs .u ^ legExp l *
      (xs .c1 * lamP v (-xs .u) j + xs .c2 * lamP v (C (-betaF P0) * xs .u) j))
    ((C (-betaF P0) * xs .u) ^ legExp l *
      (xs .c2 * lamP v (C (betaF P0 ^ (P0.m - 1)) * xs .u) j + xs .c3 * lamP v (-xs .u) j))
  simp only [xs_degree, xs_pow_degree] at h₁ h₂ h₃ h₄ h₅ h₆ h₁₀
  have hpm : legExp l * (C (-betaF P0) * xs .u).totalDegree ≤ legExp l := by
    have := hx (-betaF P0)
    nlinarith
  rcases l with ⟨k, i⟩
  cases k <;> simp only [maskP] <;> omega

theorem r1P_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (l : Leg P0) (j : Fin (P0.N + 1)) :
    (r1P pp v r l j).totalDegree ≤ legExp l + Constants.D + P0.n + 6 := by
  have ha : (tauP (pp.qap.A j)).totalDegree < Constants.D :=
    (tauP_degree _).trans_lt (hD.A_degree j)
  have hb : (tauP (pp.qap.B j)).totalDegree < Constants.D :=
    (tauP_degree _).trans_lt (hD.B_degree j)
  have hl := legP_degree l
  have hm := maskP_degree v l j
  have h₁ := totalDegree_add (C (r j)) (tauP (pp.qap.A j))
  have h₂ := totalDegree_sub (tauP (pp.qap.B j)) (xy j)
  have h₃ := totalDegree_mul (xs .Om22) (xs .eps)
  have h₄ := totalDegree_mul (xs .Om22 * xs .eps) (legP l)
  have h₅ := totalDegree_mul (xs .Om22 * xs .eps * legP l) (C (r j) + tauP (pp.qap.A j))
  have h₆ := totalDegree_mul (xs .Om22) (maskP v l j)
  have h₇ := totalDegree_add (xs .Om22 * xs .eps * legP l * (C (r j) + tauP (pp.qap.A j)))
    (xs .Om22 * maskP v l j)
  have h₈ := totalDegree_mul (xs .Om12) (xs .eps)
  have h₉ := totalDegree_mul (xs .Om12 * xs .eps) (legP l)
  have h₁₀ := totalDegree_mul (xs .Om12 * xs .eps * legP l) (tauP (pp.qap.B j) - xy j)
  have h₁₁ := totalDegree_sub
    (xs .Om22 * xs .eps * legP l * (C (r j) + tauP (pp.qap.A j)) + xs .Om22 * maskP v l j)
    (xs .Om12 * xs .eps * legP l * (tauP (pp.qap.B j) - xy j))
  have h₁₂ := totalDegree_mul (xs .zeta) (xs .zeta')
  have h₁₃ := totalDegree_mul (xs .zeta * xs .zeta') (xs .zeta4)
  have h₁₄ := totalDegree_mul (xs .zeta * xs .zeta' * xs .zeta4)
    (xs .Om22 * xs .eps * legP l * (C (r j) + tauP (pp.qap.A j)) + xs .Om22 * maskP v l j -
      xs .Om12 * xs .eps * legP l * (tauP (pp.qap.B j) - xy j))
  simp only [totalDegree_C, xs_degree, xy_degree] at h₁ h₂ h₃ h₆ h₈ h₁₂ h₁₃
  have hnum : 1 ≤ Constants.D := by decide
  dsimp only [r1P]
  omega

theorem gamma_z_degree (pp : PublicParams P0) (S : Relation P0)
    (hD : ValidQAP pp.qap S) (cl : Cell P0) :
    (gammaP cl).totalDegree + (tauP (pp.qap.zCell cl)).totalDegree ≤
      P0.n + Constants.D + 1 := by
  have hg := gammaP_degree cl
  have ht := tauP_degree (pp.qap.zCell cl)
  by_cases hc : IsKeyCell cl
  · have hz := zCell_degree pp S hD cl
    rcases cl with ⟨k, l, i⟩
    simp only [IsKeyCell] at hc
    rcases hc with ⟨hk, hl, hi⟩
    subst l
    simp only [legExp, LegKind.base, hi, mul_zero, add_zero, hk] at hg
    have hn : 2 ≤ P0.n := by decide
    omega
  · have hz := zCell_degree_nonkey pp S hD cl hc
    have he := cellExp_lt_n cl
    unfold cellExp at he
    have hpos : 1 ≤ Constants.D := by decide
    omega

theorem e2P_QB_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (σ : Sector) (cl : Cell P0) (j : Fin P0.Mq) :
    (e2P pp v r (some (.QB σ cl j))).totalDegree ≤ Constants.view_degree_d2 := by
  have hs := sectorP_degree σ
  have hg := gamma_z_degree pp S hD cl
  have h₁ := totalDegree_mul (sectorP σ) (xs .Om22)
  have h₂ := totalDegree_mul (sectorP σ * xs .Om22) (xs .zeta')
  have h₃ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta') (xs .zeta4)
  have h₄ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta' * xs .zeta4) (xs .eps)
  have h₅ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta' * xs .zeta4 * xs .eps) (gammaP cl)
  have h₆ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta' * xs .zeta4 * xs .eps * gammaP cl)
    (tauP (pp.qap.zCell cl))
  have h₇ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta' * xs .zeta4 * xs .eps * gammaP cl *
    tauP (pp.qap.zCell cl)) (xs .tau ^ (P0.E1 * j.val))
  simp only [xs_degree, xs_pow_degree] at h₁ h₂ h₃ h₄ h₇
  have hj : j.val ≤ P0.Mq - 1 := Nat.le_sub_one_of_lt j.isLt
  have hmul : P0.E1 * j.val ≤ P0.E1 * (P0.Mq - 1) := Nat.mul_le_mul_left _ hj
  have hnum : P0.n + Constants.D + 6 + P0.E1 * (P0.Mq - 1) ≤ Constants.view_degree_d2 := by decide
  simp only [e2P]
  omega

theorem e2P_RB_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (σ : Sector) (cl : Cell P0) (j : Fin P0.Wr) :
    (e2P pp v r (some (.RB σ cl j))).totalDegree ≤ Constants.view_degree_d2 := by
  have hs := sectorP_degree σ
  have hg := gammaP_degree cl
  have he := cellExp_lt_n cl
  unfold cellExp at he
  have hz := (tauP_degree pp.qap.Z0).trans (z0_degree pp S hD)
  have h₁ := totalDegree_mul (sectorP σ) (xs .Om22)
  have h₂ := totalDegree_mul (sectorP σ * xs .Om22) (xs .zeta)
  have h₃ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta) (xs .zeta4)
  have h₄ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta4) (xs .eps)
  have h₅ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta4 * xs .eps) (gammaP cl)
  have h₆ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta4 * xs .eps * gammaP cl) (tauP pp.qap.Z0)
  have h₇ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta4 * xs .eps * gammaP cl *
    tauP pp.qap.Z0) (xs .tau ^ (P0.U * P0.E1p * j.val))
  simp only [xs_degree, xs_pow_degree] at h₁ h₂ h₃ h₄ h₇
  have hj : j.val ≤ P0.Wr - 1 := Nat.le_sub_one_of_lt j.isLt
  have hmul : P0.U * P0.E1p * j.val ≤ P0.U * P0.E1p * (P0.Wr - 1) := Nat.mul_le_mul_left _ hj
  have hnum : P0.n + P0.N + 9 + P0.U * P0.E1p * (P0.Wr - 1) ≤ Constants.view_degree_d2 := by decide
  simp only [e2P]
  omega

theorem e2P_GB_degree (pp : PublicParams P0)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (σ : Sector) (g : CrossIdx) (e : Fin (2 * P0.n - 1)) :
    (e2P pp v r (some (.GB σ g e))).totalDegree ≤ Constants.view_degree_d2 := by
  have hs := sectorP_degree σ
  have hc := crossP_degree g
  have h₁ := totalDegree_mul (sectorP σ) (xs .Om22)
  have h₂ := totalDegree_mul (sectorP σ * xs .Om22) (xs .zeta)
  have h₃ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta) (xs .zeta')
  have h₄ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta') (xs .pi)
  have h₅ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta' * xs .pi) (crossP g)
  have h₆ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta' * xs .pi * crossP g)
    (xs .u ^ e.val)
  simp only [xs_degree, xs_pow_degree] at h₁ h₂ h₃ h₄ h₆
  have he := e.isLt
  have hnum : 2 * P0.n + 8 ≤ Constants.view_degree_d2 := by decide
  simp only [e2P]
  omega

theorem e2P_GM_degree (pp : PublicParams P0)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (σ : Sector) (s : TieIdx) (e : Fin (P0.n - 1)) :
    (e2P pp v r (some (.GM σ s e))).totalDegree ≤ Constants.view_degree_d2 := by
  have hs := sectorP_degree σ
  have ht := tieP_degree s
  have h₁ := totalDegree_mul (sectorP σ) (xs .Om22)
  have h₂ := totalDegree_mul (sectorP σ * xs .Om22) (xs .zeta)
  have h₃ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta) (xs .zeta')
  have h₄ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta') (xs .eps)
  have h₅ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta' * xs .eps) (xs .pi)
  have h₆ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta' * xs .eps * xs .pi) (tieP s)
  have h₇ := totalDegree_sub (xs .u ^ P0.n) (C (c0F P0))
  have h₈ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta' * xs .eps * xs .pi * tieP s)
    (xs .u ^ P0.n - C (c0F P0))
  have h₉ := totalDegree_mul (sectorP σ * xs .Om22 * xs .zeta * xs .zeta' * xs .eps * xs .pi * tieP s *
    (xs .u ^ P0.n - C (c0F P0))) (xs .u ^ e.val)
  simp only [xs_degree, xs_pow_degree, totalDegree_C] at h₁ h₂ h₃ h₄ h₅ h₇ h₉
  have he := e.isLt
  have hnum : 2 * P0.n + 8 ≤ Constants.view_degree_d2 := by decide
  simp only [e2P]
  omega

theorem e2P_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (r : Algebra.Vec (Fq P0) P0.N)
    (b : Option (G2Idx P0)) : (e2P pp v r b).totalDegree ≤ Constants.view_degree_d2 := by
  cases b with
  | none =>
    simp only [e2P]
    exact denomP_degree.trans (by decide)
  | some b =>
    cases b with
    | ZeroCoordinate σ l j =>
      have hs := sectorP_degree σ
      have hr := r1P_degree pp S hD v r l j
      have he := legExp_lt_n l
      have h := totalDegree_mul (sectorP σ) (r1P pp v r l j)
      have hnum : 2 * P0.n + Constants.D + 7 ≤ Constants.view_degree_d2 := by decide
      simp only [e2P]
      omega
    | R2 σ l j => exact e2P_R2_degree pp S hD v r σ l j
    | totR1 σ l =>
      have hs := sectorP_degree σ
      have he := legExp_lt_n l
      have hr : (∑ j, r1P pp v r l j).totalDegree ≤ legExp l + Constants.D + P0.n + 6 := by
        apply totalDegree_finsetSum_le
        intro j hj
        exact r1P_degree pp S hD v r l j
      have h := totalDegree_mul (sectorP σ) (∑ j, r1P pp v r l j)
      have hnum : 2 * P0.n + Constants.D + 7 ≤ Constants.view_degree_d2 := by decide
      simp only [e2P]
      omega
    | totR2 σ l => exact e2P_totR2_degree pp S hD v r σ l
    | QB σ cl j => exact e2P_QB_degree pp S hD v r σ cl j
    | RB σ cl j => exact e2P_RB_degree pp S hD v r σ cl j
    | SC σ l => exact e2P_SC_degree pp v r σ l
    | GB σ g e => exact e2P_GB_degree pp v r σ g e
    | GM σ s e => exact e2P_GM_degree pp v r σ s e

theorem kappaP_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S) :
    (kappaP pp).totalDegree ≤ Constants.D + 2 := by
  have h₁ := totalDegree_mul (piP 0) (xs .bE)
  have h₂ := totalDegree_mul (piP 0 * xs .bE) (tauP pp.qap.Lrho)
  have h₃ := piP_degree 0
  have h₄ := tauP_degree pp.qap.Lrho
  have h₅ := hD.Lrho_degree
  change pp.qap.Lrho.natDegree < Constants.D at h₅
  simp only [xs_degree] at h₁
  dsimp only [kappaP]
  omega

theorem list_degree_le {α : Type} (l : List α) (f : α → Poly) (d : ℕ)
    (hf : ∀ a ∈ l, (f a).totalDegree ≤ d) : (l.map f).sum.totalDegree ≤ d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    apply (totalDegree_add _ _).trans
    apply max_le
    · exact hf a (by simp)
    · apply ih
      intro b hb
      exact hf b (by simp [hb])

theorem e1P_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (a : Option (G1Idx P0)) : (e1P pp a).totalDegree ≤ Constants.view_degree_d1 := by
  have ha (i : Fin (P0.N + 1)) : (tauP (pp.qap.A i)).totalDegree < Constants.D :=
    (tauP_degree _).trans_lt (hD.A_degree i)
  have hp (k : Fin P0.K1) : (piP k.val).totalDegree ≤ 2 * k.val + 2 := piP_degree _
  have hk (k : Fin P0.K1) : k.val < Constants.K1 := k.isLt
  have hc : Constants.view_degree_d1 = 2 * Constants.K1 + Constants.D := by decide
  rw [hc]
  cases a with
  | none => simp [e1P]
  | some a =>
    cases a with
    | L1 k i =>
      simp only [e1P]
      have h := totalDegree_mul (piP k.val) (xy i)
      rw [xy_degree] at h
      have := hp k
      have := hk k
      have : 4 ≤ Constants.D := by decide
      omega
    | L2 k i =>
      simp only [e1P]
      have h₁ := totalDegree_mul (xs .Om12) (xy i)
      have h₂ := totalDegree_mul (xs .Om22) (tauP (pp.qap.A i))
      have h₃ := totalDegree_add (xs .Om12 * xy i) (xs .Om22 * tauP (pp.qap.A i))
      have h₄ := totalDegree_mul (piP k.val)
        (xs .Om12 * xy i + xs .Om22 * tauP (pp.qap.A i))
      simp only [xs_degree, xy_degree] at h₁ h₂
      have := hp k
      have := hk k
      have := ha i
      have : 4 ≤ Constants.D := by decide
      omega
    | totL1 k =>
      simp only [e1P]
      apply totalDegree_finsetSum_le
      intro i hi
      have h := totalDegree_mul (piP k.val) (xy i)
      rw [xy_degree] at h
      have := hp k
      have := hk k
      have : 4 ≤ Constants.D := by decide
      omega
    | totL2 k =>
      simp only [e1P]
      apply totalDegree_finsetSum_le
      intro i hi
      have h₁ := totalDegree_mul (xs .Om12) (xy i)
      have h₂ := totalDegree_mul (xs .Om22) (tauP (pp.qap.A i))
      have h₃ := totalDegree_add (xs .Om12 * xy i) (xs .Om22 * tauP (pp.qap.A i))
      have h₄ := totalDegree_mul (piP k.val)
        (xs .Om12 * xy i + xs .Om22 * tauP (pp.qap.A i))
      simp only [xs_degree, xy_degree] at h₁ h₂
      have := hp k
      have := hk k
      have := ha i
      have : 4 ≤ Constants.D := by decide
      omega
    | QP s =>
      simp only [e1P]
      have h := totalDegree_mul (xs .zeta) (xs .tau ^ s.val)
      simp only [xs_degree, xs_pow_degree] at h
      have hs := s.isLt
      have : P0.E1 ≤ Constants.D := by decide
      omega
    | RP s =>
      simp only [e1P]
      have h := totalDegree_mul (xs .zeta') (xs .tau ^ s.1.val)
      simp only [xs_degree, xs_pow_degree] at h
      have hs := s.1.isLt
      have : P0.U * P0.E1p ≤ Constants.D := by decide
      omega
    | GY i =>
      simp only [e1P]
      have h := totalDegree_mul (xs .zeta4) (xy i)
      simp only [xs_degree, xy_degree] at h
      have : 2 ≤ Constants.D := by decide
      omega

theorem differenceP_degree_of_e2 (pp : PublicParams P0) (S : Relation P0)
    (hD : ValidQAP pp.qap S) (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N)
    (r : Algebra.Vec (Fq P0) P0.N) (D : ExprT P0) (ι : Fq P0)
    (h2 : ∀ b, (e2P pp v r b).totalDegree ≤ Constants.view_degree_d2) :
    (differenceP pp v r D ι).totalDegree ≤ Constants.view_degree_total := by
  have ht := Degree.degree_bound.1
  have hsum : (((keys1 P0).map fun a => ((keys2 P0).map fun b =>
      C (D.1 (a, b)) * (e1P pp a * e2P pp v r b)).sum).sum).totalDegree ≤
      Constants.view_degree_total := by
    apply list_degree_le
    intro a ha
    apply list_degree_le
    intro b hb
    have h₁ := totalDegree_mul (e1P pp a) (e2P pp v r b)
    have h₂ := totalDegree_mul (C (D.1 (a,b))) (e1P pp a * e2P pp v r b)
    simp only [totalDegree_C, zero_add] at h₂
    have h₃ := e1P_degree pp S hD a
    have h₄ := h2 b
    omega
  have hk := kappaP_degree pp S hD
  have hd := denomP_degree
  have h₁ := totalDegree_mul (C D.2) denomP
  have h₂ := totalDegree_mul (C D.2 * denomP) (xs .alpha)
  have h₃ := totalDegree_mul (C D.2 * denomP * xs .alpha) (kappaP pp)
  have h₄ := totalDegree_mul (C ι) denomP
  have h₅ := totalDegree_mul (C ι * denomP) (kappaP pp)
  simp only [totalDegree_C, zero_add, xs_degree] at h₁ h₂ h₄
  have hnum : Constants.D + 8 ≤ Constants.view_degree_total := by decide
  have hadd := totalDegree_add
    (((keys1 P0).map fun a => ((keys2 P0).map fun b =>
      C (D.1 (a, b)) * (e1P pp a * e2P pp v r b)).sum).sum)
    (C D.2 * denomP * xs .alpha * kappaP pp)
  have hsub := totalDegree_sub
    ((((keys1 P0).map fun a => ((keys2 P0).map fun b =>
      C (D.1 (a, b)) * (e1P pp a * e2P pp v r b)).sum).sum) +
      C D.2 * denomP * xs .alpha * kappaP pp)
    (C ι * denomP * kappaP pp)
  dsimp only [differenceP]
  omega

end Praxis.Proofs.View.SZ
