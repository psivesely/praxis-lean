import Praxis.Proofs.Monitor.Stop.LeftDegree
import Praxis.Proofs.Monitor.Stop.RightPoly
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Monitor.Stop.Degree
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open MvPolynomial

noncomputable section

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem deg_scalar_le (s : ScalarCoin) : (scalarX s : MonPoly P).totalDegree ≤ 1 :=
  (degree_scalarX s).le

theorem deg_pow_le {a : MonPoly P} (k : ℕ) (ha : a.totalDegree ≤ 1) :
    (a ^ k).totalDegree ≤ k :=
  (MvPolynomial.totalDegree_pow a k).trans (by nlinarith)

theorem degree_lambdaPoly_le (v : Fin P.n → Algebra.Vec (Fq P) P.N) (s : MonPoly P)
    (j : Fin (P.N + 1)) (hs : s.totalDegree ≤ 1) : (lambdaPoly v s j).totalDegree ≤ P.n - 1 := by
  unfold lambdaPoly
  apply deg_sum_le
  intro e _
  have h := deg_mul_le (deg_pow_le e.val hs) (deg_C_le (P := P) (v e j))
  have := e.2
  omega

theorem degree_maskPoly_le (v : Fin P.n → Algebra.Vec (Fq P) P.N) (l : Leg P) (j : Fin (P.N + 1))
    (hleg : legExp l < P.n) : (maskPoly v l j).totalDegree ≤ 2 * P.n := by
  have hu : (scalarX .u : MonPoly P).totalDegree ≤ 1 := deg_scalar_le _
  have hb : (-C (betaF P) * scalarX .u : MonPoly P).totalDegree ≤ 1 := by
    have := deg_mul_le (a := -C (betaF P)) (b := (scalarX .u : MonPoly P)) (m := 0) (n := 1)
      (by simp) hu
    omega
  have ht : (C (betaF P ^ (P.m - 1)) * scalarX .u : MonPoly P).totalDegree ≤ 1 := by
    have := deg_mul_le (a := C (betaF P ^ (P.m - 1))) (b := (scalarX .u : MonPoly P)) (m := 0)
      (n := 1) (MvPolynomial.totalDegree_C _).le hu
    omega
  have hnu : (-(scalarX .u) : MonPoly P).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree_neg]; exact hu
  have hlb := degree_lambdaPoly_le v _ j hb
  have hlt := degree_lambdaPoly_le v _ j ht
  have hlu := degree_lambdaPoly_le v _ j hnu
  obtain ⟨kind, k⟩ := l
  have hpre : (scalarX .eps * scalarX .u ^ legExp (P := P) (kind, k) : MonPoly P).totalDegree ≤
      1 + legExp (P := P) (kind, k) := deg_mul_le (deg_scalar_le _) (deg_pow_le _ hu)
  have h4 : ((-C (betaF P) * scalarX .u) ^ legExp (P := P) (kind, k) : MonPoly P).totalDegree ≤
      legExp (P := P) (kind, k) := deg_pow_le _ hb
  have hc : ∀ (c : ScalarCoin) (s : MonPoly P), s.totalDegree ≤ 1 →
      (scalarX c * lambdaPoly v s j : MonPoly P).totalDegree ≤ 1 + (P.n - 1) :=
    fun c s hs => deg_mul_le (deg_scalar_le c) (degree_lambdaPoly_le v s j hs)
  cases kind
  · simp only [maskPoly]
    refine deg_sub_le (d := 2 * P.n) ?_ ?_
    · have := deg_mul_le hpre (deg_add_le (d := 1 + (P.n - 1))
        (hc .c1 _ hnu) (hc .c2 _ hb))
      omega
    · have := deg_mul_le h4 (deg_add_le (d := 1 + (P.n - 1))
        (hc .c2 _ ht) (hc .c3 _ hnu))
      omega
  · simp only [maskPoly]
    refine deg_sub_le (d := 2 * P.n) ?_ ?_
    · have := deg_mul_le hpre (deg_add_le (d := 1 + (P.n - 1))
        (hc .c1 _ hnu) (hc .c2 _ hb))
      omega
    · have := deg_mul_le h4 (deg_add_le (d := 1 + (P.n - 1))
        (hc .c2 _ ht) (hc .c3 _ hnu))
      omega
  · simp only [maskPoly]
    have := deg_mul_le hpre (deg_sub_le (d := 1 + (P.n - 1))
      (hc .c3 _ hb) (hc .c1 _ ht))
    omega

theorem deg_scalars4 (a b c d : ScalarCoin) :
    (scalarX a * scalarX b * scalarX c * scalarX d : MonPoly P).totalDegree ≤ 4 := by
  have := deg_mul_le (deg_mul_le (deg_mul_le (deg_scalar_le (P := P) a) (deg_scalar_le b))
    (deg_scalar_le c)) (deg_scalar_le d)
  omega

theorem deg_scalars5 (a b c d e : ScalarCoin) :
    (scalarX a * scalarX b * scalarX c * scalarX d * scalarX e : MonPoly P).totalDegree ≤ 5 := by
  have := deg_mul_le (deg_scalars4 (P := P) a b c d) (deg_scalar_le e)
  omega

theorem deg_sector5 (σ : Sector) (a b c d : ScalarCoin) :
    (sectorPoly σ * scalarX a * scalarX b * scalarX c * scalarX d : MonPoly P).totalDegree ≤ 5 := by
  have := deg_mul_le (deg_mul_le (deg_mul_le (deg_mul_le (degree_sectorPoly (P := P) σ)
    (deg_scalar_le a)) (deg_scalar_le b)) (deg_scalar_le c)) (deg_scalar_le d)
  omega

theorem degree_rightPoly_le (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (hD : 2 ≤ P.D) (hn : P.n ≤ P.D) (hleg : ∀ l : Leg P, legExp l < P.n)
    (hcell : ∀ c : Cell P, cellExp c < P.n)
    (hA : ∀ j, (pp.qap.A j).natDegree < P.D) (hB : ∀ j, (pp.qap.B j).natDegree < P.D)
    (hZc : ∀ c, (pp.qap.zCell c).natDegree ≤ P.D) (hZ0 : pp.qap.Z0.natDegree ≤ P.N + 2)
    (hRB : P.N + 2 + P.U * P.E1p * (P.Wr - 1) ≤ P.D + P.E1 * (P.Mq - 1))
    (b : Option (G2Idx P)) :
    (rightPoly pp v b).totalDegree ≤ P.D + P.E1 * (P.Mq - 1) + P.n + 7 := by
  have hlegp : ∀ l : Leg P, (legPoly l : MonPoly P).totalDegree ≤ P.n := by
    intro l
    have := degree_legPoly (P := P) l
    have := hleg l
    omega
  have hh2 : ∀ l j, (h2Poly pp l j).totalDegree ≤ P.D + P.n - 1 := by
    intro l j
    have := degree_h2Poly pp l j (P.D - 1) (by have := hB j; omega)
    have := hleg l
    omega
  have hgamma : ∀ c : Cell P, (gammaPoly c : MonPoly P).totalDegree ≤ P.n + 2 := by
    intro c
    have := degree_gammaPoly (P := P) c
    have := hcell c
    simp only [cellExp] at this
    omega
  have hR1 : ∀ σ l j, (rightR1Poly pp v σ l j).totalDegree ≤ P.D + P.n + 5 := by
    intro σ l j
    have hrx : (rX j : MonPoly P).totalDegree ≤ P.D - 1 := by
      have := degree_rX (P := P) j
      omega
    have hAj : (univarAtTau (pp.qap.A j)).totalDegree ≤ P.D - 1 :=
      (degree_univarAtTau _).trans (by have := hA j; omega)
    have ha := deg_mul_le (deg_mul_le (degree_deltaPoly (P := P)) (hlegp l))
      (deg_add_le hrx hAj)
    have hb := deg_mul_le (deg_scalars4 (P := P) .Om22 .zeta .zeta' .zeta4)
      (degree_maskPoly_le v l j (hleg l))
    have hc := deg_mul_le (deg_scalars5 (P := P) .Om12 .zeta .zeta' .zeta4 .eps) (hh2 l j)
    have hin := deg_sub_le (d := P.D + P.n + 4) (deg_add_le (ha.trans (by omega))
      (hb.trans (by omega))) (hc.trans (by omega))
    have := deg_mul_le (degree_sectorPoly (P := P) σ) hin
    unfold rightR1Poly
    omega
  have hR2 : ∀ σ l j, (rightR2Poly pp σ l j).totalDegree ≤ P.D + P.n + 5 := by
    intro σ l j
    have := deg_mul_le (deg_sector5 (P := P) σ .zeta .zeta' .zeta4 .eps) (hh2 l j)
    unfold rightR2Poly
    omega
  have hQB : ∀ σ c t, (rightQBPoly pp σ c t).totalDegree ≤
      P.D + P.E1 * (P.Mq - 1) + P.n + 7 := by
    intro σ c t
    have ht : ((scalarX .tau : MonPoly P) ^ (P.E1 * t.val)).totalDegree ≤ P.E1 * (P.Mq - 1) := by
      refine (deg_pow_le _ (deg_scalar_le _)).trans (Nat.mul_le_mul_left _ ?_)
      have := t.2
      omega
    have hz : (univarAtTau (pp.qap.zCell c)).totalDegree ≤ P.D :=
      (degree_univarAtTau _).trans (hZc c)
    have := deg_mul_le (deg_mul_le (deg_mul_le (deg_sector5 (P := P) σ .Om22 .zeta' .zeta4 .eps)
      (hgamma c)) hz) ht
    unfold rightQBPoly
    omega
  have hRBb : ∀ σ c t, (rightRBPoly pp σ c t).totalDegree ≤
      P.D + P.E1 * (P.Mq - 1) + P.n + 7 := by
    intro σ c t
    have ht : ((scalarX .tau : MonPoly P) ^ (P.U * P.E1p * t.val)).totalDegree ≤
        P.U * P.E1p * (P.Wr - 1) := by
      refine (deg_pow_le _ (deg_scalar_le _)).trans (Nat.mul_le_mul_left _ ?_)
      have := t.2
      omega
    have hz : (univarAtTau pp.qap.Z0).totalDegree ≤ P.N + 2 :=
      (degree_univarAtTau _).trans hZ0
    have := deg_mul_le (deg_mul_le (deg_mul_le (deg_sector5 (P := P) σ .Om22 .zeta .zeta4 .eps)
      (hgamma c)) hz) ht
    unfold rightRBPoly
    omega
  have hSC : ∀ σ l, (rightSCPoly σ l : MonPoly P).totalDegree ≤
      P.D + P.E1 * (P.Mq - 1) + P.n + 7 := by
    intro σ l
    have := deg_mul_le (deg_mul_le (degree_deltaPoly (P := P)) (degree_sectorPoly (P := P) σ))
      (hlegp l)
    unfold rightSCPoly
    omega
  have hcross : ∀ g : CrossIdx, (crossPoly g : MonPoly P).totalDegree ≤ 3 := by
    intro g
    have h1 := deg_scalar_le (P := P) .c1
    have h2 := deg_scalar_le (P := P) .c2
    have h3 := deg_scalar_le (P := P) .c3
    have he := deg_pow_le (a := (scalarX .eps : MonPoly P)) 2 (deg_scalar_le _)
    cases g <;> simp only [crossPoly]
    · have := deg_mul_le h1 he; omega
    · have := deg_mul_le h2 he; omega
    · have := deg_mul_le h3 he; omega
    · omega
    · omega
  have hGB : ∀ σ g e, (rightGBPoly σ g e : MonPoly P).totalDegree ≤
      P.D + P.E1 * (P.Mq - 1) + P.n + 7 := by
    intro σ g e
    have he : ((scalarX .u : MonPoly P) ^ e.val).totalDegree ≤ 2 * P.n - 2 := by
      refine (deg_pow_le _ (deg_scalar_le _)).trans ?_
      have := e.2
      omega
    have h5 := deg_mul_le (deg_mul_le (deg_sector5 (P := P) σ .Om22 .zeta .zeta' .pi) (hcross g)) he
    unfold rightGBPoly
    omega
  have hGM : ∀ σ s e, (rightGMPoly σ s e : MonPoly P).totalDegree ≤
      P.D + P.E1 * (P.Mq - 1) + P.n + 7 := by
    intro σ s e
    have he : ((scalarX .u : MonPoly P) ^ e.val).totalDegree ≤ P.n - 2 := by
      refine (deg_pow_le _ (deg_scalar_le _)).trans ?_
      have := e.2
      omega
    have hun : ((scalarX .u : MonPoly P) ^ P.n - C (c0F P)).totalDegree ≤ P.n :=
      deg_sub_le (deg_pow_le _ (deg_scalar_le _)) (by simp)
    have h7 := deg_mul_le (deg_mul_le (deg_mul_le (deg_mul_le (deg_sector5 (P := P) σ .Om22 .zeta
      .zeta' .eps) (deg_scalar_le (P := P) .pi)) (deg_scalar_le (P := P) (tieCoin s))) hun) he
    unfold rightGMPoly
    omega
  cases b with
  | none =>
    have := degree_deltaPoly (P := P)
    simp only [rightPoly]
    omega
  | some b =>
    cases b with
    | ZeroCoordinate σ l j => have := hR1 σ l j; simp only [rightPoly]; omega
    | R2 σ l j => have := hR2 σ l j; simp only [rightPoly]; omega
    | totR1 σ l =>
      simp only [rightPoly, rightTotR1Poly]
      exact (deg_sum_le _ _ (fun j _ => (hR1 σ l j))).trans (by omega)
    | totR2 σ l =>
      simp only [rightPoly, rightTotR2Poly]
      exact (deg_sum_le _ _ (fun j _ => (hR2 σ l j))).trans (by omega)
    | QB σ c t => exact hQB σ c t
    | RB σ c t => exact hRBb σ c t
    | SC σ l => exact hSC σ l
    | GB σ g e => exact hGB σ g e
    | GM σ s e => exact hGM σ s e

end

end Praxis.Proofs.Monitor
