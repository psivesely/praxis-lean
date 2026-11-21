import Praxis.Proofs.Ties.Division
import Praxis.KummerIrr
import Mathlib.Tactic.Module
import Praxis.Dec
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Ties

open Praxis.Algebra (Vec dot)

theorem P0_n : P0.n = 4608 := rfl

theorem P0_K1 : P0.K1 = 192 := rfl

theorem cellExp_P0 (c : Cell P0) :
    cellExp c = 2 * c.1.val + c.2.1.base + 384 * c.2.2.val := by
  simp only [cellExp, legExp, P0_K1]
  ring

theorem uCell_exp_lt (c : Cell P0) (_h : IsUCell c) : cellExp c < P0.n := by
  obtain ⟨a, X, b⟩ := c
  have ha : a.val < 192 := a.isLt
  have hb : b.val < 12 := b.isLt
  rw [cellExp_P0, P0_n]
  cases X <;> simp only [LegKind.base] <;> omega

theorem vCell_exp (c : Cell P0) (h : ¬ IsUCell c) :
    cellExp c < P0.n ∧ Even (cellExp c) := by
  obtain ⟨a, X, b⟩ := c
  have ha : a.val < 192 := a.isLt
  have hb : b.val < 12 := b.isLt
  have hX : X = .V := by simpa [IsUCell] using h
  subst hX
  rw [cellExp_P0, P0_n]
  simp only [LegKind.base]
  refine ⟨by omega, ⟨a.val + 192 * b.val, by omega⟩⟩

theorem beta_pow_m : betaF P0 ^ P0.m = -1 := Praxis.KummerIrr.beta_pow_m

section Evaluation

open Praxis.Algebra (Mat)

def coeffEval {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {n : ℕ} (p : KPoly M n) (u : R) : M := ∑ j : Fin n, u ^ j.val • p j

def rawEval {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (p : ℕ → M) (u : R) : M :=
  ∑ t ∈ Finset.range (2 * n - 1), u ^ t • p t

theorem rawEval_sub {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (n : ℕ) (p q : ℕ → M) (u : R) :
    rawEval n (p - q) u = rawEval n p u - rawEval n q u := by
  simp only [rawEval, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem rawEval_sub_apply {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (n : ℕ) (p q : ℕ → M) (u : R) :
    rawEval n (fun t => p t - q t) u = rawEval n p u - rawEval n q u :=
  rawEval_sub n p q u

theorem rawEval_rawMulMV {N n : ℕ} {F : Type*} [CommSemiring F]
    (hn : 0 < n) (A : KPoly (Mat F N) n) (b : KPoly (Vec F N) n) (u : F) :
    rawEval n (rawMulMV A b) u = (coeffEval A u).mulVec (coeffEval b u) := by
  classical
  simp only [rawEval, rawMulMV, Finset.smul_sum]
  rw [Finset.sum_comm]
  unfold coeffEval
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Matrix.smul_mulVec, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq, if_pos (by
    have := i.isLt
    have := j.isLt
    simp only [Finset.mem_range]
    omega)]
  rw [Matrix.mulVec_smul, smul_smul, pow_add]

theorem coeffEval_sigma {P : Params} {M : Type*} [AddCommMonoid M] [Module (Fq P) M]
    (a : KPoly M P.n) (s : ℕ) (u : Fq P) :
    coeffEval (sigma P s a) u = coeffEval a (betaF P ^ s * u) := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [sigma, frob, smul_smul, mul_pow, ← pow_mul]
  rw [mul_comm]

theorem rawEval_shiftLam {P : Params} (v : Fin P.n → Vec (Fq P) P.N)
    (M : Mat (Fq P) P.N) (a u : Fq P) (k : ℕ) (hk : k < P.n) :
    rawEval P.n (shiftLam v M a k) u = u ^ k • M.mulVec (lam v (a * u)) := by
  classical
  unfold rawEval
  have hb : ∀ j ∈ Finset.range P.n, k + j < 2 * P.n - 1 := by
    intro j hj
    have := Finset.mem_range.mp hj
    omega
  calc
    _ = ∑ j ∈ Finset.range P.n, u ^ (k + j) • shiftLam v M a k (k + j) := by
      rw [← Finset.sum_subset (s₁ := (Finset.range P.n).image (k + ·))]
      · rw [Finset.sum_image (by intro j _ j' _ h; exact Nat.add_left_cancel h)]
      · intro t ht
        rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
        exact Finset.mem_range.mpr (hb j hj)
      · intro t _ ht
        have h : ¬ (k ≤ t ∧ t - k < P.n) := by
          intro h
          apply ht
          exact Finset.mem_image.mpr ⟨t - k, Finset.mem_range.mpr h.2, by omega⟩
        simp only [shiftLam, dif_neg h, smul_zero]
    _ = u ^ k • M.mulVec (lam v (a * u)) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => u ^ (k + j) • shiftLam v M a k (k + j)) P.n,
        lam, Matrix.mulVec_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj' : j.val < P.n := j.isLt
      simp only [shiftLam, Nat.add_sub_cancel_left,
        dif_pos (show k ≤ k + j.val ∧ j.val < P.n from ⟨by omega, hj'⟩),
        Matrix.mulVec_smul, smul_smul, pow_add, mul_pow]
      congr 1
      ring

theorem coeffEval_fiber {F M ι : Type*} [CommSemiring F] [AddCommMonoid M]
    [Module F M] [Fintype ι] (n : ℕ) (p : ι → Prop) [DecidablePred p]
    (e : ι → ℕ) (w : ι → M) (a : F) (he : ∀ cl, p cl → e cl < n) :
    coeffEval (fun k : Fin n =>
      ∑ cl ∈ Finset.univ.filter (fun cl => p cl ∧ e cl = k.val), w cl) a =
        ∑ cl ∈ Finset.univ.filter p, a ^ e cl • w cl := by
  classical
  simp only [coeffEval, Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cl _
  by_cases hp : p cl
  · simp only [hp, true_and, if_true]
    rw [Finset.sum_eq_single (⟨e cl, he cl hp⟩ : Fin n)]
    · simp
    · intro j _ hj
      rw [if_neg (by intro h; exact hj (Fin.ext h.symm))]
    · simp
  · simp only [hp, false_and, if_false, Finset.sum_const_zero]

def Ueval {P : Params} (W : Stack P) (a : Fq P) : Mat (Fq P) P.N :=
  ∑ cl ∈ uCells, a ^ cellExp cl • W cl

def Veval {P : Params} (W : Stack P) (a : Fq P) : Mat (Fq P) P.N :=
  ∑ cl ∈ vCells, a ^ cellExp cl • W cl

theorem coeffEval_polyU {P : Params} (W : Stack P) (a : Fq P)
    (he : ∀ cl : Cell P, IsUCell cl → cellExp cl < P.n) :
    coeffEval (polyU W) a = Ueval W a :=
  coeffEval_fiber P.n IsUCell cellExp W a he

theorem vCell_even {P : Params} (cl : Cell P) (h : ¬ IsUCell cl) :
    Even (cellExp cl) := by
  rcases cl with ⟨k1, X, k2⟩
  have hX : X = .V := by simpa only [IsUCell, not_not] using h
  subst X
  refine ⟨k1.val + P.K1 * k2.val, ?_⟩
  simp only [cellExp, legExp, LegKind.base]
  ring

theorem polyV_fiber {P : Params} (W : Stack P) (k : Fin P.n) :
    polyV W k =
      ∑ cl ∈ Finset.univ.filter (fun cl : Cell P => ¬ IsUCell cl ∧ cellExp cl = k.val), W cl := by
  classical
  unfold polyV
  by_cases hk : k.val % 2 = 0
  · rw [if_pos hk]
    have he : 2 * (k.val / 2) = k.val := by omega
    simp only [stackV, he]
  · rw [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro cl hcl
    rcases (Finset.mem_filter.mp hcl).2 with ⟨hc, he⟩
    obtain ⟨j, hj⟩ := vCell_even cl hc
    omega

theorem coeffEval_polyV {P : Params} (W : Stack P) (a : Fq P)
    (he : ∀ cl : Cell P, ¬ IsUCell cl → cellExp cl < P.n) :
    coeffEval (polyV W) a = Veval W a := by
  simp only [coeffEval, polyV_fiber]
  exact coeffEval_fiber P.n (fun cl => ¬ IsUCell cl) cellExp W a he

theorem coeffEval_lam {P : Params} (v : Fin P.n → Vec (Fq P) P.N) (u : Fq P) :
    coeffEval v u = lam v u := rfl

theorem tiePoly_eval {P : Params} (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P)
    (hn : 0 < P.n) (hb : betaF P ^ P.m = -1)
    (hU : ∀ cl : Cell P, IsUCell cl → cellExp cl < P.n)
    (hV : ∀ cl : Cell P, ¬ IsUCell cl → cellExp cl < P.n) (u : Fq P) (s : TieIdx) :
    rawEval P.n (tiePoly v W s) u = match s with
    | .t1 => (Ueval W u).mulVec (lam v (-u)) -
        (Veval W u).mulVec (lam v (betaF P ^ (P.m - 1) * u))
    | .t2 => (Ueval W u).mulVec (lam v (-betaF P * u)) -
        (Ueval W (-betaF P * u)).mulVec (lam v (betaF P ^ (P.m - 1) * u))
    | .t3 => (Veval W u).mulVec (lam v (-betaF P * u)) -
        (Ueval W (-betaF P * u)).mulVec (lam v (-u)) := by
  have hb' : betaF P ^ (P.m + 1) = -betaF P := by rw [pow_succ, hb, neg_one_mul]
  cases s <;>
    simp only [tiePoly, rawEval_sub, rawEval_rawMulMV hn, coeffEval_sigma,
      coeffEval_polyU W _ hU, coeffEval_polyV W _ hV, coeffEval_lam,
      hb, hb', neg_one_mul]

theorem rawEval_sum {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (s : Finset ι) (p : ι → ℕ → M) (u : R) :
    rawEval n (fun t => ∑ cl ∈ s, p cl t) u = ∑ cl ∈ s, rawEval n (p cl) u := by
  simp only [rawEval, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem rawEval_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (p : ℕ → M) (u a : R) :
    rawEval n (fun t => a • p t) u = a • rawEval n p u := by
  simp only [rawEval, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact smul_comm _ _ _

theorem rawEval_neg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (n : ℕ) (p : ℕ → M) (u : R) :
    rawEval n (fun t => -p t) u = -rawEval n p u := by
  simp only [rawEval, smul_neg, Finset.sum_neg_distrib]

theorem rawEval_cellSum {P : Params} (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P)
    (S : Finset (Cell P)) (d : Cell P → Fq P) (a u : Fq P)
    (he : ∀ cl ∈ S, cellExp cl < P.n) :
    rawEval P.n (fun t => ∑ cl ∈ S, d cl • shiftLam v (W cl) a (cellExp cl) t) u =
      ∑ cl ∈ S, d cl • u ^ cellExp cl • (W cl).mulVec (lam v (a * u)) := by
  rw [rawEval_sum]
  apply Finset.sum_congr rfl
  intro cl hcl
  rw [rawEval_smul, rawEval_shiftLam v (W cl) a u _ (he cl hcl)]

theorem crossPoly_eval {P : Params} (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P)
    (hU : ∀ cl : Cell P, IsUCell cl → cellExp cl < P.n)
    (hV : ∀ cl : Cell P, ¬ IsUCell cl → cellExp cl < P.n) (u : Fq P) (g : CrossIdx) :
    rawEval P.n (crossPoly v W g) u = match g with
    | .c1eps =>
        (∑ cl ∈ uCells, cellTheta cl • u ^ cellExp cl • (W cl).mulVec (lam v (-u))) -
        ∑ cl ∈ vCells, cellTheta cl • u ^ cellExp cl •
          (W cl).mulVec (lam v (betaF P ^ (P.m - 1) * u))
    | .c2eps => ∑ cl ∈ uCells, cellTheta cl • u ^ cellExp cl •
        (W cl).mulVec (lam v (-betaF P * u))
    | .c3eps => ∑ cl ∈ vCells, cellTheta cl • u ^ cellExp cl •
        (W cl).mulVec (lam v (-betaF P * u))
    | .c2div => -∑ cl ∈ uCells, cellBetaLeg cl • u ^ cellExp cl •
        (W cl).mulVec (lam v (betaF P ^ (P.m - 1) * u))
    | .c3div => -∑ cl ∈ uCells, cellBetaLeg cl • u ^ cellExp cl • (W cl).mulVec (lam v (-u)) := by
  have hu : ∀ cl ∈ (uCells : Finset (Cell P)), cellExp cl < P.n :=
    fun cl h => hU cl (Finset.mem_filter.mp h).2
  have hv : ∀ cl ∈ (vCells : Finset (Cell P)), cellExp cl < P.n :=
    fun cl h => hV cl (Finset.mem_filter.mp h).2
  cases g <;>
    simp only [crossPoly, rawEval_sub_apply, rawEval_neg,
      rawEval_cellSum v W uCells _ _ u hu, rawEval_cellSum v W vCells _ _ u hv,
      neg_one_mul]

end Evaluation

section MaskExpansion

open Praxis.Algebra (Mat)

theorem maskScalar_U {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (pi eps beta u c1 c2 c3 : F) (k x : ℕ) (L0 L1 L2 : M) (heps : eps ≠ 0) :
    (pi * u ^ (2 * k) * (1 + eps * beta ^ (2 * k))) •
        (u ^ x • (c1 • L0 + c2 • L1) -
          (eps⁻¹ * (-beta * u) ^ x) • (c2 • L2 + c3 • L0)) =
      pi • (c1 • (u ^ (2 * k + x) • L0) +
        c2 • (u ^ (2 * k + x) • L1 - (-beta * u) ^ (2 * k + x) • L2) -
        c3 • ((-beta * u) ^ (2 * k + x) • L0) +
        (c1 * eps) • (beta ^ (2 * k) • u ^ (2 * k + x) • L0) +
        (c2 * eps) • (beta ^ (2 * k) • u ^ (2 * k + x) • L1) -
        (c2 / eps) • ((-beta) ^ x • u ^ (2 * k + x) • L2) -
        (c3 / eps) • ((-beta) ^ x • u ^ (2 * k + x) • L0)) := by
  have hb : (-beta) ^ (2 * k) = beta ^ (2 * k) := by
    rw [pow_mul, neg_sq, ← pow_mul]
  simp only [pow_add, mul_pow, hb]
  match_scalars <;> field_simp <;> ring

theorem maskScalar_V {F M : Type*} [CommRing F] [AddCommGroup M] [Module F M]
    (pi eps beta u c1 c3 : F) (k x : ℕ) (L1 L2 : M) :
    (pi * u ^ (2 * k) * (1 + eps * beta ^ (2 * k))) •
        (u ^ x • (c3 • L1 - c1 • L2)) =
      pi • (-(c1 • (u ^ (2 * k + x) • L2)) +
        c3 • (u ^ (2 * k + x) • L1) -
        (c1 * eps) • (beta ^ (2 * k) • u ^ (2 * k + x) • L2) +
        (c3 * eps) • (beta ^ (2 * k) • u ^ (2 * k + x) • L1)) := by
  simp only [pow_add]
  all_goals module

def Ucontrib {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P) (cl : Cell P) : Vec (Fq P) P.N :=
  let u := coin c .u
  let bu := -betaF P * u
  let L0 := (W cl).mulVec (lam v (-u))
  let L1 := (W cl).mulVec (lam v bu)
  let L2 := (W cl).mulVec (lam v (betaF P ^ (P.m - 1) * u))
  coin c .c1 • (u ^ cellExp cl • L0) +
    coin c .c2 • (u ^ cellExp cl • L1 - bu ^ cellExp cl • L2) -
    coin c .c3 • (bu ^ cellExp cl • L0) +
    crossVal c .c1eps • (cellTheta cl • u ^ cellExp cl • L0) +
    crossVal c .c2eps • (cellTheta cl • u ^ cellExp cl • L1) -
    crossVal c .c2div • (cellBetaLeg cl • u ^ cellExp cl • L2) -
    crossVal c .c3div • (cellBetaLeg cl • u ^ cellExp cl • L0)

def Vcontrib {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P) (cl : Cell P) : Vec (Fq P) P.N :=
  let u := coin c .u
  let L1 := (W cl).mulVec (lam v (-betaF P * u))
  let L2 := (W cl).mulVec (lam v (betaF P ^ (P.m - 1) * u))
  (-(coin c .c1 • (u ^ cellExp cl • L2))) +
    coin c .c3 • (u ^ cellExp cl • L1) -
    crossVal c .c1eps • (cellTheta cl • u ^ cellExp cl • L2) +
    crossVal c .c3eps • (cellTheta cl • u ^ cellExp cl • L1)

theorem cellMask_U {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P) (cl : Cell P)
    (hU : IsUCell cl) (heps : coin c .eps ≠ 0) :
    piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2) = coin c .pi • Ucontrib v W c cl := by
  have hm : legMask v c cl.2 =
      coin c .u ^ legExp cl.2 •
        (coin c .c1 • lam v (-coin c .u) + coin c .c2 • lam v (-betaF P * coin c .u)) -
      ((coin c .eps)⁻¹ * (-betaF P * coin c .u) ^ legExp cl.2) •
        (coin c .c2 • lam v (betaF P ^ (P.m - 1) * coin c .u) +
          coin c .c3 • lam v (-coin c .u)) := by
    cases h : cl.2.1 <;> simp only [legMask, h]
    exact (hU h).elim
  rw [hm]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_add]
  exact maskScalar_U (coin c .pi) (coin c .eps) (betaF P) (coin c .u)
    (coin c .c1) (coin c .c2) (coin c .c3) cl.1.val (legExp cl.2)
    ((W cl).mulVec (lam v (-coin c .u)))
    ((W cl).mulVec (lam v (-betaF P * coin c .u)))
    ((W cl).mulVec (lam v (betaF P ^ (P.m - 1) * coin c .u))) heps

theorem cellMask_V {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P) (cl : Cell P)
    (hV : ¬ IsUCell cl) :
    piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2) = coin c .pi • Vcontrib v W c cl := by
  have h : cl.2.1 = .V := not_not.mp hV
  simp only [legMask, h, Matrix.mulVec_smul, Matrix.mulVec_sub]
  exact maskScalar_V (coin c .pi) (coin c .eps) (betaF P) (coin c .u)
    (coin c .c1) (coin c .c3) cl.1.val (legExp cl.2)
    ((W cl).mulVec (lam v (-betaF P * coin c .u)))
    ((W cl).mulVec (lam v (betaF P ^ (P.m - 1) * coin c .u)))

theorem sum_tieIdx {M : Type*} [AddCommMonoid M] (f : TieIdx → M) :
    ∑ s, f s = f .t1 + f .t2 + f .t3 := by
  change ∑ s ∈ ({.t1, .t2, .t3} : Finset TieIdx), f s = _
  simp [add_assoc]

theorem sum_crossIdx {M : Type*} [AddCommMonoid M] (f : CrossIdx → M) :
    ∑ g, f g = f .c1eps + f .c2eps + f .c3eps + f .c2div + f .c3div := by
  change ∑ g ∈ ({.c1eps, .c2eps, .c3eps, .c2div, .c3div} : Finset CrossIdx), f g = _
  simp [add_assoc]

theorem mask_parts {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P)
    (heps : coin c .eps ≠ 0) :
    ∑ cl : Cell P, piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2) =
      coin c .pi • ((∑ cl ∈ uCells, Ucontrib v W c cl) + ∑ cl ∈ vCells, Vcontrib v W c cl) := by
  classical
  have hu : ∀ cl ∈ (uCells : Finset (Cell P)),
      piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2) = coin c .pi • Ucontrib v W c cl :=
    fun cl h => cellMask_U v W c cl (Finset.mem_filter.mp h).2 heps
  have hv : ∀ cl ∈ (vCells : Finset (Cell P)),
      piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2) = coin c .pi • Vcontrib v W c cl :=
    fun cl h => cellMask_V v W c cl (Finset.mem_filter.mp h).2
  calc
    _ = (∑ cl ∈ uCells, piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2)) +
        ∑ cl ∈ vCells, piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ IsUCell _).symm
    _ = (∑ cl ∈ uCells, coin c .pi • Ucontrib v W c cl) +
        ∑ cl ∈ vCells, coin c .pi • Vcontrib v W c cl := by
      rw [Finset.sum_congr rfl hu, Finset.sum_congr rfl hv]
    _ = _ := by simp only [smul_add, Finset.smul_sum]

theorem mask_contrib_sum {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P)
    (hn : 0 < P.n) (hb : betaF P ^ P.m = -1)
    (hU : ∀ cl : Cell P, IsUCell cl → cellExp cl < P.n)
    (hV : ∀ cl : Cell P, ¬ IsUCell cl → cellExp cl < P.n) :
    (∑ cl ∈ uCells, Ucontrib v W c cl) + (∑ cl ∈ vCells, Vcontrib v W c cl) =
      (∑ s : TieIdx, cTie c s • rawEval P.n (tiePoly v W s) (coin c .u)) +
      ∑ g : CrossIdx, crossVal c g • rawEval P.n (crossPoly v W g) (coin c .u) := by
  rw [sum_tieIdx, sum_crossIdx]
  simp only [tiePoly_eval v W hn hb hU hV, crossPoly_eval v W hU hV, cTie,
    Ueval, Veval, Matrix.sum_mulVec, Matrix.smul_mulVec, Ucontrib, Vcontrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.smul_sum]
  all_goals module

theorem mask_sum {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P)
    (hn : 0 < P.n) (hb : betaF P ^ P.m = -1)
    (hU : ∀ cl : Cell P, IsUCell cl → cellExp cl < P.n)
    (hV : ∀ cl : Cell P, ¬ IsUCell cl → cellExp cl < P.n) (heps : coin c .eps ≠ 0) :
    ∑ cl : Cell P, piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2) =
      coin c .pi • ((∑ s : TieIdx, cTie c s • rawEval P.n (tiePoly v W s) (coin c .u)) +
        ∑ g : CrossIdx, crossVal c g • rawEval P.n (crossPoly v W g) (coin c .u)) := by
  rw [mask_parts v W c heps, mask_contrib_sum v W c hn hb hU hV]

theorem dot_smul_right {F : Type*} [CommSemiring F] {N : ℕ}
    (y z : Vec F N) (a : F) : dot y (a • z) = a * dot y z := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_sum_right {F ι : Type*} [CommSemiring F] {N : ℕ}
    (y : Vec F N) (s : Finset ι) (z : ι → Vec F N) :
    dot y (∑ cl ∈ s, z cl) = ∑ cl ∈ s, dot y (z cl) := by
  simp only [dot, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mask_origin_gen {P : Params} [Fact (Nat.Prime P.q)]
    (v : Fin P.n → Vec (Fq P) P.N) (W : Stack P) (c : Coins P)
    (hn : 0 < P.n) (hb : betaF P ^ P.m = -1)
    (hU : ∀ cl : Cell P, IsUCell cl → cellExp cl < P.n)
    (hV : ∀ cl : Cell P, ¬ IsUCell cl → cellExp cl < P.n) (heps : coin c .eps ≠ 0) :
    ∑ cl : Cell P, piAt c cl.1.val * dot c.1 ((W cl).mulVec (legMask v c cl.2)) =
      coin c .pi * ∑ i : Fin (P.N + 1), c.1 i *
        ((∑ s : TieIdx, cTie c s *
            ∑ t ∈ Finset.range (2 * P.n - 1), coin c .u ^ t * tiePoly v W s t i) +
          ∑ g : CrossIdx, crossVal c g *
            ∑ t ∈ Finset.range (2 * P.n - 1), coin c .u ^ t * crossPoly v W g t i) := by
  calc
    _ = dot c.1 (∑ cl : Cell P, piAt c cl.1.val • (W cl).mulVec (legMask v c cl.2)) := by
      rw [dot_sum_right]
      simp only [dot_smul_right]
    _ = _ := by
      rw [mask_sum v W c hn hb hU hV heps, dot_smul_right]
      congr 1
      simp only [dot, rawEval, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end MaskExpansion

end Praxis.Proofs.Ties
