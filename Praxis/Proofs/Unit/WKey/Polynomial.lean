import Praxis.Proofs.Basic
import Praxis.Algebra.Probe.SZ
import Praxis.Forms
import Praxis.Grid
import Praxis.Kummer
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

noncomputable section

namespace Praxis.Proofs.Unit.WitnessKey

open Praxis.Algebra (Vec)

open scoped BigOperators

variable {P : Params} [Fact (Nat.Prime P.q)]

abbrev Idx (P : Params) := FormIndex P × Fin P.d

abbrev K (P : Params) := Fintype.card (Idx P)

abbrev Poly (P : Params) := MvPolynomial (Fin (K P)) (Fq P)

def idxEquiv (P : Params) : Idx P ≃ Fin (K P) := Fintype.equivFin _

def entry (i : FormIndex P) (j : Fin P.d) : Poly P :=
  MvPolynomial.X (idxEquiv P (i, j))

def coeff (i : FormIndex P) (j : ℕ) : Poly P :=
  if h : j < P.d then entry i ⟨j, h⟩ else 0

def productCoeff (i : FormIndex P) (v : Rq P) (j : ℕ) : Poly P :=
  if h : j < P.d then
    ∑ a : Fin P.d, ∑ b : Fin P.d,
      if a.val + b.val = j then entry i a * MvPolynomial.C (v b)
      else if a.val + b.val = j + P.d then -(entry i a * MvPolynomial.C (v b)) else 0
  else 0

def phiPoly (e : Fin P.n) (x : Vec (Fq P) P.N) : Poly P :=
  if e.val / P.d = 0 then MvPolynomial.C (if e.val % P.d = 0 then x 0 else 0)
  else if h : e.val / P.d - 1 < P.rows then
    MvPolynomial.C (x 0) * coeff (⟨e.val / P.d - 1, h⟩, none) (e.val % P.d) +
      ∑ j : Fin P.cols, productCoeff (⟨e.val / P.d - 1, h⟩, some j)
        (slotPoly x j) (e.val % P.d)
  else 0

def zPoly (x : Vec (Fq P) P.N) (e : Fin P.n) : Poly P :=
  ∑ c, phiPoly e (Pi.single c 1) * MvPolynomial.C (x c)

def rawPoly (x : Vec (Fq P) P.N) (t : ℕ) : Poly P :=
  ∑ i : Fin P.n, ∑ j : Fin P.n,
    if i.val + j.val = t then
      zPoly x i * (MvPolynomial.C (betaF P ^ ((P.m - 1) * j.val)) * zPoly x j)
    else 0

def weightPoly (x : Vec (Fq P) P.N) : Poly P :=
  rawPoly x 0 + MvPolynomial.C (c0F P) * rawPoly x P.n

def assignment (A : FormMatrix P) : Fin (K P) → Fq P :=
  fun k => A ((idxEquiv P).symm k).1 ((idxEquiv P).symm k).2

def oracleMap (seed : Seed P) : FormOracle P →+ (Fin (K P) → Fq P) where
  toFun HF := assignment (HF seed)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem oracleMap_surjective (seed : Seed P) : Function.Surjective (oracleMap seed) := by
  intro a
  refine ⟨fun _ i j => a (idxEquiv P (i, j)), ?_⟩
  funext k
  change a (idxEquiv P (((idxEquiv P).symm k).1, ((idxEquiv P).symm k).2)) = a k
  simp

theorem eval_entry (A : FormMatrix P) (i : FormIndex P) (j : Fin P.d) :
    MvPolynomial.eval (assignment A) (entry i j) = A i j := by
  simp [entry, assignment]

theorem eval_coeff (A : FormMatrix P) (i : FormIndex P) (j : ℕ) :
    MvPolynomial.eval (assignment A) (coeff i j) = rqCoeff (A i) j := by
  by_cases h : j < P.d <;> simp [coeff, rqCoeff, h, eval_entry]

theorem eval_productCoeff (A : FormMatrix P) (i : FormIndex P) (v : Rq P) (j : ℕ) :
    MvPolynomial.eval (assignment A) (productCoeff i v j) = rqCoeff (rqMul (A i) v) j := by
  by_cases h : j < P.d
  · simp only [productCoeff, rqCoeff, h, dif_pos, if_pos, rqMul, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp [eval_entry]
  · simp [productCoeff, rqCoeff, h]

theorem eval_phiPoly (A : FormMatrix P) (e : Fin P.n) (x : Vec (Fq P) P.N) :
    MvPolynomial.eval (assignment A) (phiPoly e x) = phi A e x := by
  by_cases h : e.val / P.d = 0
  · simp [phiPoly, phi, h]
  · by_cases h' : e.val / P.d - 1 < P.rows
    · simp [phiPoly, phi, h, h', eval_coeff, eval_productCoeff]
    · simp [phiPoly, phi, h, h']

theorem eval_zPoly (A : FormMatrix P) (x : Vec (Fq P) P.N) (e : Fin P.n) :
    MvPolynomial.eval (assignment A) (zPoly x e) = zOf (formVec A) x e := by
  simp [zPoly, zOf, formVec, Algebra.dot, eval_phiPoly]

theorem eval_rawPoly (A : FormMatrix P) (x : Vec (Fq P) P.N) (t : ℕ) :
    MvPolynomial.eval (assignment A) (rawPoly x t) =
      rawMul (zOf (formVec A) x) (sigma P (P.m - 1) (zOf (formVec A) x)) t := by
  simp only [rawPoly, rawMul, sigma, frob, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [eval_zPoly, smul_eq_mul]

theorem eval_weightPoly (A : FormMatrix P) (x : Vec (Fq P) P.N) (hn : 0 < P.n) :
    MvPolynomial.eval (assignment A) (weightPoly x) = wKey (formVec A) x := by
  simp [weightPoly, eval_rawPoly, wKey, Uw, kcoeff, kmul, reduceP, hn, smul_eq_mul]

theorem degree_coeff (i : FormIndex P) (j : ℕ) : (coeff i j).totalDegree ≤ 1 := by
  by_cases h : j < P.d <;> simp [coeff, h, entry, MvPolynomial.totalDegree_X]

theorem degree_productCoeff (i : FormIndex P) (v : Rq P) (j : ℕ) :
    (productCoeff i v j).totalDegree ≤ 1 := by
  classical
  by_cases h : j < P.d
  · simp only [productCoeff, h, if_pos]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro a _
    apply MvPolynomial.totalDegree_finsetSum_le
    intro b _
    have hd : (entry i a * MvPolynomial.C (v b)).totalDegree ≤ 1 := by
      have hh := MvPolynomial.totalDegree_mul (entry i a) (MvPolynomial.C (v b))
      simpa [entry, MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] using hh
    split_ifs <;> simpa [MvPolynomial.totalDegree_neg] using hd
  · simp [productCoeff, h]

theorem degree_phiPoly (e : Fin P.n) (x : Vec (Fq P) P.N) :
    (phiPoly e x).totalDegree ≤ 1 := by
  classical
  by_cases h : e.val / P.d = 0
  · simp [phiPoly, h]
  · by_cases h' : e.val / P.d - 1 < P.rows
    · simp only [phiPoly, h, if_false, h', dif_pos]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · have hh := MvPolynomial.totalDegree_mul (MvPolynomial.C (x 0))
          (coeff (⟨e.val / P.d - 1, h'⟩, none) (e.val % P.d))
        simp only [MvPolynomial.totalDegree_C, zero_add] at hh
        exact hh.trans (degree_coeff _ _)
      · apply MvPolynomial.totalDegree_finsetSum_le
        intro j _
        exact degree_productCoeff _ _ _
    · simp [phiPoly, h, h']

theorem degree_zPoly (x : Vec (Fq P) P.N) (e : Fin P.n) :
    (zPoly x e).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro c _
  have hh := MvPolynomial.totalDegree_mul (phiPoly e (Pi.single c 1)) (MvPolynomial.C (x c))
  simp only [MvPolynomial.totalDegree_C, add_zero] at hh
  exact hh.trans (degree_phiPoly _ _)

theorem degree_rawPoly (x : Vec (Fq P) P.N) (t : ℕ) :
    (rawPoly x t).totalDegree ≤ 2 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  have h1 := degree_zPoly x i
  have h2 := degree_zPoly x j
  have h3 := MvPolynomial.totalDegree_mul (MvPolynomial.C (betaF P ^ ((P.m - 1) * j.val)))
    (zPoly x j)
  have h4 := MvPolynomial.totalDegree_mul (zPoly x i)
    (MvPolynomial.C (betaF P ^ ((P.m - 1) * j.val)) * zPoly x j)
  simp only [MvPolynomial.totalDegree_C, zero_add] at h3
  split_ifs
  · omega
  · simp

theorem degree_weightPoly (x : Vec (Fq P) P.N) : (weightPoly x).totalDegree ≤ 2 := by
  unfold weightPoly
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact degree_rawPoly x 0
  · have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (c0F P)) (rawPoly x P.n)
    simp only [MvPolynomial.totalDegree_C, zero_add] at h
    exact h.trans (degree_rawPoly x P.n)

def onePoly : KPoly (Fq P) P.n := fun e => if e.val = 0 then 1 else 0

theorem zero_formVec (e : Fin P.n) :
    formVec (0 : FormMatrix P) e = if e.val = 0 then Pi.single 0 1 else 0 := by
  funext c
  by_cases he : e.val = 0
  · simp [formVec, phi, he, Pi.single_apply, eq_comm]
  · have hne : ¬ (e.val / P.d = 0 ∧ e.val % P.d = 0) := fun ⟨h1, h2⟩ =>
      he (by rw [← Nat.div_add_mod e.val P.d, h1, h2]; simp)
    simp only [formVec, phi, he, if_false, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all [rqCoeff, rqMul]

theorem zero_zOf (x : Vec (Fq P) P.N) (hx : x 0 = 1) :
    zOf (formVec (0 : FormMatrix P)) x = onePoly := by
  funext e
  by_cases he : e.val = 0
  · simp [zOf, zero_formVec, he, onePoly, Algebra.dot, Pi.single_apply, hx]
  · simp [zOf, zero_formVec, he, onePoly, Algebra.dot]

theorem sigma_onePoly (s : ℕ) : sigma P s (onePoly (P := P)) = onePoly := by
  funext e
  by_cases he : e.val = 0 <;> simp [sigma, frob, he, onePoly]

theorem raw_onePoly (hn : 0 < P.n) (t : ℕ) :
    rawMul (onePoly (P := P)) onePoly t = if t = 0 then 1 else 0 := by
  unfold rawMul
  rw [Finset.sum_eq_single ⟨0, hn⟩]
  · rw [Finset.sum_eq_single ⟨0, hn⟩]
    · simp [onePoly, eq_comm]
    · intro j _ hj
      have : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [onePoly, this]
    · simp
  · intro i _ hi
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [onePoly, this]
  · simp

theorem weight_zero_matrix (x : Vec (Fq P) P.N) (hx : x 0 = 1) (hn : 0 < P.n) :
    wKey (formVec (0 : FormMatrix P)) x = 1 := by
  simp [wKey, Uw, kcoeff, kmul, reduceP, hn, zero_zOf x hx, sigma_onePoly,
    raw_onePoly hn, Nat.ne_of_gt hn]

theorem weightPoly_ne_zero (x : Vec (Fq P) P.N) (hx : x 0 = 1) (hn : 0 < P.n) :
    weightPoly x ≠ 0 := by
  intro h
  have he := eval_weightPoly (0 : FormMatrix P) x hn
  rw [h, map_zero, weight_zero_matrix x hx hn] at he
  exact zero_ne_one he

end Praxis.Proofs.Unit.WitnessKey
