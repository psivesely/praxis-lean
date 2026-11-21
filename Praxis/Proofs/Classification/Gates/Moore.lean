import Praxis.Proofs.Classification.Gates.Algebra
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Moore
import Praxis.Params

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification.GateAlgebra

lemma sum_contract {X R K : Type*} [Fintype R] [CommSemiring K]
    (xs : Finset X) (f : X → K) (u : X → R → K) (a : R → K) :
    (∑ r, (∑ x ∈ xs, f x * u x r) * a r) =
      ∑ x ∈ xs, f x * (∑ r, u x r * a r) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mul_sum, mul_assoc]

lemma expand_conjugate {d : ℕ} (a : Fin d → KPoly k P0.n)
    (u : Fin d → k) (s : ℕ) :
    toK (sigma P0 s (∑ r, u r • a r)) =
      ∑ r, emb (u r) * toK (sigma P0 s (a r)) := by
  have hh := map_sum (eval.comp (sigmaLin s)) (fun r => u r • a r) Finset.univ
  change toK (sigma P0 s (∑ r, u r • a r)) = _ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul]
  exact Algebra.smul_def (u r) (toK (sigma P0 s (a r)))

lemma moore_annihilate {d : ℕ} (a : Fin d → KPoly k P0.n)
    (ha : LinearIndependent k a) (s : ℕ) (g : Fin d → F)
    (hg : ∀ j : Fin d, ∑ r, g r * toK (sigma P0 (s+j.val) (a r)) = 0) : g = 0 := by
  let a' : Fin d → KPoly k P0.n := fun r => sigma P0 s (a r)
  have ha' : LinearIndependent k a' :=
    ha.map' (sigmaLin s) (LinearMap.ker_eq_bot.mpr (sigma_injective s))
  let M : Matrix (Fin d) (Fin d) F :=
    Matrix.of fun i j => toK (sigma P0 j.val (a' i))
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (moore_spanning a' ha')
  have hz : Matrix.vecMul g M = Matrix.vecMul 0 M := by
    funext j
    simpa only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, a', sigma_add,
      Nat.add_comm j.val s, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using hg j
  exact Matrix.vecMul_injective_of_isUnit hM hz

lemma two_moore {X : Type*} {d : ℕ} (a : Fin d → KPoly k P0.n)
    (ha : LinearIndependent k a) (hd : d ≤ 3) (xs : Finset X)
    (u : X → Fin d → k) (e : X → k)
    (h : ∀ r : Fin 3, ∑ x ∈ xs, emb (e x) * toK (∑ i, u x i • a i) *
      toK (sigma P0 (P0.m-1+r.val) (∑ i, u x i • a i)) = 0) :
    ∀ i j, ∑ x ∈ xs, e x * u x i * u x j = 0 := by
  let g : Fin d → F := fun i =>
    ∑ x ∈ xs, (emb (e x) * toK (∑ r, u x r • a r)) * emb (u x i)
  have hg : g = 0 := by
    apply moore_annihilate a ha (P0.m-1) g
    intro j
    change (∑ r, (∑ x ∈ xs,
      (emb (e x) * toK (∑ r, u x r • a r)) * emb (u x r)) *
      toK (sigma P0 (P0.m-1+j.val) (a r))) = 0
    rw [sum_contract]
    simp_rw [← expand_conjugate]
    exact h ⟨j.val, lt_of_lt_of_le j.isLt hd⟩
  intro i
  have hconj (s : ℕ) : ∑ x ∈ xs, emb (e x) *
      toK (sigma P0 s (∑ r, u x r • a r)) * emb (u x i) = 0 := by
    have hgi : g i = 0 := congrFun hg i
    have hh := congrArg (conjugate s) hgi
    simpa only [g, map_sum, map_mul, map_zero, conjugate_emb, conjugate_toK] using hh
  let q : Fin d → F := fun r => ∑ x ∈ xs, (emb (e x) * emb (u x i)) * emb (u x r)
  have hq : q = 0 := by
    apply moore_annihilate a ha 0 q
    intro j
    change (∑ r, (∑ x ∈ xs, (emb (e x) * emb (u x i)) * emb (u x r)) *
      toK (sigma P0 (0+j.val) (a r))) = 0
    rw [sum_contract]
    simp_rw [← expand_conjugate, zero_add]
    convert hconj j.val using 1
    apply Finset.sum_congr rfl
    intro x hx
    ring
  intro j
  apply (algebraMap k F).injective
  rw [map_zero, map_sum]
  simpa only [q, map_mul, Pi.zero_apply] using congrFun hq j

end Praxis.Proofs.Classification.GateAlgebra
