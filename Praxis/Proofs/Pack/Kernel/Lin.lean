import Praxis.Proofs.Basic
import Praxis.Packing.Coefficients
import Praxis.Forms
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Pack

open Praxis.Algebra (Vec dot)

section Lin

variable {P : Params}

theorem rqCoeff_add (a b : Rq P) (i : ℕ) : rqCoeff (a + b) i = rqCoeff a i + rqCoeff b i := by
  unfold rqCoeff
  split_ifs <;> simp

theorem rqCoeff_smul (c : Fq P) (a : Rq P) (i : ℕ) : rqCoeff (c • a) i = c * rqCoeff a i := by
  unfold rqCoeff
  split_ifs <;> simp

theorem slotPoly_add (x y : Vec (Fq P) P.N) (j : Fin P.cols) :
    slotPoly (x + y) j = slotPoly x j + slotPoly y j := by
  funext s
  unfold slotPoly
  by_cases h : 1 + P.d * j.val + s.val < P.N + 1
  · simp only [Pi.add_apply, dif_pos h]
  · simp only [Pi.add_apply, dif_neg h, add_zero]

theorem slotPoly_smul (c : Fq P) (x : Vec (Fq P) P.N) (j : Fin P.cols) :
    slotPoly (c • x) j = c • slotPoly x j := by
  funext s
  unfold slotPoly
  by_cases h : 1 + P.d * j.val + s.val < P.N + 1
  · simp only [Pi.smul_apply, dif_pos h]
  · simp only [Pi.smul_apply, dif_neg h, smul_zero]

theorem rqMul_add (a b b' : Rq P) : rqMul a (b + b') = rqMul a b + rqMul a b' := by
  funext i
  simp only [rqMul, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [mul_add] <;> ring

theorem rqMul_smul (a b : Rq P) (c : Fq P) : rqMul a (c • b) = c • rqMul a b := by
  funext i
  simp only [rqMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

theorem phi_add (A : FormMatrix P) (e : Fin P.n) (x y : Vec (Fq P) P.N) :
    phi A e (x + y) = phi A e x + phi A e y := by
  unfold phi
  split_ifs
  · simp
  · simp
  · simp only [slotPoly_add, rqMul_add, rqCoeff_add, Finset.sum_add_distrib, Pi.add_apply]
    ring
  · simp

theorem phi_smul (A : FormMatrix P) (e : Fin P.n) (c : Fq P) (x : Vec (Fq P) P.N) :
    phi A e (c • x) = c * phi A e x := by
  unfold phi
  split_ifs
  · simp
  · simp
  · simp only [slotPoly_smul, rqMul_smul, rqCoeff_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_add, Finset.mul_sum]
    ring_nf
  · simp

theorem phi_eq_dot (A : FormMatrix P) (e : Fin P.n) (x : Vec (Fq P) P.N) :
    phi A e x = dot (formVec A e) x := by
  let L : Vec (Fq P) P.N →ₗ[Fq P] Fq P :=
    { toFun := phi A e, map_add' := phi_add A e, map_smul' := phi_smul A e }
  have hx : x = ∑ c, x c • (Pi.single c 1 : Vec (Fq P) P.N) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have : phi A e x = L x := rfl
  rw [this]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  unfold dot formVec
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
  rfl

end Lin

end Praxis.Proofs.Pack
