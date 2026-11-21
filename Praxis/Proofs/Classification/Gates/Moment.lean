import Praxis.Proofs.Classification.Gates.Algebra
import Praxis.Forms
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Relation
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification.GateMoment

open Praxis.Algebra (Vec Mat)

variable {K : Type*} [Field K] {N : ℕ}

noncomputable def moment (g : Algebra.Gate K N) : Mat K N →ₗ[K] K where
  toFun := Algebra.MomentGate g
  map_add' M L := by
    simp only [Algebra.MomentGate, Matrix.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
    ring
  map_smul' a M := by
    simp only [Algebra.MomentGate, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ (b c d : K), b*(a*c)*d = a*(b*c*d) by intros; ring,
      mul_assoc a]
    simp only [← Finset.mul_sum, mul_sub]

def defect (g : Algebra.Gate K N) (x : Vec K N) : K :=
  (∑ f, Algebra.dot (g.left f) x * Algebra.dot (g.right f) x) -
    x 0 * Algebra.dot g.linear x

lemma moment_square (g : Algebra.Gate K N) (x : Vec K N) :
    moment g (Matrix.vecMulVec x x) = defect g x := by
  change Algebra.MomentGate g (Matrix.vecMulVec x x) = _
  unfold Algebra.MomentGate defect Algebra.dot
  simp only [Matrix.vecMulVec_apply, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro f _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma cells (A : FormMatrix P0) (S : Relation P0) (W : Stack P0)
    (xs : Finset (Vec (Fq P0) P0.N)) (ρ : Vec (Fq P0) P0.N → Fq P0)
    (hW : W = ∑ x ∈ xs, ρ x • honestStack (formVec A) x)
    (hgates : ∀ c t, Algebra.MomentGate (S t) (W c) = 0) :
    ∀ t c, ∑ x ∈ xs, (ρ x * defect (S t) x) * weight (formVec A) x c = 0 := by
  intro t c
  have h : (moment (S t)) (W c) = 0 := hgates c t
  rw [hW] at h
  simp only [Finset.sum_apply, Pi.smul_apply, honestStack, map_sum, map_smul,
    smul_eq_mul, moment_square] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro x hx
  ring

end Praxis.Proofs.Classification.GateMoment
