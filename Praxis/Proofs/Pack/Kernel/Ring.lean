import Praxis.Proofs.Basic
import Praxis.Packing.Coefficients
import Praxis.Forms
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Pack

open Praxis.Algebra (Vec dot)

section Ring

variable {P : Params} [Fact (1 < P.q)] (hd : P.d ≠ 0)

noncomputable def toRing (r : Rq P) : (msisRing P hd).Ring :=
  ∑ i : Fin P.d, AdjoinRoot.of (msisRing P hd).Phi (r i) *
    AdjoinRoot.root (msisRing P hd).Phi ^ i.val

theorem toRing_add (a b : Rq P) : toRing hd (a + b) = toRing hd a + toRing hd b := by
  unfold toRing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

theorem toRing_zero : toRing hd (0 : Rq P) = 0 := by
  simp [toRing]

theorem toRing_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Rq P) :
    toRing hd (∑ i ∈ s, f i) = ∑ i ∈ s, toRing hd (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using toRing_zero hd
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toRing_add, ih]

theorem root_pow_d : AdjoinRoot.root (msisRing P hd).Phi ^ P.d = -1 := by
  have h : AdjoinRoot.mk (msisRing P hd).Phi (msisRing P hd).Phi = 0 := AdjoinRoot.mk_self
  have e : AdjoinRoot.mk (msisRing P hd).Phi (msisRing P hd).Phi =
      AdjoinRoot.root (msisRing P hd).Phi ^ P.d + 1 := by
    conv_lhs => arg 2; change (Polynomial.X ^ P.d + Polynomial.C 1 : Polynomial (ZMod P.q))
    rw [map_add, map_pow, AdjoinRoot.mk_X, Polynomial.C_1, map_one]
  have h2 : AdjoinRoot.root (msisRing P hd).Phi ^ P.d + 1 = 0 := e ▸ h
  exact eq_neg_of_add_eq_zero_left h2

theorem key_sum (x : Fq P) (j k : Fin P.d) :
    ∑ i : Fin P.d, AdjoinRoot.of (msisRing P hd).Phi
        (if j.val + k.val = i.val then x
          else if j.val + k.val = i.val + P.d then -x else 0) *
      AdjoinRoot.root (msisRing P hd).Phi ^ i.val =
    AdjoinRoot.of (msisRing P hd).Phi x *
      AdjoinRoot.root (msisRing P hd).Phi ^ (j.val + k.val) := by
  have hj := j.isLt
  have hk := k.isLt
  by_cases h : j.val + k.val < P.d
  · rw [Finset.sum_eq_single (⟨j.val + k.val, h⟩ : Fin P.d)]
    · simp
    · intro i _ hne
      have : j.val + k.val ≠ i.val := fun e => hne (Fin.ext e.symm)
      have h2 : j.val + k.val ≠ i.val + P.d := by omega
      simp [this, h2]
    · simp
  · have hlt : j.val + k.val - P.d < P.d := by omega
    rw [Finset.sum_eq_single (⟨j.val + k.val - P.d, hlt⟩ : Fin P.d)]
    · have h1 : j.val + k.val ≠ j.val + k.val - P.d := by omega
      have h2 : j.val + k.val = j.val + k.val - P.d + P.d := by omega
      have h3 : AdjoinRoot.root (msisRing P hd).Phi ^ (j.val + k.val) =
          - AdjoinRoot.root (msisRing P hd).Phi ^ (j.val + k.val - P.d) := by
        conv_lhs => rw [h2, pow_add, root_pow_d hd]
        ring
      rw [h3]
      dsimp only
      rw [if_neg h1, if_pos h2, map_neg]
      ring
    · intro i _ hne
      have h1 : j.val + k.val ≠ i.val := by have := i.isLt; omega
      have h2 : j.val + k.val ≠ i.val + P.d := by
        intro e; apply hne; apply Fin.ext; simp only; omega
      simp [h1, h2]
    · simp

theorem toRing_mul (a b : Rq P) : toRing hd (rqMul a b) = toRing hd a * toRing hd b := by
  unfold toRing
  rw [Finset.sum_mul_sum]
  simp only [rqMul]
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [key_sum hd (a j * b k) j k]
  simp only [map_mul, pow_add]
  ring

theorem coords_symm_eq (c : Fin (msisRing P hd).Phi.natDegree → Fq P) :
    (msisRing P hd).coords.symm c =
      toRing hd (fun i : Fin P.d => c (Fin.cast (msisRing P hd).natDegree_eq.symm i)) := by
  unfold Algebra.MSISRing.coords toRing
  erw [Module.Basis.equivFun_symm_apply]
  refine Fintype.sum_equiv (finCongr (msisRing P hd).natDegree_eq) _ _ (fun i => ?_)
  simp [Algebra.smul_def, AdjoinRoot.powerBasis'_gen]

theorem embed_eq (w : Fin P.d → ℤ) :
    (msisRing P hd).embed w = toRing hd (fun t => ((w t : ℤ) : Fq P)) := by
  unfold Algebra.MSISRing.embed toRing
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]

end Ring

end Praxis.Proofs.Pack
