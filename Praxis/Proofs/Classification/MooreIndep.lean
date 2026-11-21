import Praxis.Proofs.Classification.MooreSpan
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Coeff
import Praxis.Proofs.Classification.Moore
import Praxis.Params
import Praxis.Setting

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

theorem moore_columns_independent {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) :
    LinearIndependent (KummerField P0)
      (fun j : Fin d => fun i => toK (sigma P0 j.val (a i))) := by
  let M : Matrix (Fin d) (Fin d) (KummerField P0) := Matrix.of fun i j => toK (sigma P0 j.val (a i))
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (moore_spanning a ha)
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hM : M.mulVec c = 0 := by
    have heq : M.mulVec c = ∑ j, c j • (fun i => toK (sigma P0 j.val (a i))) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, Matrix.of_apply]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    exact heq.trans hc
  have hzero : c = 0 := hinj (hM.trans (Matrix.mulVec_zero M).symm)
  intro i
  exact congrFun hzero i

theorem moore_consecutive_independent {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) (s : ℕ) :
    LinearIndependent (KummerField P0)
      (fun j : Fin d => fun i => toK (sigma P0 (s + j.val) (a i))) := by
  have hli := ha.map' (sigmaLin s) (LinearMap.ker_eq_bot.mpr (sigma_injective s))
  have h := moore_columns_independent (fun i => sigma P0 s (a i)) hli
  simpa only [← sigma_add, Nat.add_comm _ s] using h

section Generic

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M] {d : ℕ}

theorem independent_two_relation (v : Fin d → M) (hli : LinearIndependent F v)
    (i j : Fin d) (hij : i ≠ j) (a b : F) (h : a • v i - b • v j = 0) : a = 0 := by
  classical
  let c : Fin d → F := Pi.single i a - Pi.single j b
  have hc : ∑ r, c r • v r = 0 := by
    simpa [c, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply,
      ite_smul, zero_smul] using h
  have hi := Fintype.linearIndependent_iff.mp hli c hc i
  simpa [c, Pi.single_apply, hij, Ne.symm hij] using hi

end Generic

end

end Praxis.Proofs.Classification
