import Praxis.Proofs.Reduction.Convert
import Praxis.Proofs.Reduction.Kernel.Null
import Praxis.Extractor
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Proofs.Injectivity.Rref
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Reduction

open Praxis.Algebra (Vec)

open Praxis.Proofs.Injectivity

theorem kernelVec_general {P : Params} [Fact (Nat.Prime P.q)]
    (F : FormMatrix P) (g : Fin 3 → Vec (Fq P) P.N) :
    ((∃ v, kernelVec F g = some v) ↔
        ∃ v ≠ 0, v ∈ Submodule.span (Fq P) (Set.range g) ∧ zLin (formVec F) v = 0 ∧ v 0 = 0) ∧
      ∀ v, kernelVec F g = some v →
        v ≠ 0 ∧ v ∈ Submodule.span (Fq P) (Set.range g) ∧ zLin (formVec F) v = 0 ∧ v 0 = 0 := by
  let R := rref [g 0, g 1, g 2]
  let B := R.map Prod.snd
  let b : Fin B.length → Vec (Fq P) P.N := fun i => B.getD i.val 0
  have hi : LinearIndependent (Fq P) b := by
    exact reduced_basis_independent R (rref_invariants [g 0, g 1, g 2]).1
      (rref_invariants [g 0, g 1, g 2]).2.2
  have hspan : Submodule.span (Fq P) (Set.range b) =
      Submodule.span (Fq P) (Set.range g) := by
    change Submodule.span (Fq P) (Set.range fun i : Fin (R.map Prod.snd).length =>
      (R.map Prod.snd).getD i.val 0) = _
    rw [indexed_rows_span, show rowSpan (R.map Prod.snd) = rowSpan [g 0, g 1, g 2] from
      rref_span [g 0, g 1, g 2]]
    apply congrArg (Submodule.span (Fq P))
    ext v
    constructor
    · intro hv
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] <;>
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  let ts : List (Vec (Fq P) P.N →ₗ[Fq P] Fq P) :=
    (List.finRange P.n).map (fun e => (LinearMap.proj e).comp (zLin (formVec F))) ++
      [LinearMap.proj 0]
  have ht (v : Vec (Fq P) P.N) :
      (∀ t ∈ ts, t v = 0) ↔ zLin (formVec F) v = 0 ∧ v 0 = 0 := by
    simp only [ts, List.forall_mem_append, List.forall_mem_map, List.mem_finRange,
      true_implies, List.forall_mem_singleton, LinearMap.comp_apply, LinearMap.proj_apply,
      funext_iff, Pi.zero_apply]
  have heqs : ts.map (fun t i => t (b i)) =
      ((List.finRange P.n).map fun e => fun l => Algebra.dot (formVec F e) (B.getD l.val 0)) ++
        [fun l => (B.getD l.val 0) 0] := by
    simp [ts, b, zLin, Matrix.mulVecLin_apply, Matrix.mulVec, Algebra.dot, dotProduct]
  have hs := combine_null_spec b hi ts
  dsimp only at hs
  rw [heqs] at hs
  have heval : (firstNull (rrefK
      (((List.finRange P.n).map fun e => fun l => Algebra.dot (formVec F e) (B.getD l.val 0)) ++
        [fun l => (B.getD l.val 0) 0]))).map (combine b) = kernelVec F g := by
    rfl
  rw [heval, hspan] at hs
  simp only [ht] at hs
  exact hs

theorem kernelVec_spec (F : FormMatrix P0) (g : Fin dimMax → Vec (Fq P0) P0.N) :
    ((∃ v, kernelVec F g = some v) ↔
        ∃ v ≠ 0, v ∈ Submodule.span (Fq P0) (Set.range g) ∧ zLin (formVec F) v = 0 ∧ v 0 = 0) ∧
      ∀ v, kernelVec F g = some v →
        v ≠ 0 ∧ v ∈ Submodule.span (Fq P0) (Set.range g) ∧ zLin (formVec F) v = 0 ∧ v 0 = 0 := by
  exact kernelVec_general F g

end Praxis.Proofs.Reduction
