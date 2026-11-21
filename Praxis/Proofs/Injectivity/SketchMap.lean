import Praxis.Proofs.Basic
import Praxis.Extractor
import Praxis.Grid
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra (Vec)

variable {P : Params} [Fact (Nat.Prime P.q)]

def stackMap (W : Stack P) : (Cell P → Vec (Fq P) P.N) →ₗ[Fq P] Vec (Fq P) P.N where
  toFun u := ∑ c, (W c).mulVec (u c)
  map_add' u v := by simp [Matrix.mulVec_add, Finset.sum_add_distrib]
  map_smul' a u := by simp [Matrix.mulVec_smul, Finset.smul_sum]

lemma stackMap_mem (W : Stack P) (u : Cell P → Vec (Fq P) P.N) :
    stackMap W u ∈ jointSpace W := by
  apply Submodule.sum_mem
  intro c _
  exact (le_iSup (fun c => LinearMap.range (W c).mulVecLin) c) ⟨u c, rfl⟩

lemma range_stackMap (W : Stack P) : LinearMap.range (stackMap W) = jointSpace W := by
  classical
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    exact stackMap_mem W u
  · apply iSup_le
    intro c
    rintro v ⟨u, rfl⟩
    refine ⟨Pi.single c u, ?_⟩
    change (∑ d, (W d).mulVec ((Pi.single c u : Cell P → Vec (Fq P) P.N) d)) = (W c).mulVec u
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]
    · simp

def jointSketchMap (W : Stack P) (σ : Sector) :
    Sketches P →ₗ[Fq P] (Fin 3 → jointSpace W) where
  toFun sk l := ⟨stackMap W (fun c => sk c l σ), stackMap_mem W _⟩
  map_add' sk sk' := by
    ext l i
    exact congrFun (map_add (stackMap W) (fun c => sk c l σ) (fun c => sk' c l σ)) i
  map_smul' a sk := by
    ext l i
    exact congrFun (map_smul (stackMap W) a (fun c => sk c l σ)) i

lemma jointSketchMap_surjective (W : Stack P) (σ : Sector) :
    Function.Surjective (jointSketchMap W σ) := by
  classical
  intro s
  have hs (l : Fin 3) : ∃ u, stackMap W u = (s l).val := by
    have hmem : (s l).val ∈ LinearMap.range (stackMap W) := by
      rw [range_stackMap]
      exact (s l).property
    exact hmem
  choose u hu using hs
  refine ⟨fun c l _ => u l c, ?_⟩
  funext l
  apply Subtype.ext
  exact hu l

def coordinateSketchMap (W : Stack P) (σ : Sector) {d : ℕ}
    (e : jointSpace W ≃ₗ[Fq P] (Fin d → Fq P)) :
    Sketches P →ₗ[Fq P] (Fin 3 → Fin d → Fq P) where
  toFun sk l := e (jointSketchMap W σ sk l)
  map_add' sk sk' := by funext l; simp only [map_add, Pi.add_apply]
  map_smul' a sk := by funext l; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

lemma coordinateSketchMap_surjective (W : Stack P) (σ : Sector) {d : ℕ}
    (e : jointSpace W ≃ₗ[Fq P] (Fin d → Fq P)) :
    Function.Surjective (coordinateSketchMap W σ e) := by
  intro s
  obtain ⟨sk, hsk⟩ := jointSketchMap_surjective W σ (fun l => e.symm (s l))
  refine ⟨sk, ?_⟩
  funext l
  change e (jointSketchMap W σ sk l) = s l
  rw [hsk]
  exact e.apply_symm_apply (s l)

lemma span_equiv_eq_top_iff {K V U : Type*} [Field K] [AddCommGroup V] [AddCommGroup U]
    [Module K V] [Module K U] {ι : Type*} (e : V ≃ₗ[K] U) (s : ι → V) :
    Submodule.span K (Set.range (fun i => e (s i))) = ⊤ ↔
      Submodule.span K (Set.range s) = ⊤ := by
  have hm : (Submodule.span K (Set.range s)).map e.toLinearMap =
      Submodule.span K (Set.range (fun i => e (s i))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have ht : (⊤ : Submodule K V).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact e.surjective
  rw [← hm, ← ht]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

end Praxis.Proofs.Injectivity
