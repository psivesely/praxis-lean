import Praxis.Proofs.Classification.Main
import Praxis.Proofs.ZeroCoordinate
import Praxis.Proofs.Injectivity.Rref
import Praxis.Extractor
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open Praxis.Algebra (Vec)

theorem jse_core (A : FormMatrix P0) (S : Relation P0) (hS : InShape P0 S) (W : Stack P0)
    (hW : PassingStack S (formVec A) W) (hW0 : W ≠ 0)
    (hdim : Module.finrank (Fq P0) (jointSpace W) ≤ dimMax)
    (hinj : jointSpace W ⊓ LinearMap.ker (zLin (formVec A)) = ⊥) (s : Fin dimMax → Vec (Fq P0) P0.N)
    (hs : Submodule.span (Fq P0) (Set.range s) = jointSpace W) :
    ∃ x, testSketches S s = some x ∧ IsWitness S x := by
  classical
  obtain ⟨xs, ρ, hxs, hcomb⟩ := Classification.classification A S hS W hW hdim hinj
  have hne : xs.Nonempty := by
    by_contra h
    have hx : xs = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hW0
    simpa [hx] using hcomb
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxV, hxSat⟩ := hxs x hx
  have hrows : rowSpan [s 0, s 1, s 2] = jointSpace W := by
    rw [← hs]
    unfold rowSpan
    congr 1
    ext v
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hcan : x ∈ candidates (rref [s 0, s 1, s 2]) := by
    apply mem_candidates_rref _ x (hrows.symm ▸ hxV) hxSat.1
    intro i
    exact Fin.cases (Or.inr hxSat.1) (fun j => hxSat.2.1 j) i
  have hsome : (testSketches S s).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨x, hcan, decide_eq_true hxSat⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨y, hy, ?_⟩
  exact of_decide_eq_true (List.find?_some (p := fun v => decide (Algebra.Sat S v)) hy)

theorem jse_expr (A : FormMatrix P0) (S : Relation P0) (hS : InShape P0 S) (D : ExprT P0)
    (hP : PassingStack S (formVec A) (markStack D)) (h0 : markStack D ≠ 0)
    (hdim : Module.finrank (Fq P0) (jointSpace (markStack D)) ≤ dimMax)
    (hinj : jointSpace (markStack D) ⊓ LinearMap.ker (zLin (formVec A)) = ⊥) (sk : Sketches P0)
    (hs : Submodule.span (Fq P0) (Set.range fun l : Fin dimMax => sketchesOf D sk l (markSector D)) =
      jointSpace (markStack D)) :
    testExpr S (sketchesOf D sk) ≠ none := by
  obtain ⟨x, hx, _⟩ := jse_core A S hS (markStack D) hP h0 hdim hinj
    (fun l => sketchesOf D sk l (markSector D)) hs
  cases hσ : markSector D with
  | plain =>
    simp only [hσ] at hx
    simp [testExpr, hx]
  | alpha =>
    simp only [hσ] at hx
    unfold testExpr
    cases testSketches S (fun l => sketchesOf D sk l .plain) <;> simp [hx]

end Praxis.Proofs.Injectivity
