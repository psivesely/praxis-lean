import Praxis.Proofs.Classification.Frame

namespace Praxis.Proofs.Classification

noncomputable section

section

variable {k : Type*} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    (V : Submodule k (I → k))

theorem fin_coordinate_dual_basis (i₀ : I) (h₀ : evalAt V i₀ ≠ 0) :
    ∃ d : ℕ, d + 1 = Module.finrank k V ∧
      ∃ (b : Module.Basis (Fin (d + 1)) k (Module.Dual k V)) (idx : Fin (d + 1) → I),
        idx 0 = i₀ ∧ ∀ j, b j = evalAt V (idx j) := by
  classical
  obtain ⟨J, hJ, b, j₀, idx, hidx₀, hb⟩ := exists_coordinate_dual_basis V i₀ h₀
  letI := hJ
  have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨j₀⟩
  let d := Fintype.card J - 1
  have hd : Fintype.card J = d + 1 := by dsimp [d]; omega
  let e₀ : J ≃ Fin (d + 1) := Fintype.equivFinOfCardEq hd
  let e : J ≃ Fin (d + 1) := e₀.trans (Equiv.swap (e₀ j₀) 0)
  have he : e j₀ = 0 := by simp [e]
  have he' : e.symm 0 = j₀ := (Equiv.symm_apply_eq e).mpr he.symm
  refine ⟨d, ?_, b.reindex e, fun j => idx (e.symm j), ?_, ?_⟩
  · rw [← hd, ← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
  · simpa only [he'] using hidx₀
  · intro j
    rw [Module.Basis.reindex_apply, hb]

def frameEquiv {d : ℕ} (b : Module.Basis (Fin d) k (Module.Dual k V)) :
    V ≃ₗ[k] (Fin d → k) :=
  (Module.evalEquiv k V).trans b.dualBasis.equivFun

theorem frameEquiv_apply {d : ℕ} (b : Module.Basis (Fin d) k (Module.Dual k V))
    (x : V) (j : Fin d) : frameEquiv V b x j = b j x := by
  simp only [frameEquiv, LinearEquiv.trans_apply, Module.Basis.dualBasis_equivFun,
    Module.evalEquiv_apply, Module.Dual.eval_apply]

end

end

end Praxis.Proofs.Classification
