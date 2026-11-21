import Praxis.Proofs.View.SZ.Law
import Praxis.Algebra.BilinearModel.Bilinear.SmallRoots

namespace Praxis.Proofs.View

open OracleComp OracleSpec

open Classical

theorem grid_root_bound {σ F : Type} [Fintype σ] [DecidableEq σ]
    [CommRing F] [IsDomain F] [DecidableEq F]
    (S : σ → Finset F) (m : ℕ) (hm : 0 < m) (hS : ∀ i, m ≤ (S i).card)
    (p : MvPolynomial σ F) (hp : p ≠ 0) :
    (((Fintype.piFinset S).filter (fun x => MvPolynomial.eval x p = 0)).card : ENNReal) /
        (Fintype.piFinset S).card ≤ (p.totalDegree : ENNReal) / m := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let T : Fin (Fintype.card σ) → Finset F := fun i => S (e.symm i)
  let q := MvPolynomial.rename e p
  have hq : q ≠ 0 := by
    intro h
    apply hp
    apply (MvPolynomial.rename_injective e e.injective)
    simpa [q] using h
  have hT : ∀ i, (T i).Nonempty := fun i => Finset.card_pos.mp (lt_of_lt_of_le hm (hS _))
  have h := Algebra.Bilinear.small_roots_product_eval T hT m hm (fun i => hS (e.symm i)) q hq
  rw [Algebra.Bilinear.gridLaw, Algebra.Bilinear.prob_uniform_finset] at h
  have hsize : (Fintype.piFinset S).card = (Fintype.piFinset T).card := by
    apply Finset.card_bij (fun x _ i => x (e.symm i))
    · intro x hx
      rw [Fintype.mem_piFinset] at hx ⊢
      exact fun i => hx (e.symm i)
    · intro x hx y hy hxy
      funext i
      have := congrFun hxy (e i)
      simpa using this
    · intro y hy
      refine ⟨fun i => y (e i), ?_, ?_⟩
      · rw [Fintype.mem_piFinset] at hy ⊢
        intro i
        simpa [T] using hy (e i)
      · funext i
        simp
  have hcount : ((Fintype.piFinset S).filter (fun x => MvPolynomial.eval x p = 0)).card =
      ((Fintype.piFinset T).filter (fun x => MvPolynomial.eval x q = 0)).card := by
    apply Finset.card_bij (fun x _ i => x (e.symm i))
    · intro x hx
      obtain ⟨hx, hz⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      constructor
      · rw [Fintype.mem_piFinset] at hx ⊢
        exact fun i => hx (e.symm i)
      · simpa [q, MvPolynomial.eval_rename, Function.comp_def] using hz
    · intro x hx y hy hxy
      funext i
      have := congrFun hxy (e i)
      simpa using this
    · intro y hy
      obtain ⟨hy, hz⟩ := Finset.mem_filter.mp hy
      refine ⟨fun i => y (e i), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · rw [Fintype.mem_piFinset] at hy ⊢
          intro i
          simpa [T] using hy (e i)
        · simpa [q, MvPolynomial.eval_rename, Function.comp_def] using hz
      · funext i
        simp
  rw [hsize, hcount]
  have hd : (q.totalDegree : ENNReal) ≤ (p.totalDegree : ENNReal) := by
    exact_mod_cast (MvPolynomial.totalDegree_rename_le e p)
  convert h.trans (ENNReal.div_le_div_right hd _) using 1
  all_goals try rfl
  congr 2
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter]

end Praxis.Proofs.View
