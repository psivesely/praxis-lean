import Praxis.Proofs.Monitor.Recover.Helpers
import Praxis.Algebra.BilinearModel.Bilinear.SmallRoots

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

set_option maxHeartbeats 40000 in
theorem uniformSubtype_event {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) [SampleableType {x : α // x ∈ s}] (hs : s.Nonempty) (E : α → Prop) :
    Pr[fun x : {x : α // x ∈ s} => E x.1 | $ᵗ {x : α // x ∈ s}] =
      Pr[E | PMF.uniformOfFinset s hs] := by
  classical
  rw [probEvent_uniformSample, Algebra.Bilinear.prob_uniform_finset]
  have hc : Fintype.card {x : {x : α // x ∈ s} // E x.1} = (s.filter E).card := by
    let e : {x : {x : α // x ∈ s} // E x.1} ≃ {x : α // x ∈ s.filter E} :=
      { toFun := fun x => ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_coe _)
  have heq : (Finset.univ.filter fun x : {x : α // x ∈ s} => E x.1).card = (s.filter E).card := by
    rw [← Fintype.card_subtype (fun x : {x : α // x ∈ s} => E x.1)]
    exact hc
  rw [heq, Fintype.card_coe]

set_option maxHeartbeats 40000 in
theorem uniformGrid_roots {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (S : Fin n → Finset F)
    [SampleableType {x : Fin n → F // x ∈ Fintype.piFinset S}]
    (hS : ∀ i, (S i).Nonempty)
    (m : ℕ) (hm : 0 < m) (hmin : ∀ i, m ≤ (S i).card)
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    Pr[fun x : {x : Fin n → F // x ∈ Fintype.piFinset S} =>
      MvPolynomial.eval x.1 p = 0 | $ᵗ {x : Fin n → F // x ∈ Fintype.piFinset S}] ≤
        (p.totalDegree : ENNReal) / m := by
  classical
  calc
    _ = Pr[fun x => MvPolynomial.eval x p = 0 | Algebra.Bilinear.gridLaw S hS] :=
      uniformSubtype_event (Fintype.piFinset S) (Fintype.piFinset_nonempty.mpr hS)
        (fun x => MvPolynomial.eval x p = 0)
    _ ≤ _ := Algebra.Bilinear.small_roots_product_eval S hS m hm hmin p hp

noncomputable def gridReindexEquiv {F ι : Type} [Fintype F] [Fintype ι] [DecidableEq F] [DecidableEq ι]
    {n : ℕ} (e : ι ≃ Fin n) (S : ι → Finset F) :
    {x : ι → F // x ∈ Fintype.piFinset S} ≃
      {x : Fin n → F // x ∈ Fintype.piFinset (fun i => S (e.symm i))} where
  toFun x := ⟨fun i => x.1 (e.symm i), by
    rw [Fintype.mem_piFinset]
    intro i
    exact (Fintype.mem_piFinset.mp x.2) (e.symm i)⟩
  invFun x := ⟨fun i => x.1 (e i), by
    rw [Fintype.mem_piFinset]
    intro i
    simpa using (Fintype.mem_piFinset.mp x.2) (e i)⟩
  left_inv := by intro x; apply Subtype.ext; funext i; simp
  right_inv := by intro x; apply Subtype.ext; funext i; simp

theorem uniformGrid_roots_reindexed {F ι : Type} [Field F] [Fintype F] [Fintype ι]
    [DecidableEq F] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n) (S : ι → Finset F)
    [SampleableType {x : ι → F // x ∈ Fintype.piFinset S}]
    [SampleableType {x : Fin n → F // x ∈ Fintype.piFinset (fun i => S (e.symm i))}]
    (hS : ∀ i, (S i).Nonempty) (m : ℕ) (hm : 0 < m)
    (hmin : ∀ i, m ≤ (S i).card) (p : MvPolynomial ι F) (hp : p ≠ 0) :
    Pr[fun x : {x : ι → F // x ∈ Fintype.piFinset S} => MvPolynomial.eval x.1 p = 0 |
      $ᵗ {x : ι → F // x ∈ Fintype.piFinset S}] ≤ (p.totalDegree : ENNReal) / m := by
  classical
  let e' := gridReindexEquiv e S
  let p' := MvPolynomial.rename e p
  have hp' : p' ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.rename_injective e e.injective) (by simpa [p'] using h)
  have heval (x : {x : ι → F // x ∈ Fintype.piFinset S}) :
      MvPolynomial.eval (e' x).1 p' = MvPolynomial.eval x.1 p := by
    simp [p', e', gridReindexEquiv, MvPolynomial.eval_rename, Function.comp_def]
  have hlaw := evalSPMF_map_bijective_uniform_cross
    {x : ι → F // x ∈ Fintype.piFinset S} e' e'.bijective
  have hprob : Pr[fun x : {x : ι → F // x ∈ Fintype.piFinset S} => MvPolynomial.eval x.1 p = 0 |
      $ᵗ {x : ι → F // x ∈ Fintype.piFinset S}] =
      Pr[fun x : {x : Fin n → F // x ∈ Fintype.piFinset (fun i => S (e.symm i))} =>
        MvPolynomial.eval x.1 p' = 0 |
        $ᵗ {x : Fin n → F // x ∈ Fintype.piFinset (fun i => S (e.symm i))}] := by
    have hmap := probEvent_map ($ᵗ {x : ι → F // x ∈ Fintype.piFinset S}) e'
      (fun x => MvPolynomial.eval x.1 p' = 0)
    have hdist : Pr[fun x : {x : Fin n → F // x ∈ Fintype.piFinset (fun i => S (e.symm i))} =>
        MvPolynomial.eval x.1 p' = 0 | e' <$> ($ᵗ {x : ι → F // x ∈ Fintype.piFinset S})] =
      Pr[fun x : {x : Fin n → F // x ∈ Fintype.piFinset (fun i => S (e.symm i))} =>
        MvPolynomial.eval x.1 p' = 0 |
        $ᵗ {x : Fin n → F // x ∈ Fintype.piFinset (fun i => S (e.symm i))}] := by
      simp only [probEvent_def, hlaw]
    simpa only [Function.comp_def, heval] using hmap.symm.trans hdist
  rw [hprob]
  have h := uniformGrid_roots (fun i => S (e.symm i)) (fun i => hS (e.symm i))
    m hm (fun i => hmin (e.symm i)) p' hp'
  exact h.trans (ENNReal.div_le_div_right (by exact_mod_cast
    (MvPolynomial.totalDegree_rename_le e p)) _)

end Praxis.Proofs.Monitor
