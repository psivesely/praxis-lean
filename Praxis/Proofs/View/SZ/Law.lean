import Praxis.Proofs.View.SZ.Grid
import Praxis.Enc
import Praxis.Params
import Praxis.Search
import Praxis.Setting

namespace Praxis.Proofs.View

open OracleComp OracleSpec

open Classical

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem coinLaw_grid (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (E : (CoinVar P → Fq P) → Prop) :
    (letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
     Pr[fun c => E (coinVar c.1) | $ᵗ {c : Coins P // ValidCoins pp.qap c}]) =
      ((Fintype.piFinset (sampleSet pp.qap)).filter E).card /
        (Fintype.piFinset (sampleSet pp.qap)).card := by
  let G := {x : CoinVar P → Fq P // x ∈ Fintype.piFinset (sampleSet pp.qap)}
  let C := {c : Coins P // ValidCoins pp.qap c}
  let e : C ≃ SearchSample P × G := coinGridEquiv pp.qap
  let ee : {c : C // E (coinVar c.1)} ≃ SearchSample P × {x : G // E x.1} := {
    toFun c := ((e c.1).1, ⟨(e c.1).2, c.2⟩)
    invFun z := ⟨e.symm (z.1, z.2.1), by
      have h := z.2.2
      have hx : Sum.elim (fun i => z.2.1.1 (.inl i)) (fun s => z.2.1.1 (.inr s)) = z.2.1.1 := by
        funext i
        cases i <;> rfl
      simpa [e, coinGridEquiv, coinVar, hx] using h⟩
    left_inv c := by apply Subtype.ext; exact e.left_inv c.1
    right_inv z := by
      rcases z with ⟨r, ⟨x, hx⟩⟩
      apply Prod.ext
      · change (e (e.symm (r, x))).1 = r
        exact congrArg Prod.fst (e.right_inv (r, x))
      · apply Subtype.ext
        change (e (e.symm (r, x))).2 = x
        exact congrArg Prod.snd (e.right_inv (r, x)) }
  have hcard : Fintype.card C = Fintype.card (SearchSample P) * Fintype.card G := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hecard : Fintype.card {c : C // E (coinVar c.1)} =
      Fintype.card (SearchSample P) * Fintype.card {x : G // E x.1} := by
    rw [Fintype.card_congr ee, Fintype.card_prod]
  have hgcard : Fintype.card G = (Fintype.piFinset (sampleSet pp.qap)).card := by
    exact Fintype.card_coe _
  have hegc : Fintype.card {x : G // E x.1} =
      ((Fintype.piFinset (sampleSet pp.qap)).filter E).card := by
    let e' : {x : G // E x.1} ≃ {x : CoinVar P → Fq P //
        x ∈ (Fintype.piFinset (sampleSet pp.qap)).filter E} := {
      toFun x := ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
      invFun x := ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
      left_inv x := by cases x; rfl
      right_inv x := by cases x; rfl }
    rw [Fintype.card_congr e']
    exact Fintype.card_coe _
  have hs : (Fintype.card (SearchSample P) : ENNReal) ≠ 0 := by
    haveI : Nonempty (SearchSample P) := ⟨(Classical.choice
      (inferInstance : Nonempty {c : Coins P // ValidCoins pp.qap c})).1.2.1⟩
    exact_mod_cast Fintype.card_ne_zero
  change Pr[fun c : C => E (coinVar c.1) | letI := SampleableType.ofFintype C; $ᵗ C] = _
  rw [probEvent_uniformSample, ← Fintype.card_subtype, hecard, hcard, hgcard, hegc]
  simp only [Nat.cast_mul]
  exact ENNReal.mul_div_mul_left _ _ hs (ENNReal.natCast_ne_top _)

end Praxis.Proofs.View
