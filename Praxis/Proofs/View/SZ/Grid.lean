import Praxis.Proofs.View.Locus
import Praxis.Enc
import Praxis.Kummer
import Praxis.Params
import Praxis.QAP
import Praxis.Search
import Praxis.Setting

namespace Praxis.Proofs.View

open Classical

variable {P : Params} [Fact (Nat.Prime P.q)]

abbrev CoinVar (P : Params) := Fin (P.N + 1) ⊕ ScalarCoin

def coinVar (c : Coins P) : CoinVar P → Fq P := Sum.elim c.1 c.2.2

noncomputable def sampleSet (Dm : QAPData P) : CoinVar P → Finset (Fq P)
  | .inl _ => Finset.univ
  | .inr .tau => Finset.univ \ Finset.univ.image Dm.point
  | .inr .eps => Finset.univ \ insert 0 (Finset.univ.image
      (fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹))
  | .inr .Om12 => Finset.univ
  | .inr _ => Finset.univ.erase 0

theorem coinVar_valid (Dm : QAPData P) (c : Coins P) :
    coinVar c ∈ Fintype.piFinset (sampleSet Dm) ↔ ValidCoins Dm c := by
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    have ht := h (Sum.inr ScalarCoin.tau)
    have he := h (Sum.inr ScalarCoin.eps)
    simp only [sampleSet, coinVar, Sum.elim_inr, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_image, Finset.mem_insert, not_or, not_exists] at ht he
    refine ⟨?_, ?_, he.1, ?_⟩
    · intro k hk
      exact ht k (by simpa using hk.symm)
    · intro s hs
      have h' := h (Sum.inr s)
      cases s <;> simp [ScalarCoin.inUnits] at hs <;>
        simpa [sampleSet, coinVar] using h'
    · intro k hk
      exact he.2 k (by simpa using hk.symm)
  · rintro ⟨ht, hu, he, hk⟩ x
    cases x with
    | inl i => simp [sampleSet]
    | inr s =>
      cases s <;> simp only [sampleSet, coinVar, Sum.elim_inr, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_insert,
        Finset.mem_erase, not_or, not_exists, true_and, and_true]
      all_goals first | exact fun k h => ht k h.symm | exact ⟨he, fun k h => hk k h.symm⟩ |
        solve | apply hu; rfl

noncomputable def coinGridEquiv (Dm : QAPData P) :
    {c : Coins P // ValidCoins Dm c} ≃
      SearchSample P × {x : CoinVar P → Fq P // x ∈ Fintype.piFinset (sampleSet Dm)} where
  toFun c := (c.1.2.1, ⟨coinVar c.1, (coinVar_valid Dm c.1).2 c.2⟩)
  invFun z := ⟨(fun i => z.2.1 (.inl i), z.1, fun s => z.2.1 (.inr s)),
    (coinVar_valid Dm _).1 (by
      have hz := Fintype.mem_piFinset.mp z.2.2
      rw [Fintype.mem_piFinset]
      intro i
      cases i <;> exact hz _)⟩
  left_inv c := by cases c with | mk c hc => cases c with | mk y c => cases c; rfl
  right_inv z := by
    rcases z with ⟨r, ⟨x, hx⟩⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext i
      cases i <;> rfl

theorem sampleSet_card_lower (Dm : QAPData P) (d : ℕ)
    (hqap : Fintype.card (QAPIndex P) ≤ d) (hK : P.K1 + 1 ≤ d) (hD : 1 ≤ d)
    (i : CoinVar P) : P.q - d ≤ (sampleSet Dm i).card := by
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  have hcard : (Finset.univ : Finset (Fq P)).card = P.q := by simp [Fq, ZMod.card]
  cases i with
  | inl j =>
    simp only [sampleSet, hcard]
    exact Nat.sub_le _ _
  | inr s =>
    cases s <;> simp only [sampleSet]
    all_goals first
      | rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard]
        apply Nat.sub_le_sub_left
        exact Finset.card_image_le.trans hqap
      | rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard]
        apply Nat.sub_le_sub_left
        exact (Finset.card_insert_le _ _).trans ((Nat.add_le_add_right
          (Finset.card_image_le.trans_eq (Fintype.card_fin P.K1)) 1).trans hK)
      | rw [Finset.card_erase_of_mem (Finset.mem_univ _), hcard]
        exact Nat.sub_le_sub_left hD _
      | rw [hcard]
        exact Nat.sub_le _ _

end Praxis.Proofs.View
