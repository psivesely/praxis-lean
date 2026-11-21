import Praxis.Proofs.Basic
import Praxis.Constants
import Praxis.Enc
import Praxis.Kummer
import Praxis.Params
import Praxis.QAP
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open Classical

open OracleComp OracleSpec

variable {P : Params} [Fact (Nat.Prime P.q)]

noncomputable def scalarSet (Dm : QAPData P) : ScalarCoin → Finset (Fq P)
  | .tau => Finset.univ \ Dm.pointSet
  | .Om12 => Finset.univ
  | .eps => Finset.univ \ (insert 0 (Finset.univ.image
      (fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹)))
  | _ => Finset.univ \ {0}

theorem validCoins_iff_scalarSet (Dm : QAPData P) (c : Coins P) :
    ValidCoins Dm c ↔ ∀ s, c.2.2 s ∈ scalarSet Dm s := by
  constructor
  · intro h s
    rcases h with ⟨ht, hu, he, hk⟩
    cases s
    case tau =>
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hm
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
      exact ht k hk.symm
    case Om12 => simp [scalarSet]
    case eps =>
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hm
      rcases Finset.mem_insert.mp hm with hzero | hm
      · exact he hzero
      · obtain ⟨k, _, hk'⟩ := Finset.mem_image.mp hm
        exact hk k hk'.symm
    all_goals simpa [scalarSet] using hu _ rfl
  · intro h
    unfold ValidCoins
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      have ht := (Finset.mem_sdiff.mp (h .tau)).2
      exact ht (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩)
    · intro s hs
      have hh := h s
      cases s <;> simp only [ScalarCoin.inUnits, Bool.false_eq_true] at hs
      all_goals simpa [scalarSet] using hh
    · intro hz
      have he := (Finset.mem_sdiff.mp (h .eps)).2
      apply he
      exact Finset.mem_insert.mpr (Or.inl hz)
    · intro k hk
      have he := (Finset.mem_sdiff.mp (h .eps)).2
      apply he
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩))

theorem card_univ_sdiff_lower (s : Finset (Fq P)) (d : ℕ) (h : s.card ≤ d) :
    P.q - d ≤ (Finset.univ \ s).card := by
  have h' := Finset.le_card_sdiff s (Finset.univ : Finset (Fq P))
  rw [Finset.card_univ, ZMod.card] at h'
  omega

theorem scalarSet_card_lower (Dm : QAPData P)
    (hpoint : Fintype.card (QAPIndex P) ≤ P.D) (hK : P.K1 + 1 ≤ P.D)
    (hD : 1 ≤ P.D) (s : ScalarCoin) : P.q - P.D ≤ (scalarSet Dm s).card := by
  have hp : Dm.pointSet.card ≤ P.D := by
    exact (Finset.card_image_le.trans_eq (Finset.card_univ)).trans hpoint
  have he : (insert (0 : Fq P) (Finset.univ.image
      (fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹))).card ≤ P.D := by
    have hi := Finset.card_image_le (s := (Finset.univ : Finset (Fin P.K1)))
      (f := fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹)
    have hj := Finset.card_insert_le (0 : Fq P) (Finset.univ.image
      (fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹))
    simp only [Finset.card_univ, Fintype.card_fin] at hi
    omega
  cases s <;> simp only [scalarSet]
  case tau => exact card_univ_sdiff_lower _ _ hp
  case Om12 => simp only [Finset.card_univ, ZMod.card]; omega
  case eps => exact card_univ_sdiff_lower _ _ he
  all_goals exact card_univ_sdiff_lower _ _ (by simpa using hD)

theorem qapIndex_card : Fintype.card (QAPIndex P) = P.N + 2 + P.U * P.gatesMax := by
  simp only [QAPIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  rw [Nat.mul_comm P.gatesMax P.U]
  omega

theorem main_scalarSet_card_lower (Dm : QAPData P0) (s : ScalarCoin) :
    P0.q - P0.D ≤ (scalarSet Dm s).card := by
  apply scalarSet_card_lower Dm
  · rw [qapIndex_card]
    norm_num [P0, Params.main, Constants.N, Constants.U, Constants.gates_max, Constants.D]
  · norm_num [P0, Params.main, Constants.K1, Constants.D]
  · norm_num [P0, Params.main, Constants.D]

end Praxis.Proofs.Monitor
