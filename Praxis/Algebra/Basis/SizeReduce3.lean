import Praxis.Algebra.Basis.ElementaryModel
import Mathlib.Tactic.FinCases

namespace Praxis.Algebra.Basis

open Praxis.Algebra.Basis.ElementaryModel

theorem sizeReduce3 (hgram : Gram3Identities) : SizeReduce3 := by
  intro C hC
  have facts := hgram C hC
  obtain ⟨hdet1, _, _, hpot1, _, _, _, h21_1, _, _⟩ :=
    facts.shear21 (round (m21 C))
  have hn1 : (firstReduce C).det ≠ 0 := by
    simpa only [firstReduce, hdet1] using hC
  have facts1 := hgram (firstReduce C) hn1
  obtain ⟨hdet2, _, _, hpot2, _, _, _, h21_2, _, h32_2⟩ :=
    facts1.shear32 (round (m32 (firstReduce C)))
  have hn2 : (secondReduce C).det ≠ 0 := by
    simpa only [secondReduce, hdet2] using hn1
  have facts2 := hgram (secondReduce C) hn2
  obtain ⟨_, _, _, hpot3, _, _, _, h21_3, h31_3, h32_3⟩ :=
    facts2.shear31 (round (m31 (secondReduce C)))
  have hfinal : C * sizeReduceChange C =
      secondReduce C * shear 0 2 (round (m31 (secondReduce C))) := by
    simp only [sizeReduceChange, secondReduce, firstReduce, Matrix.mul_assoc]
  refine ⟨Or.inl ?_, ?_, ?_⟩
  · simp only [sizeReduceChange, Matrix.det_mul,
      facts.shear_det 0 1 _ (by decide), facts.shear_det 1 2 _ (by decide),
      facts.shear_det 0 2 _ (by decide), mul_one]
  · rw [hfinal, hpot3]
    change potential (firstReduce C * shear 1 2 (round (m32 (firstReduce C)))) = _
    rw [hpot2]
    exact hpot1
  · unfold SizeBounds3
    rw [hfinal, h21_3, h31_3, h32_3]
    change |m21 (firstReduce C * shear 1 2 (round (m32 (firstReduce C))))| ≤ _ ∧
      _ ∧ |m32 (firstReduce C * shear 1 2 (round (m32 (firstReduce C))))| ≤ _
    rw [h21_2, h32_2]
    change |m21 (C * shear 0 1 (round (m21 C)))| ≤ _ ∧ _
    rw [h21_1]
    exact ⟨abs_sub_round _, abs_sub_round _, abs_sub_round _⟩

end Praxis.Algebra.Basis
