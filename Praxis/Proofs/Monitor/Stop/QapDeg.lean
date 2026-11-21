import Praxis.Proofs.Monitor.Stop.Coins
import Praxis.Constants
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.QAP
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open Polynomial

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem rho_mem_pointSet (Dm : QAPData P) : Dm.rho ∈ Dm.pointSet := by
  unfold QAPData.pointSet
  exact Finset.mem_image.2 ⟨.inr (.inl ()), Finset.mem_univ _, rfl⟩

theorem pointSet_card_le_main (Dm : QAPData P0) : Dm.pointSet.card ≤ P0.D := by
  have h : Dm.pointSet.card ≤ Fintype.card (QAPIndex P0) :=
    Finset.card_image_le.trans_eq Finset.card_univ
  refine h.trans ?_
  rw [qapIndex_card]
  norm_num [P0, Params.main, Constants.N, Constants.U, Constants.gates_max, Constants.D]

theorem Z_natDegree_le (Dm : QAPData P) (hZ : Dm.Z = zPoly Dm.pointSet Dm.rho)
    (hp : Dm.pointSet.card ≤ P.D) : Dm.Z.natDegree ≤ P.D - 1 := by
  rw [hZ]
  unfold zPoly
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have h1 : ∀ p ∈ Dm.pointSet.erase Dm.rho, (X - C p : Polynomial (Fq P)).natDegree ≤ 1 :=
    fun p _ => (natDegree_X_sub_C p).le
  refine (Finset.sum_le_sum h1).trans ?_
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem (rho_mem_pointSet Dm)]
  omega

theorem zCell_natDegree_le (Dm : QAPData P) (hZ : Dm.Z = zPoly Dm.pointSet Dm.rho)
    (hp : Dm.pointSet.card ≤ P.D) (hD : 1 ≤ P.D) (c : Cell P) :
    (Dm.zCell c).natDegree ≤ P.D := by
  have hz := Z_natDegree_le Dm hZ hp
  unfold QAPData.zCell
  split_ifs
  · refine (natDegree_mul_le).trans ?_
    rw [natDegree_X_sub_C]
    omega
  · omega

theorem Z0_natDegree_le (Dm : QAPData P) (hZ0 : Dm.Z0 = z0Poly Dm.colPt Dm.rho) :
    Dm.Z0.natDegree ≤ P.N + 2 := by
  rw [hZ0]
  unfold z0Poly
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_sub_C]
  have h2 : (∏ j : Fin (P.N + 1), (X - C (Dm.colPt j) : Polynomial (Fq P))).natDegree ≤
      P.N + 1 := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin (P.N + 1))),
        (X - C (Dm.colPt j) : Polynomial (Fq P)).natDegree ≤ 1 :=
      fun j _ => (natDegree_X_sub_C _).le
    refine (Finset.sum_le_sum h1).trans ?_
    simp
  omega

end Praxis.Proofs.Monitor
