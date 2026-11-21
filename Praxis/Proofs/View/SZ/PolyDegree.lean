import Praxis.Proofs.View.SZ.Model
import Praxis.Constants
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.QAP
import Praxis.Relation

namespace Praxis.Proofs.View.SZ

theorem qapIndex_card (P : Params) :
    Fintype.card (QAPIndex P) = (P.N + 1) + (1 + P.gatesMax * P.U) := by
  simp only [QAPIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, Fintype.card_prod]

theorem zPoly_degree {P : Params} [Fact (Nat.Prime P.q)] (Dm : QAPData P) :
    (zPoly Dm.pointSet Dm.rho).natDegree ≤ Fintype.card (QAPIndex P) - 1 := by
  have hmem : Dm.rho ∈ Dm.pointSet := by
    simp [QAPData.pointSet, QAPData.point]
  have hcard : Dm.pointSet.card ≤ Fintype.card (QAPIndex P) := Finset.card_image_le
  unfold zPoly
  calc
    (∏ p ∈ Dm.pointSet.erase Dm.rho, (Polynomial.X - Polynomial.C p)).natDegree ≤
        ∑ p ∈ Dm.pointSet.erase Dm.rho,
          (Polynomial.X - Polynomial.C p).natDegree := Polynomial.natDegree_prod_le _ _
    _ = (Dm.pointSet.erase Dm.rho).card := by simp
    _ ≤ Fintype.card (QAPIndex P) - 1 := by
      rw [Finset.card_erase_of_mem hmem]
      exact Nat.sub_le_sub_right hcard 1

theorem z_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S) :
    pp.qap.Z.natDegree ≤ Constants.D - 1 := by
  have h := zPoly_degree pp.qap
  have hc : Fintype.card (QAPIndex P0) = Constants.D := by rw [qapIndex_card]; decide
  rw [hc] at h
  rw [hD.Z_eq]
  exact h

theorem zCell_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S)
    (cl : Cell P0) : (pp.qap.zCell cl).natDegree ≤ Constants.D := by
  have hz := z_degree pp S hD
  unfold QAPData.zCell
  split
  · have h : (pp.qap.Z * (Polynomial.X - Polynomial.C pp.qap.rho)).natDegree ≤
        pp.qap.Z.natDegree + (Polynomial.X - Polynomial.C pp.qap.rho).natDegree :=
        Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_X_sub_C] at h
    have hpos : 1 ≤ Constants.D := by decide
    omega
  · omega

theorem zCell_degree_nonkey (pp : PublicParams P0) (S : Relation P0)
    (hD : ValidQAP pp.qap S) (cl : Cell P0) (hc : ¬ IsKeyCell cl) :
    (pp.qap.zCell cl).natDegree ≤ Constants.D - 1 := by
  simpa [QAPData.zCell, hc] using z_degree pp S hD

theorem z0Poly_degree {P : Params} [Fact (Nat.Prime P.q)] (Dm : QAPData P) :
    (z0Poly Dm.colPt Dm.rho).natDegree ≤ P.N + 2 := by
  unfold z0Poly
  have h : ((Polynomial.X - Polynomial.C Dm.rho) *
      ∏ j, (Polynomial.X - Polynomial.C (Dm.colPt j))).natDegree ≤
      (Polynomial.X - Polynomial.C Dm.rho).natDegree +
        (∏ j, (Polynomial.X - Polynomial.C (Dm.colPt j))).natDegree := Polynomial.natDegree_mul_le
  have hp := Polynomial.natDegree_prod_le Finset.univ
    (fun j => Polynomial.X - Polynomial.C (Dm.colPt j))
  simp at h hp
  omega

theorem z0_degree (pp : PublicParams P0) (S : Relation P0) (hD : ValidQAP pp.qap S) :
    pp.qap.Z0.natDegree ≤ P0.N + 2 := by
  rw [hD.Z0_eq]
  exact z0Poly_degree pp.qap

end Praxis.Proofs.View.SZ
