import Praxis.Proofs.Basic
import Praxis.KummerIrr
import Praxis.Proofs.Classification.Moore.Roots
import Praxis.Proofs.Classification.Moore.Bridge
import Praxis.Kummer
import Praxis.Params
import Praxis.Setting

namespace Praxis.Proofs.Classification

noncomputable def toK (a : KPoly (Fq P0) P0.n) : KummerField P0 :=
  AdjoinRoot.mk (KummerPoly P0) (∑ e : Fin P0.n, Polynomial.C (a e) * Polynomial.X ^ e.val)

theorem moore_spanning {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) :
    IsUnit (Matrix.of fun i j : Fin d => toK (sigma P0 j.val (a i))).det := by
  letI : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩
  have h := moore_det (fun i => vecToK (a i)) (vecToK_independent a ha)
  have hcard : Fintype.card (Fq P0) = P0.q := ZMod.card _
  rw [hcard] at h
  have hmat : (Matrix.of fun i j : Fin d => toK (sigma P0 j.val (a i))) =
      (Matrix.of fun i j : Fin d => vecToK (a i) ^ (P0.q ^ j.val)) := by
    ext i j
    change vecToK (sigma P0 j.val (a i)) = _
    exact vecToK_sigma j.val (a i)
  rw [hmat]
  exact h

end Praxis.Proofs.Classification
