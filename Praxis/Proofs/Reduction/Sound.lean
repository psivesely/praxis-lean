import Praxis.Proofs.Reduction.Kernel
import Praxis.Proofs.Pack
import Praxis.Proofs.ZeroCoordinate
import Praxis.Constants
import Praxis.Forms
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.Pack.Kernel
import Praxis.Proofs.Reduction.Convert
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Scheme
import Praxis.Setting
import Praxis.Algebra.Definitions.Forms
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Reduction

set_option maxRecDepth 4096

private theorem converted_solution (F : FormMatrix P0) (v : Algebra.Vec (Fq P0) P0.N)
    (w : Algebra.Vec ℤ P0.N) (hv : zLin (formVec F) v = 0) (hv0 : v 0 = 0)
    (hw : convertLIFT v = some w) :
    Algebra.IsMSISSolution (msisRing P0 main_d_ne_zero) P0.eta
      (chalOf main_d_ne_zero F) (packCore w) := by
  classical
  obtain ⟨hnz, ⟨a, ha, hm⟩, hb⟩ := convert_sound v w hw
  let w' : Algebra.Vec ℤ P0.N := Function.update w 0 0
  have hw0 : w' 0 = 0 := by simp [w']
  have hcast0 : (w 0 : Fq P0) = 0 := by rw [hm, hv0, mul_zero]
  have hcast : Algebra.castVec (p := P0.q) w' = Algebra.castVec w := by
    funext i
    by_cases hi : i = 0
    · subst i; simp [w', Algebra.castVec, hcast0]
    · simp [w', Algebra.castVec, hi]
  have hpack : packCore w' = packCore w := by
    funext c t
    unfold packCore
    split
    · simp [w']
    · rfl
  have hker : zLin (formVec F) (Algebra.castVec (p := P0.q) w') = 0 := by
    rw [hcast]
    have heq : Algebra.castVec (p := P0.q) w = a • v := by
      funext i
      exact hm i
    rw [heq, map_smul, hv, smul_zero]
  rw [← hpack]
  refine ⟨?_, ?_, ?_⟩
  · rw [Pack.packCore_eq]
    have hnz' : Algebra.castVec (p := Constants.q) w' ≠ 0 := by
      change Algebra.castVec (p := P0.q) w' ≠ 0
      rw [hcast]
      exact hnz
    exact (Pack.pack_nonzero w' hw0).mp hnz'
  · rw [hpack, Algebra.coeffNorm_le_iff]
    intro c t
    unfold packCore
    split
    · exact_mod_cast (by simpa only [Int.natCast_natAbs] using hb _ :
        ((w _).natAbs : ℤ) ≤ (P0.eta : ℤ))
    · simp
  · apply Pack.pack_kernel F w' hw0
    intro e _
    have he := congrFun hker e
    simpa [zLin, Matrix.mulVecLin_apply, Matrix.mulVec, Algebra.dot, dotProduct] using he

theorem red_sound (rv : RedView P0) (ωp : Assign P0) (ωs : Fin dimMax → Sector → Assign P0)
    (z : Algebra.CoeffVec P0.d P0.cols) (h : redOutput rv ωp ωs = some z) :
    Algebra.IsMSISSolution (msisRing P0 main_d_ne_zero) P0.eta
      (chalOf main_d_ne_zero rv.out.forms) z := by
  classical
  cases hm : monitor (monCtx rv ωp) rv.out.pv rv.state.tr rv.state.kdfLog with
  | running => simp only [redOutput, hm] at h; cases h
  | noStack => simp only [redOutput, hm] at h; cases h
  | stack D =>
    simp only [redOutput, hm] at h
    obtain ⟨w, hw, hz⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, hc, hv⟩ := Option.bind_eq_some_iff.mp hw
    have hk : zLin (formVec rv.out.forms) v = 0 ∧ v 0 = 0 := by
      unfold chooseVec at hc
      have hc' := (Option.orElse_eq_some _ _ _).mp hc
      rcases hc' with hp | ⟨_, hp⟩
      · exact ⟨(kernelVec_spec _ _).2 _ hp |>.2.2.1,
          (kernelVec_spec _ _).2 _ hp |>.2.2.2⟩
      · exact ⟨(kernelVec_spec _ _).2 _ hp |>.2.2.1,
          (kernelVec_spec _ _).2 _ hp |>.2.2.2⟩
    rw [← hz]
    exact converted_solution _ _ _ hk.1 hk.2 hv

end Praxis.Proofs.Reduction
