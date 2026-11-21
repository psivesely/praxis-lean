import Praxis.Proofs.Reduction.Sound
import Praxis.Proofs.Basic
import Praxis.Proofs.Reduction.Complete.Delta
import Praxis.Proofs.Reduction.Complete.Locus
import Praxis.Proofs.Reduction.Complete.Polynomial
import Praxis.Proofs.Lift.Convert
import Praxis.Proofs.Differences
import Praxis.Domain
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.ZeroCoordinate
import Praxis.Proofs.Reduction.Kernel
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Reduction

theorem mark_kernel_exists (rv : RedView P0) (ωs : Fin dimMax → Sector → Assign P0)
    (D : ExprT P0)
    (hker : jointSpace (markStack D) ⊓ LinearMap.ker (zLin (formVec rv.out.forms)) ≠ ⊥)
    (hrec : gradSpan rv.pp ωs D (markSector D) = jointSpace (markStack D)) :
    ∃ v, kernelVec rv.out.forms (fun l => rGrad rv.pp (ωs l (markSector D)) D (markSector D)) = some v := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hvs : v ∈ gradSpan rv.pp ωs D (markSector D) := by
    rw [hrec]
    exact hv.1
  have hvz : zLin (formVec rv.out.forms) v = 0 := LinearMap.mem_ker.mp hv.2
  have hv00 : v 0 = 0 := ZeroCoordinate.kernel_zero_coordinate rv.out.forms v hvz
  apply (kernelVec_spec _ _).1.mpr
  exact ⟨v, hv0, hvs, hvz, hv00⟩

set_option maxHeartbeats 10000 in
theorem output_of_selected {P : Params} [Fact (Nat.Prime P.q)] [NeZero P.q]
    (rv : RedView P) (ωp : Assign P)
    (ωs : Fin 3 → Sector → Assign P) (D : ExprT P)
    (hmon : monitor (monCtx rv ωp) rv.out.pv rv.state.tr rv.state.kdfLog = MonStop.stack D)
    (v : Algebra.Vec (Fq P) P.N) (hchoose : chooseVec rv ωs D = some v)
    (hconv : (convertLIFT v).isSome) :
    (redOutput rv ωp ωs).isSome := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hconv
  unfold redOutput
  rw [hmon]
  simp only [hchoose, Option.bind_some, hz, Option.map_some, Option.isSome_some]

theorem choose_marked {P : Params} [Fact (Nat.Prime P.q)]
    (rv : RedView P) (ωs : Fin 3 → Sector → Assign P) (D : ExprT P)
    (v : Algebra.Vec (Fq P) P.N)
    (hmark : kernelVec rv.out.forms (fun l => rGrad rv.pp (ωs l (markSector D)) D (markSector D)) = some v)
    (hselect : markSector D = .plain ∨
      kernelVec rv.out.forms (fun l => rGrad rv.pp (ωs l .plain) D .plain) = none) :
    chooseVec rv ωs D = some v := by
  rcases hselect with hm | hn
  · rw [hm] at hmark
    dsimp only [chooseVec]
    rw [hmark]
    rfl
  · cases hm : markSector D with
    | plain =>
      rw [hm, hn] at hmark
      cases hmark
    | alpha =>
      rw [hm] at hmark
      dsimp only [chooseVec]
      rw [hn, hmark]
      rfl

theorem kernel_none_of_grads_zero (rv : RedView P0)
    (ωs : Fin dimMax → Sector → Assign P0) (D : ExprT P0) (σ : Sector)
    (hzero : ∀ l, rGrad rv.pp (ωs l σ) D σ = 0) :
    kernelVec rv.out.forms (fun l => rGrad rv.pp (ωs l σ) D σ) = none := by
  cases hk : kernelVec rv.out.forms (fun l => rGrad rv.pp (ωs l σ) D σ) with
  | none => rfl
  | some v =>
    have hv := (kernelVec_spec rv.out.forms _).2 v hk
    have hspan : Submodule.span (Fq P0) (Set.range (fun l => rGrad rv.pp (ωs l σ) D σ)) ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨l, rfl⟩
      change rGrad rv.pp (ωs l σ) D σ ∈ (⊥ : Submodule (Fq P0) (Algebra.Vec (Fq P0) P0.N))
      rw [hzero l]
      exact Submodule.zero_mem _
    have hvbot : v ∈ (⊥ : Submodule (Fq P0) (Algebra.Vec (Fq P0) P0.N)) := hspan hv.2.1
    have hvzero : v = 0 := by simpa only [Submodule.mem_bot] using hvbot
    exact False.elim (hv.1 hvzero)

theorem plain_stack_zero_of_mark_alpha {P : Params} (D : ExprT P)
    (h : markSector D = .alpha) : exprStack D .plain = 0 := by
  classical
  by_contra hn
  have hm : markSector D = .plain := by simp [markSector, hn]
  rw [hm] at h
  cases h

theorem red_complete (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (m : Msg P0) (f : FullOut P0) (D : ExprT P0) (ι : Fq P0)
    (hgood : GoodMark (ppOf ch S) f.w D ι)
    (hker : jointSpace (markStack D) ⊓ LinearMap.ker (zLin (formsOfRun f.w)) ≠ ⊥)
    (hmon : monitor (monCtx (redViewOf (ppOf ch S) m f.w) f.wp) f.w.out.pv f.w.st.tr
      f.w.st.kdfLog = MonStop.stack D)
    (hrec : gradSpan (ppOf ch S) (recAssign f.w0 f.w1) D (markSector D) =
      jointSpace (markStack D)) :
    (redOutput (redViewOf (ppOf ch S) m f.w) f.wp (recAssign f.w0 f.w1)).isSome := by
  classical
  let rv := redViewOf (ppOf ch S) m f.w
  let ωs := recAssign f.w0 f.w1
  by_cases hselect : markSector D = .plain ∨
      kernelVec rv.out.forms (fun l => rGrad rv.pp (ωs l .plain) D .plain) = none
  · have hker' : jointSpace (markStack D) ⊓ LinearMap.ker (zLin (formVec rv.out.forms)) ≠ ⊥ := by
      simpa only [rv, redViewOf, formsOfRun] using hker
    have hrec' : gradSpan rv.pp ωs D (markSector D) = jointSpace (markStack D) := hrec
    obtain ⟨v, hv⟩ := mark_kernel_exists rv ωs D hker' hrec'
    have hk := (kernelVec_spec rv.out.forms _).2 v hv
    have hmem : v ∈ jointSpace (markStack D) := by
      rw [← hrec']
      exact hk.2.1
    have hsym := (Differences.good_mark_passing ch S hS f.w D ι hgood).2.2.1
    obtain ⟨_, _, _, _, _, hheavy⟩ := hgood
    apply output_of_selected rv f.wp ωs D hmon v (choose_marked rv ωs D v hv hselect)
    exact Lift.convert_complete (markStack D) hsym hheavy v hmem hk.1 hk.2.2.2
  · have hn := (not_or.mp hselect).2
    have hm : markSector D = .alpha := by
      cases hm : markSector D with
      | plain => exact False.elim ((not_or.mp hselect).1 hm)
      | alpha => rfl
    have hstack : exprStack D .plain = 0 := plain_stack_zero_of_mark_alpha D hm
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Option.isSome_iff_ne_none.mpr hn)
    have hk := (kernelVec_spec rv.out.forms _).2 v hv
    have hchoose : chooseVec rv ωs D = some v := by
      dsimp only [chooseVec]
      rw [hv]
      rfl
    have hmem : v ∈ jointSpace (markStack D) := by
      have hzero : ∀ l, rGrad rv.pp (ωs l .plain) D .plain = 0 := by
        intro l
        obtain ⟨_, _, _, hid, _, _⟩ := hgood
        exact plain_gradient_zero ch S hS f.w.out.forms D (realR f.w) ι hid hstack (ωs l .plain)
      exact False.elim (hn (kernel_none_of_grads_zero rv ωs D .plain hzero))
    have hsym := (Differences.good_mark_passing ch S hS f.w D ι hgood).2.2.1
    obtain ⟨_, _, _, _, _, hheavy⟩ := hgood
    apply output_of_selected rv f.wp ωs D hmon v hchoose
    exact Lift.convert_complete (markStack D) hsym hheavy v hmem hk.1 hk.2.2.2

end Praxis.Proofs.Reduction
