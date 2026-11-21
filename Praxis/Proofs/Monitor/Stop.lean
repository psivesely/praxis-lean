import Praxis.Proofs.Differences
import Praxis.Proofs.Degree
import Praxis.Proofs.Monitor.Stop.Deterministic
import Praxis.Proofs.Monitor.Stop.Coins
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Proofs.Monitor.Stop.RightPoly
import Praxis.Proofs.Monitor.Stop.Numerator
import Praxis.Proofs.Monitor.Stop.Degree
import Praxis.Proofs.Monitor.Stop.NumDegree
import Praxis.Proofs.Monitor.Stop.Sync
import Praxis.Proofs.Monitor.Stop.Init
import Praxis.Proofs.Monitor.Stop.Op
import Praxis.Proofs.Monitor.Stop.Kdf
import Praxis.Proofs.Monitor.Stop.Fold
import Praxis.Proofs.Monitor.Stop.FixedBound
import Praxis.Proofs.Monitor.Stop.Sampling
import Praxis.Proofs.Monitor.Stop.Roots
import Praxis.Proofs.Monitor.Stop.LeftDegree
import Praxis.Proofs.Monitor.Stop.RightDegree
import Praxis.Proofs.Monitor.Stop.Main
import Praxis.Proofs.Monitor.Stop.MainRoot
import Praxis.Proofs.Monitor.Stop.QapDeg
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.QAP.Valid
import Praxis.Params
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

private theorem sampleAssigns_one_event {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty (ValidCoin pp)] (p : Assign P → Prop) :
    letI := SampleableType.ofFintype (AssignSample pp)
    Pr[fun ωs => p (ωs 0) | sampleAssigns pp 1] =
      Pr[fun z => p (sampleToAssign z) | $ᵗ (AssignSample pp)] := by
  classical
  letI := SampleableType.ofFintype (ValidCoin pp)
  letI := SampleableType.ofFintype (AssignSample pp)
  have h := probEvent_congr' (p := fun ωs => p (ωs 0))
    (fun _ _ => Iff.rfl) (sampleAssigns_law pp 1)
  rw [probEvent_map] at h
  have he := evalSPMF_map_bijective_uniform_cross (α := Fin 1 → AssignSample pp)
    (Equiv.funUnique (Fin 1) (AssignSample pp))
    (Equiv.funUnique (Fin 1) (AssignSample pp)).bijective
  have hp := probEvent_congr' (p := fun z => p (sampleToAssign z))
    (fun _ _ => Iff.rfl) he
  rw [probEvent_map] at hp
  exact h.trans hp

private theorem worldFull_private_bound {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (Fq P ↪ Label P)] (pp : PublicParams P) [Nonempty (ValidCoin pp)]
    (m : Msg P) (A : Adversary P) (ext : ExtractorLaw P)
    (p : WorldOut P → Assign P → Prop) (b : ENNReal)
    (h : letI := SampleableType.ofFintype (AssignSample pp)
      ∀ w, Pr[fun z => p w (sampleToAssign z) | $ᵗ (AssignSample pp)] ≤ b) :
    Pr[fun f => p f.w f.wp | worldFull pp m A ext] ≤ b := by
  classical
  unfold worldFull
  apply probEvent_bind_le_of_forall_le
  intro w _
  have hk (ωp : Fin 1 → Assign P) :
      Pr[fun f : FullOut P => p f.w f.wp | (do
        let ω0 ← sampleAssigns pp 3
        let ω1 ← sampleAssigns pp 3
        let x ← ext pp.S w.out.pv w.st.tr
        pure (⟨w, ωp 0, ω0, ω1, x⟩ : FullOut P))] =
        if p w (ωp 0) then 1 else 0 := by
    simp only [probEvent_bind_eq_tsum, probEvent_pure]
    by_cases hp : p w (ωp 0) <;> simp [hp, tsum_probOutput_eq_sub]
  rw [probEvent_bind_eq_tsum]
  simp_rw [hk]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← probEvent_eq_tsum_ite, sampleAssigns_one_event]
  exact h w

theorem monitor_at_mark (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (Q QH : ℕ) (A : Adversary P0) (hA : InClass A Q QH) (m : Msg P0) :
    (Pr[fun f => ∃ D ι, GoodMark (ppOf ch S) f.w D ι ∧
        monitor (monCtx (redViewOf (ppOf ch S) m f.w) f.wp) f.w.out.pv f.w.st.tr f.w.st.kdfLog ≠
          MonStop.stack D |
      worldFull (ppOf ch S) m A extF]).toReal ≤ (Constants.eps_f : ℝ) := by
  classical
  let pp := ppOf ch S
  have hv : ValidQAP pp.qap S := Praxis.Proofs.QAP.domainMap_valid ch S
  have hZc : ∀ c, (pp.qap.zCell c).natDegree ≤ P0.D :=
    zCell_natDegree_le pp.qap hv.Z_eq (pointSet_card_le_main _)
      (by norm_num [P0, Params.main, Constants.D])
  have hZ0 := Z0_natDegree_le pp.qap hv.Z0_eq
  let b : ENNReal := (Constants.eps_f_numerator : ENNReal) /
    ((P0.q - P0.D : ℕ) : ENNReal)
  have hb : b ≠ ⊤ := by
    exact ENNReal.div_ne_top (by simp)
      (by norm_num [P0, Params.main, Constants.q, Constants.D])
  letI := SampleableType.ofFintype (AssignSample pp)
  have hprob : Pr[fun f => ∃ D ι, GoodMark pp f.w D ι ∧
      monitor (monCtx (redViewOf pp m f.w) f.wp) f.w.out.pv f.w.st.tr f.w.st.kdfLog ≠
        MonStop.stack D | worldFull pp m A extF] ≤ b := by
    refine worldFull_private_bound pp m A extF (fun w ω => ∃ D ι, GoodMark pp w D ι ∧
      monitor (monCtx (redViewOf pp m w) ω) w.out.pv w.st.tr w.st.kdfLog ≠
        MonStop.stack D) b ?_
    intro w
    apply fixed_world_bound_of_roots pp m w b
    intro D ι hnon
    exact main_root_bound pp (formsOfRun w) D ι hv.A_degree hv.B_degree hv.Lrho_degree
      hZc hZ0 hnon
  apply (ENNReal.toReal_mono hb hprob).trans
  norm_num [b, P0, Params.main, Constants.eps_f_numerator, Constants.q, Constants.D,
    Constants.eps_f]

end Praxis.Proofs.Monitor
