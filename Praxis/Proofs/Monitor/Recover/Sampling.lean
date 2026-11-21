import Praxis.Proofs.Monitor.Stop
import Praxis.Constants
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Degree
import Praxis.Params
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

abbrev ValidDraw {P : Params} (pp : PublicParams P) :=
  {c : Coins P // ValidCoins pp.qap c} × Vec (Fq P) P.N

def drawAssign {P : Params} {pp : PublicParams P} (a : ValidDraw pp) : Assign P :=
  ⟨a.1.val, a.2⟩

def pairFunctions (α β ι : Type) : ((ι → α) × (ι → β)) ≃ (ι → α × β) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; funext i; exact Prod.eta (x i)

theorem sampleProd_law (α β : Type) [SampleableType α] [SampleableType β] :
    𝒮[do let x ← $ᵗ α; let y ← $ᵗ β; pure (x, y)] =
      𝒮[@uniformSample (α × β) (instSampleableTypeProd α β)] := by
  change 𝒮[do let x ← $ᵗ α; let y ← $ᵗ β; pure (x, y)] =
    𝒮[(Prod.mk <$> ($ᵗ α)) <*> ($ᵗ β)]
  simp [seq_eq_bind_map, monad_norm]

theorem rcv_sampleAssigns_law {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (k : ℕ) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (Fin k → ValidDraw pp)
    𝒮[sampleAssigns pp k] = 𝒮[(fun z : Fin k → ValidDraw pp => fun i => drawAssign (z i)) <$>
      ($ᵗ (Fin k → ValidDraw pp))] := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  letI := SampleableType.ofFintype (Fin k → ValidDraw pp)
  let X := Fin k → {c : Coins P // ValidCoins pp.qap c}
  let Y := Fin k → Vec (Fq P) P.N
  let e := pairFunctions {c : Coins P // ValidCoins pp.qap c} (Vec (Fq P) P.N) (Fin k)
  let f := fun z : Fin k → ValidDraw pp => fun i => drawAssign (z i)
  have hsyn : sampleAssigns pp k = (f ∘ e) <$> (do
      let cs ← $ᵗ X
      let rs ← $ᵗ Y
      pure (cs, rs)) := by
    unfold sampleAssigns
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  rw [hsyn]
  calc
    _ = 𝒮[(f ∘ e) <$> (@uniformSample (X × Y) (instSampleableTypeProd X Y))] :=
      evalSPMF_map_eq_of_evalSPMF_eq (sampleProd_law X Y) _
    _ = 𝒮[f <$> ($ᵗ (Fin k → ValidDraw pp))] := by
      letI := instSampleableTypeProd X Y
      have he := evalSPMF_map_bijective_uniform_cross (X × Y) e e.bijective
      have hh := evalSPMF_map_eq_of_evalSPMF_eq he f
      simpa only [Functor.map_map, Function.comp_def] using hh

theorem sampleAssigns_event {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (k : ℕ) (E : (Fin k → Assign P) → Prop) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (Fin k → ValidDraw pp)
    Pr[E | sampleAssigns pp k] =
      Pr[fun z : Fin k → ValidDraw pp => E (fun i => drawAssign (z i)) | $ᵗ (Fin k → ValidDraw pp)] := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (Fin k → ValidDraw pp)
  have h := rcv_sampleAssigns_law pp k
  have h' : Pr[E | sampleAssigns pp k] =
      Pr[E | (fun z : Fin k → ValidDraw pp => fun i => drawAssign (z i)) <$>
        ($ᵗ (Fin k → ValidDraw pp))] := by
    simp only [probEvent_def, h]
  rw [h', probEvent_map]
  rfl

theorem recovery_degree_le_eps :
    3 * ((P0.n + 3 : ℕ) : ℝ) / ((Constants.q : ℝ) - Constants.D) ≤
      (Constants.eps_f : ℝ) := by
  have hden : 0 ≤ (Constants.q : ℝ) - Constants.D := by
    norm_num [Constants.q, Constants.D]
  calc
    _ ≤ (Constants.d_star : ℝ) / ((Constants.q : ℝ) - Constants.D) := by
      apply div_le_div_of_nonneg_right _ hden
      norm_num [P0, Params.main, Constants.n, Constants.d_star]
    _ ≤ _ := Praxis.Proofs.Degree.degree_le_eps.2

noncomputable def postWorld {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (ext : ExtractorLaw P) (w : WorldOut P) :
    ProbComp (FullOut P) := do
  let ωp ← sampleAssigns pp 1
  let ω0 ← sampleAssigns pp 3
  let ω1 ← sampleAssigns pp 3
  let x ← ext pp.S w.out.pv w.st.tr
  pure ⟨w, ωp 0, ω0, ω1, x⟩

theorem worldFull_bound {P : Params} [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (ext : ExtractorLaw P) (E : FullOut P → Prop) (ε : ENNReal)
    (h : ∀ w, Pr[E | postWorld pp ext w] ≤ ε) : Pr[E | worldFull pp m A ext] ≤ ε := by
  change Pr[E | worldRun pp m A >>= postWorld pp ext] ≤ ε
  exact probEvent_bind_le_of_forall_le (fun w _ => h w)

theorem worldFull_bound_toReal {P : Params} [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (ext : ExtractorLaw P) (E : FullOut P → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ w, Pr[E | postWorld pp ext w] ≤ ENNReal.ofReal ε) :
    (Pr[E | worldFull pp m A ext]).toReal ≤ ε := by
  have hb := worldFull_bound pp m A ext E (ENNReal.ofReal ε) h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa [ENNReal.toReal_ofReal hε] using this

end Praxis.Proofs.Monitor
