import Praxis.Proofs.Coupling.Stopped
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Relation
import Praxis.Scheme
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Coupling

open OracleComp OracleSpec

theorem uniformProgram_lossless {α : Type} (c : ProbComp α) : Pr[⊥ | c] = 0 := by
  induction c using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rw [probFailure_bind_of_const (r := 0) (fun a _ => ih a)]
    simp

theorem uniformProgram_const {α : Type} (c : ProbComp α) (p : Prop) [Decidable p] :
    Pr[fun _ => p | c] = if p then 1 else 0 := by
  classical
  by_cases hp : p <;> simp [hp]

theorem extractWin_iff (S : Relation P0) (b o : Bool)
    (x : Option (Algebra.Vec (Fq P0) P0.N)) :
    extractWin S b o x = true ↔ o = b ∧ ExtFails S x := by
  cases x with
  | none => simp [extractWin, ExtFails]
  | some x => simp [extractWin, ExtFails, IsWitness]

theorem full_marginal (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0)
    (A : Adversary P0) (ext : ExtractorLaw P0)
    (B : WorldOut P0 → Option (Algebra.Vec (Fq P0) P0.N) → Prop) :
    Pr[fun f => B f.w f.x | worldFull pp m A ext] =
      Pr[fun z => B z.1 z.2 | do
        let w ← worldRun pp m A
        let x ← ext pp.S w.out.pv w.st.tr
        pure (w, x)] := by
  classical
  simp only [worldFull, bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub,
    uniformProgram_lossless, tsub_zero, one_mul]

theorem full_world_marginal (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0)
    (A : Adversary P0) (ext : ExtractorLaw P0) (B : WorldOut P0 → Prop) :
    Pr[fun f => B f.w | worldFull pp m A ext] = Pr[B | worldRun pp m A] := by
  classical
  rw [full_marginal pp m A ext (fun w _ => B w)]
  simp only [bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    uniformProgram_const, mul_ite, mul_one, mul_zero]
  exact (probEvent_eq_tsum_ite _ _).symm

theorem noquery_add_failure_le {α : Type} (L : ProbComp α)
    (out : α → Bool) (D F : α → Prop) :
    (Pr[fun x => out x = false ∧ ¬ D x | L]).toReal +
      (Pr[fun x => out x = true ∧ ¬ D x | L]).toReal +
        (Pr[fun x => D x ∧ F x | L]).toReal ≤ 1 := by
  classical
  have hs : Pr[fun x => out x = false ∧ ¬ D x | L] +
      Pr[fun x => out x = true ∧ ¬ D x | L] = Pr[fun x => ¬ D x | L] := by
    simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
    apply tsum_congr
    intro x
    cases out x <;> by_cases hd : D x <;> simp [hd]
  have hsR := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at hsR
  have hc := congrArg ENNReal.toReal (probEvent_compl L D)
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top,
    uniformProgram_lossless, tsub_zero, ENNReal.toReal_one] at hc
  have hf : (Pr[fun x => D x ∧ F x | L]).toReal ≤ (Pr[D | L]).toReal :=
    ENNReal.toReal_mono probEvent_ne_top (probEvent_mono (fun _ _ h => h.1))
  linarith

theorem win_split_le {α : Type} (L : ProbComp α)
    (out : α → Bool) (D F : α → Prop) (b : Bool) :
    (Pr[fun x => out x = b ∧ F x | L]).toReal ≤
      (Pr[fun x => out x = b ∧ ¬ D x | L]).toReal +
        (Pr[fun x => D x ∧ F x | L]).toReal := by
  have h : Pr[fun x => out x = b ∧ F x | L] ≤
      Pr[fun x => out x = b ∧ ¬ D x | L] + Pr[fun x => D x ∧ F x | L] :=
    probEvent_le_add_of_imp_or (fun x _ hx => by
      by_cases hd : D x
      · exact Or.inr ⟨hd, hx.2⟩
      · exact Or.inl ⟨hx.1, hd⟩)
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) h
  rwa [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at hr

theorem half_of_stopped {α : Type} (L0 L1 : ProbComp α)
    (out : α → Bool) (D F : α → Prop)
    (hstop : ∀ o, Pr[fun x => out x = o ∧ ¬ D x | L0] =
      Pr[fun x => out x = o ∧ ¬ D x | L1]) :
    1 / 2 * (Pr[fun x => out x = false ∧ F x | L0]).toReal +
      1 / 2 * (Pr[fun x => out x = true ∧ F x | L1]).toReal ≤
        1 / 2 + 1 / 2 * (1 / 2 * (Pr[fun x => D x ∧ F x | L0]).toReal +
          1 / 2 * (Pr[fun x => D x ∧ F x | L1]).toReal) := by
  have h0 := win_split_le L0 out D F false
  have h1 := win_split_le L1 out D F true
  have hd0 := noquery_add_failure_le L0 out D F
  have hd1 := noquery_add_failure_le L1 out D F
  have he0 := congrArg ENNReal.toReal (hstop false)
  have he1 := congrArg ENNReal.toReal (hstop true)
  linarith

theorem world_win_correspondence (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (m : Msg P0)
    (A : Adversary P0) (ext : ExtractorLaw P0) (b : Bool) :
    Pr[= true | do
      let σ ← (sampleEncoding : ProbComp (LabelEncoding P0))
      let r ← runWith σ A (encGame σ pp m) OracleState.empty
      let x ← ext pp.S r.1.1.pv r.2.tr
      pure (extractWin pp.S b r.1.2 x)] =
      Pr[fun f => f.w.o = b ∧ ExtFails pp.S f.x | worldFull pp m A ext] := by
  classical
  rw [full_marginal pp m A ext (fun w x => w.o = b ∧ ExtFails pp.S x)]
  simp only [worldRun, bind_assoc, bind_map_left, bind_pure_comp]
  simp only [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum,
    probOutput_map, probEvent_map, Function.comp_def, extractWin_iff]

set_option maxRecDepth 2048 in

theorem extractExp_average (ch : AdmissibleChoice P0) (S : Relation P0)
    (A : Adversary P0) (m0 m1 : Msg P0) :
    (Pr[= true | (scheme ch).extractExp S m0 m1 A]).toReal =
      1 / 2 * (Pr[fun f => f.w.o = false ∧ ExtFails S f.x |
        worldFull (ppOf ch S) m0 A extF]).toReal +
      1 / 2 * (Pr[fun f => f.w.o = true ∧ ExtFails S f.x |
        worldFull (ppOf ch S) m1 A extF]).toReal := by
  change (Pr[= true | extractGame (ppOf ch S) m0 m1 A extF]).toReal = _
  have he : Pr[= true | extractGame (ppOf ch S) m0 m1 A extF] =
      (2 : ENNReal)⁻¹ * Pr[fun f => f.w.o = false ∧ ExtFails S f.x |
        worldFull (ppOf ch S) m0 A extF] +
      (2 : ENNReal)⁻¹ * Pr[fun f => f.w.o = true ∧ ExtFails S f.x |
        worldFull (ppOf ch S) m1 A extF] := by
    unfold extractGame
    rw [probOutput_bind_eq_sum_fintype]
    simp only [Fintype.sum_bool, probOutput_uniformSample, Fintype.card_bool,
      Bool.false_eq_true, if_false, if_true]
    rw [world_win_correspondence (ppOf ch S) m1 A extF true,
      world_win_correspondence (ppOf ch S) m0 A extF false]
    exact add_comm _ _
  rw [he, ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_mul]
  · norm_num
  · exact ENNReal.mul_ne_top (by simp) probEvent_ne_top
  · exact ENNReal.mul_ne_top (by simp) probEvent_ne_top

theorem couple_half (ch : AdmissibleChoice P0) (S : Relation P0) (A : Adversary P0)
    (m0 m1 : Msg P0) :
    (Pr[= true | (scheme ch).extractExp S m0 m1 A]).toReal ≤
      1 / 2 + 1 / 2 * (1 / 2 * (Pr[fun f => TargetQueried (ppOf ch S) f.w ∧ ExtFails S f.x |
          worldFull (ppOf ch S) m0 A extF]).toReal +
        1 / 2 * (Pr[fun f => TargetQueried (ppOf ch S) f.w ∧ ExtFails S f.x |
          worldFull (ppOf ch S) m1 A extF]).toReal) := by
  rw [extractExp_average]
  apply half_of_stopped
    (worldFull (ppOf ch S) m0 A extF) (worldFull (ppOf ch S) m1 A extF)
    (fun f => f.w.o) (fun f => TargetQueried (ppOf ch S) f.w)
    (fun f => ExtFails S f.x)
  intro o
  exact (full_world_marginal (ppOf ch S) m0 A extF
    (fun w => w.o = o ∧ ¬ TargetQueried (ppOf ch S) w)).trans
      ((couple_stopped ch S A m0 m1 o).trans
        (full_world_marginal (ppOf ch S) m1 A extF
          (fun w => w.o = o ∧ ¬ TargetQueried (ppOf ch S) w)).symm)

end Praxis.Proofs.Coupling
