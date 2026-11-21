import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitRun
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.Coupling
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitBoundary
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Published
import Praxis.Reduction

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option maxHeartbeats 500000

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

variable (pp : PublicParams P0)

attribute [local irreducible] initialise keys1 keys2 g1Order g2Order List.mapM referenceInsert formIndexList initialWorlds Finset.filter

def InitEvent (n : ℕ) (r : Record pp) (c : CoinDomain pp) (x : ℕ → k)
    (ω : WorldOut P0 × ObsState pp) : Prop :=
  Clean n ω ∧ (fullRecord ω).cut n = r ∧ ω.1.out.coins = c.val ∧ guessValues r ω = x

lemma at_coin_zero (m : Msg P0) (A : Adversary P0) (d : InitData) (n : ℕ) (r : Record pp)
    (c c' : CoinDomain pp) (x : ℕ → k) (σ : LabelEncoding P0) (hc : c' ≠ c) :
    Pr[InitEvent pp n r c x | observedAt pp m A d c' σ] = 0 := by
  simp only [observedAt, bind_pure_comp, probEvent_map]
  rw [probEvent_eq_zero_iff]
  intro z _ h
  exact hc (Subtype.ext h.2.2.1)

lemma at_fields_zero (m : Msg P0) (A : Adversary P0) (d : InitData) (n : ℕ) (r : Record pp)
    (c : CoinDomain pp) (x : ℕ → k) (σ : LabelEncoding P0)
    (hd : ¬ (d.header = r.header ∧ d.forms = r.forms)) :
    Pr[InitEvent pp n r c x | observedAt pp m A d c σ] = 0 := by
  simp only [observedAt, bind_pure_comp, probEvent_map]
  rw [probEvent_eq_zero_iff]
  intro z _ h
  exact hd ⟨congrArg Record.header h.2.1, congrArg Record.forms h.2.1⟩

lemma average_fixed (m : Msg P0) (A : Adversary P0)
    (hf : Seed P0 × FormIndex P0 → Option (Rq P0)) (n : ℕ) (r : Record pp)
    (c : CoinDomain pp) (x : ℕ → k)
    (hind : ∀ pad, IndStmt pp n r c x pad (A.run r.pv r.header)) :
    Pr[InitEvent pp n r c x | uniform (Finset.univ : Finset (LabelEncoding P0)) >>=
      observedAt pp m A ⟨r.header, r.forms, hf⟩ c] ≤
      Pr[fun R => R.cut n = r | genericAt pp A r.header r.forms (baseOracle hf)] *
        Pr[= x | guessDraw pp r c] := by
  let g : GenState pp :=
    ⟨{baseOracle hf with issuedT := (r.pv.gT.map Prod.snd).toFinset},
      initialise pp r.forms r.pv, [], []⟩
  let W := initialWorlds pp r c x
  by_cases hc : (initialise pp r.forms r.pv).first = none
  swap
  · apply le_of_eq_of_le _ zero_le
    rw [probEvent_eq_zero_iff]
    intro ω hω hE
    rw [mem_support_bind_iff] at hω
    obtain ⟨σ, _, hω⟩ := hω
    simp only [observedAt, bind_pure_comp, support_map, Set.mem_image] at hω
    obtain ⟨z, _, rfl⟩ := hω
    have hpv : pubView σ pp (formVec r.forms) c.val = r.pv := congrArg Record.pv hE.2.1
    have hf' : (initialise pp r.forms (pubView σ pp (formVec r.forms) c.val)).first = none := hE.1.1
    exact hc ((congrArg (fun pv => (initialise pp r.forms pv).first) hpv).symm.trans hf')
  have hprob : ∀ σ : LabelEncoding P0,
      Pr[InitEvent pp n r c x | observedAt pp m A ⟨r.header, r.forms, hf⟩ c σ] =
      if σ ∈ W then
        Pr[fun z => RGood pp n r z.2 |
          (simulateQ (obsHandler pp σ c.val) (A.run r.pv r.header)).run
            (lift pp c.val (r.header.cm ^^^ m) σ g)] else 0 := by
    intro σ
    simp only [observedAt, bind_pure_comp, probEvent_map]
    split_ifs with hW
    ·
      obtain ⟨hpv, hx⟩ := (mem_initialWorlds pp r c x σ).mp hW
      simp only [hpv]
      apply probEvent_congr' (fun z _ => ?_) rfl
      change (Clean n (⟨σ, ⟨r.pv, r.header, r.forms, c.val⟩, z.1, z.2.oracle⟩, z.2) ∧
        (⟨r.header, r.forms, r.pv, z.2.steps⟩ : FullRecord pp).cut n = r ∧
        c.val = c.val ∧ guessValuesσ pp r σ = x) ↔ RGood pp n r z.2
      simp only [Clean, hc, true_and, FullRecord.cut, record_eq_iff,
        and_self, and_true, hx, RGood, cutOf, Prod.mk.injEq, and_assoc]
    · rw [probEvent_eq_zero_iff]
      intro z _ hE
      apply hW
      have hpv : pubView σ pp (formVec r.forms) c.val = r.pv := congrArg Record.pv hE.2.1
      have hx : guessValuesσ pp r σ = x := hE.2.2.2
      exact (mem_initialWorlds pp r c x σ).mpr ⟨hpv, hx⟩
  rw [probEvent_bind_eq_sum_fintype]
  simp only [hprob, uniform_mass Finset.univ Finset.univ_nonempty,
    Finset.mem_univ, if_true, Finset.card_univ]
  rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
  have hi := initial_sum_bound pp A n r c x (r.header.cm ^^^ m) (baseOracle hf)
    hc (hind _)
  dsimp only at hi
  have h := mul_le_mul_right hi ((Fintype.card (LabelEncoding P0) : ℝ≥0∞)⁻¹)
  have hN : (Fintype.card (LabelEncoding P0) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa only [W, ← mul_assoc,
    ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _), one_mul] using h

lemma average_bound (m : Msg P0) (A : Adversary P0) (d : InitData)
    (n : ℕ) (r : Record pp) (c : CoinDomain pp) (x : ℕ → k)
    (hind : ∀ pad, IndStmt pp n r c x pad (A.run r.pv r.header)) :
    Pr[InitEvent pp n r c x | uniform (Finset.univ : Finset (LabelEncoding P0)) >>=
      observedAt pp m A d c] ≤
      Pr[fun R => R.cut n = r | genericAt pp A d.header d.forms (baseOracle d.hf)] *
        Pr[= x | guessDraw pp r c] := by
  by_cases hd : d.header = r.header ∧ d.forms = r.forms
  · rcases d with ⟨hdr, forms, hf⟩
    rcases hd with ⟨rfl, rfl⟩
    exact average_fixed pp m A hf n r c x hind
  · apply le_of_eq_of_le _ zero_le
    rw [probEvent_bind_eq_tsum]
    simp only [at_fields_zero pp m A d n r c x _ hd, mul_zero, tsum_zero]

lemma coin_average [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0) (d : InitData)
    (n : ℕ) (r : Record pp) (c : CoinDomain pp) (x : ℕ → k)
    (hind : ∀ pad, IndStmt pp n r c x pad (A.run r.pv r.header)) :
    Pr[InitEvent pp n r c x | do
      let c' ← coinLaw pp
      let σ ← uniform (Finset.univ : Finset (LabelEncoding P0))
      observedAt pp m A d c' σ] ≤
      Pr[fun R => R.cut n = r | genericAt pp A d.header d.forms (baseOracle d.hf)] *
        Pr[= c | coinLaw pp] * Pr[= x | guessDraw pp r c] := by
  rw [probEvent_bind_eq_tsum, tsum_eq_single c]
  · have h := mul_le_mul_right (average_bound pp m A d n r c x hind) Pr[= c | coinLaw pp]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  · intro c' hc'
    rw [probEvent_bind_eq_tsum]
    simp only [at_coin_zero pp m A d n r c c' x _ hc', mul_zero, tsum_zero]

lemma init_bound_proof [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0)
    (n : ℕ) (r : Record pp) (c : CoinDomain pp) (x : ℕ → k)
    (hind : ∀ pad, IndStmt pp n r c x pad (A.run r.pv r.header)) :
    Pr[InitEvent pp n r c x | observedRun pp m A] ≤
      Pr[fun R => R.cut n = r | genRun pp A] * Pr[= c | coinLaw pp] *
        Pr[= x | guessDraw pp r c] := by
  have ho := probEvent_congr' (fun _ _ => Iff.rfl) (observed_setup pp m A)
    (p := InitEvent pp n r c x)
  have hg := probEvent_congr' (fun _ _ => Iff.rfl) (gen_setup pp A)
    (p := fun R => R.cut n = r)
  rw [ho, hg, probEvent_bind_eq_tsum]
  rw [probEvent_bind_eq_tsum setup
    (fun d => genericAt pp A d.header d.forms (baseOracle d.hf)) (fun R => R.cut n = r),
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro d
  have h := mul_le_mul_right (coin_average pp m A d n r c x hind) Pr[= d | setup]
  simpa only [mul_assoc] using h

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init
