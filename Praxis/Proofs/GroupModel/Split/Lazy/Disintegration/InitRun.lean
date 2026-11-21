import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitBoundary
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitSampling
import Praxis.Proofs.KeyOracle.Independence
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
import Praxis.Published
import Praxis.Reduction

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option maxHeartbeats 500000

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

variable (pp : PublicParams P0)

attribute [local irreducible] initialise keys1 keys2 g1Order g2Order List.mapM referenceInsert formIndexList

lemma commute {α β γ : Type} (oa : ProbComp α) (ob : ProbComp β)
    (f : α → β → ProbComp γ) :
    evalSPMF (oa >>= fun a => ob >>= f a) =
      evalSPMF (ob >>= fun b => oa >>= fun a => f a b) := by
  apply evalSPMF_ext
  intro z
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  ring

structure InitData where
  header : Header P0
  forms : FormMatrix P0
  hf : Seed P0 × FormIndex P0 → Option (Rq P0)

def setup : ProbComp InitData := do
  let seed ← ($ᵗ (Seed P0) : ProbComp (Seed P0))
  let ent ← ((formIndexList P0).mapM fun i => do
    let a ← hfLazy (seed, i); pure (i, a)).run OracleState.empty
  let cm ← ($ᵗ (Msg P0) : ProbComp (Msg P0))
  pure ⟨⟨seed, cm⟩, Sampling.matrixOf ent.1, ent.2.hf⟩

def baseOracle (hf : Seed P0 × FormIndex P0 → Option (Rq P0)) : OracleState P0 :=
  {OracleState.empty with hf := hf}

def observedAt (m : Msg P0) (A : Adversary P0) (d : InitData) (c : CoinDomain pp)
    (σ : LabelEncoding P0) : ProbComp (WorldOut P0 × ObsState pp) := do
  let pv := pubView σ pp (formVec d.forms) c.val
  let g : GenState pp := ⟨{baseOracle d.hf with issuedT := (pv.gT.map Prod.snd).toFinset},
    initialise pp d.forms pv, [], []⟩
  let z ← (simulateQ (obsHandler pp σ c.val) (A.run pv d.header)).run
    (lift pp c.val (d.header.cm ^^^ m) σ g)
  pure (⟨σ, ⟨pv, d.header, d.forms, c.val⟩, z.1, z.2.oracle⟩, z.2)

lemma observed_prepared [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0) :
    observedRun pp m A = (do
      let σ ← sampleEncoding
      let d ← Sampling.prepare pp
      observedAt pp m A ⟨d.header m, d.forms, d.hf⟩ d.coins σ) := by
  simp only [observedRun, Sampling.encGame_prepared, bind_map_left]
  apply bind_congr
  intro σ
  apply bind_congr
  intro d
  simp [observedAt, Sampling.Prepared.header, Sampling.fixedOut,
    Sampling.cacheTarget, Sampling.initialState, lift, cacheT, tname,
    baseOracle, BitVec.xor_comm m, BitVec.xor_assoc]

lemma observed_setup [Nonempty (CoinDomain pp)] (m : Msg P0) (A : Adversary P0) :
    evalSPMF (observedRun pp m A) = evalSPMF (do
      let d ← setup
      let c ← coinLaw pp
      let σ ← uniform (Finset.univ : Finset (LabelEncoding P0))
      observedAt pp m A d c σ) := by
  rw [observed_prepared, sampleEncoding_uniform, commute]
  simp only [Sampling.prepare, setup, bind_assoc, pure_bind]
  apply evalSPMF_bind_congr
  intro seed _
  apply evalSPMF_bind_congr
  intro ent _
  change evalSPMF ((coinLaw pp) >>= fun c => ($ᵗ (Msg P0)) >>= fun pad =>
      uniform (Finset.univ : Finset (LabelEncoding P0)) >>= fun σ =>
        observedAt pp m A ⟨⟨seed, m ^^^ pad⟩, Sampling.matrixOf ent.1, ent.2.hf⟩ c σ) = _
  rw [commute]
  simpa only [BitVec.xor_comm m] using KeyOracle.uniform_xor m (fun cm => do
    let c ← coinLaw pp
    let σ ← uniform (Finset.univ : Finset (LabelEncoding P0))
    observedAt pp m A ⟨⟨seed, cm⟩, Sampling.matrixOf ent.1, ent.2.hf⟩ c σ)

lemma gen_setup (A : Adversary P0) :
    evalSPMF (genRun pp A) = evalSPMF (do
      let d ← setup
      genericAt pp A d.header d.forms (baseOracle d.hf)) := by
  simp only [genRun, setup, genericAt, bind_assoc, pure_bind]
  apply evalSPMF_bind_congr
  intro seed _
  apply evalSPMF_bind_congr
  intro ent hent
  have hc := Sampling.readEntries_clean seed (formIndexList P0) OracleState.empty
    (by simp [Sampling.Clean, OracleState.empty]) ent hent
  have he : ent.2 = baseOracle ent.2.hf := by
    rcases ent with ⟨entries, st⟩
    rcases st with ⟨hf, kdf, tr, klog, issued, names⟩
    rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
  rw [he]
  rfl

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init
