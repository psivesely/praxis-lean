import Praxis.Proofs.Reduction.Law.Prefix
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Reduction

namespace Praxis.Proofs.Reduction

open OracleComp OracleSpec

variable {P : Params}

theorem runWith_eq [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (A : Adversary P) (enc : GameM P (EncOut P)) (s : OracleState P) :
    runWith σ A enc s = (do
      let es ← enc.run s
      let z ← (simulateQ (gameImpl σ) (A.run es.1.pv es.1.header)).run es.2
      pure ((es.1, z.1), z.2)) := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp [runWith, StateT.run_bind, monad_norm]

theorem runWith_encGame [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) :
    runWith σ A (encGame σ pp m) OracleState.empty = (do
      let seed ← $ᵗ (Seed P)
      runWith σ A (encAt σ pp m seed) OracleState.empty) := by
  simp [runWith_eq, encGame, StateT.run_bind, StateT.run_lift, bind_assoc]

noncomputable def worldAtForms [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (B : FormMatrix P) : ProbComp (WorldOut P) :=
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  do
    let σ ← sampleEncoding
    let seed ← $ᵗ (Seed P)
    let z ← runWith σ A (encAt σ pp m seed) (OracleState.empty.programHF seed B)
    pure ⟨σ, z.1.1, z.1.2, z.2⟩

theorem runWith_empty_law [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (seed : Seed P) :
    𝒮[runWith σ A (encAt σ pp m seed) OracleState.empty] =
      𝒮[do let B ← $ᵗ (FormMatrix P)
           runWith σ A (encAt σ pp m seed) (OracleState.empty.programHF seed B)] := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [runWith_eq]
  rw [evalSPMF_bind, encAt_empty_law, ← evalSPMF_bind]
  simp only [bind_assoc]

theorem worldRun_law [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) :
    𝒮[worldRun pp m A] =
      𝒮[do let B ← $ᵗ (FormMatrix P); worldAtForms pp m A B] := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  unfold worldRun worldAtForms
  simp only [runWith_encGame, bind_assoc]
  calc
    _ = 𝒮[do let σ ← sampleEncoding
             let seed ← $ᵗ (Seed P)
             let B ← $ᵗ (FormMatrix P)
             let z ← runWith σ A (encAt σ pp m seed) (OracleState.empty.programHF seed B)
             pure ⟨σ, z.1.1, z.1.2, z.2⟩] := by
      apply evalSPMF_bind_congr
      intro σ hσ
      apply evalSPMF_bind_congr
      intro seed hs
      rw [evalSPMF_bind, runWith_empty_law σ pp m A seed, ← evalSPMF_bind]
      simp only [bind_assoc]
    _ = _ := by
      calc
        _ = 𝒮[do let σ ← sampleEncoding
                 let B ← $ᵗ (FormMatrix P)
                 let seed ← $ᵗ (Seed P)
                 let z ← runWith σ A (encAt σ pp m seed) (OracleState.empty.programHF seed B)
                 pure ⟨σ, z.1.1, z.1.2, z.2⟩] := by
          apply evalSPMF_bind_congr
          intro σ hσ
          exact evalSPMF_bind_bind_swap _ _ _
        _ = _ := evalSPMF_bind_bind_swap _ _ _

theorem worldAtForms_forms [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) (m : Msg P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : Adversary P) (B : FormMatrix P) (w : WorldOut P)
    (hw : w ∈ support (worldAtForms pp m A B)) : w.out.forms = B := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp only [worldAtForms, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨σ, hσ, seed, hs, z, hz, rfl⟩ := hw
  rw [runWith_eq, encAt_programmed] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨c, hc, pad, hp, z', hz', rfl⟩ := hz
  obtain ⟨c', hc', pad', hp', rfl⟩ := hc
  rfl

theorem blackBoxRun_eq_worldAtForms {α : Type} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P) (m : Msg P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (A : Adversary P)
    (post : RedView P → ProbComp α) (B : FormMatrix P) :
    blackBoxRun pp m A post B = (do
      let w ← worldAtForms pp m A B
      post (redViewOf pp m w)) := by
  simp only [blackBoxRun, worldAtForms, redViewOf, bind_assoc, pure_bind]

theorem post_eq_full [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (m : Msg P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (w : WorldOut P)
    (ext : ExtractorLaw P) :
    𝒮[redPost pp (redViewOf pp m w)] =
      𝒮[do let ωp ← sampleAssigns pp 1
           let ω0 ← sampleAssigns pp 3
           let ω1 ← sampleAssigns pp 3
           let x ← ext pp.S w.out.pv w.st.tr
           pure (redOutput (redViewOf pp m w) (ωp 0) (recAssign ω0 ω1))] := by
  simp only [redPost, recAssign]
  apply evalSPMF_bind_congr
  intro ωp _
  apply evalSPMF_bind_congr
  intro ω0 _
  apply evalSPMF_bind_congr
  intro ω1 _
  apply evalSPMF_ext
  intro z
  change Pr[= z | pure (redOutput (redViewOf pp m w) (ωp 0) (recAssign ω0 ω1))] = _
  simp

end Praxis.Proofs.Reduction
