import Praxis.Proofs.Reduction.Law.World
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.Reduction.Law.Forms
import Praxis.Params
import Praxis.Reduction
import Praxis.Algebra.Definitions.MSIS

namespace Praxis.Proofs.Reduction

open OracleComp OracleSpec

variable {P : Params}

noncomputable def outOf [Fact (Nat.Prime P.q)] (pp : PublicParams P) (m : Msg P)
    (f : FullOut P) : Option (Algebra.CoeffVec P.d P.cols) :=
  redOutput (redViewOf pp m f.w) f.wp (recAssign f.w0 f.w1)

set_option maxHeartbeats 1600000 in
theorem joint_law [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (hd : P.d ≠ 0) (pp : PublicParams P) (m : Msg P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (A : Adversary P)
    (ext : ExtractorLaw P) :
    letI : Nonempty (MSISChallenge P hd) := ⟨0⟩
    letI := SampleableType.ofFintype (MSISChallenge P hd)
    𝒮[do let chal ← $ᵗ (MSISChallenge P hd)
         let out ← reduction hd pp m A chal
         pure (chal, out)] =
    𝒮[do let f ← worldFull pp m A ext
         pure (chalOf hd f.w.out.forms, outOf pp m f)] := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI : Nonempty (MSISChallenge P hd) := ⟨0⟩
  letI := SampleableType.ofFintype (MSISChallenge P hd)
  calc
    _ = 𝒮[do let chal ← $ᵗ (MSISChallenge P hd)
             let star ← $ᵗ (Fin P.rows → Rq P)
             let w ← worldAtForms pp m A (formsOfChallenge P hd chal star)
             let out ← redPost pp (redViewOf pp m w)
             pure (chal, out)] := by
      simp only [reduction, blackBoxRun_eq_worldAtForms, bind_assoc]
    _ = 𝒮[do let B ← $ᵗ (FormMatrix P)
             let w ← worldAtForms pp m A B
             let out ← redPost pp (redViewOf pp m w)
             pure (chalOf hd B, out)] := by
      let k := fun x : MSISChallenge P hd × FormMatrix P => do
        let w ← worldAtForms pp m A x.2
        let out ← redPost pp (redViewOf pp m w)
        pure (x.1, out)
      calc
        _ = 𝒮[(do let chal ← $ᵗ (MSISChallenge P hd)
                     let star ← $ᵗ (Fin P.rows → Rq P)
                     pure (chal, formsOfChallenge P hd chal star)) >>= k] := by
          simp only [k, bind_assoc, pure_bind]
        _ = 𝒮[(do let B ← $ᵗ (FormMatrix P); pure (chalOf hd B, B)) >>= k] := by
          rw [evalSPMF_bind, uniform_forms hd, ← evalSPMF_bind]
        _ = _ := by simp only [k, bind_assoc, pure_bind]
    _ = 𝒮[do let B ← $ᵗ (FormMatrix P)
             let w ← worldAtForms pp m A B
             let out ← redPost pp (redViewOf pp m w)
             pure (chalOf hd w.out.forms, out)] := by
      apply evalSPMF_bind_congr
      intro B hB
      apply evalSPMF_bind_congr
      intro w hw
      rw [worldAtForms_forms pp m A B w hw]
    _ = 𝒮[do let w ← worldRun pp m A
             let out ← redPost pp (redViewOf pp m w)
             pure (chalOf hd w.out.forms, out)] := by
      conv_rhs => rw [evalSPMF_bind, worldRun_law pp m A, ← evalSPMF_bind]
      simp only [bind_assoc]
    _ = 𝒮[do let f ← worldFull pp m A ext
             pure (chalOf hd f.w.out.forms, outOf pp m f)] := by
      simp only [worldFull, outOf, bind_assoc, pure_bind]
      apply evalSPMF_bind_congr
      intro w hw
      rw [evalSPMF_bind, post_eq_full pp m w ext, ← evalSPMF_bind]
      simp only [bind_assoc, pure_bind]
    _ = _ := rfl
  all_goals rfl

theorem success_law [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (hd : P.d ≠ 0) (pp : PublicParams P) (m : Msg P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (A : Adversary P)
    (ext : ExtractorLaw P) :
    msisSucc (msisRing P hd) P.eta (reduction hd pp m A) =
      (Pr[fun f => RmWins hd pp m f | worldFull pp m A ext]).toReal := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI : Nonempty (MSISChallenge P hd) := ⟨0⟩
  letI := SampleableType.ofFintype (MSISChallenge P hd)
  change (Pr[= true | do
    let chal ← $ᵗ (MSISChallenge P hd)
    let out ← reduction hd pp m A chal
    pure (decide (Algebra.MSISWins (msisRing P hd) P.eta chal out))]).toReal = _
  have h := joint_law hd pp m A ext
  have h' := evalSPMF_map_eq_of_evalSPMF_eq h
    (fun z => decide (Algebra.MSISWins (msisRing P hd) P.eta z.1 z.2))
  have hp := probOutput_congr (x := true) (y := true) rfl h'
  simpa only [map_bind, map_pure, bind_pure_comp, Functor.map_map, probOutput_map,
    probEvent_map, Function.comp_def, decide_eq_true_eq, RmWins, outOf] using congrArg ENNReal.toReal hp

end Praxis.Proofs.Reduction
