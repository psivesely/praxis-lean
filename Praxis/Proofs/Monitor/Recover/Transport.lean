import Praxis.Proofs.Monitor.Recover.Grid
import Praxis.Proofs.Monitor.Recover.Sampling
import Praxis.Enc
import Praxis.Proofs.Monitor.Recover.Helpers
import Praxis.Params
import Praxis.QAP
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

abbrev RecoveryVar (P : Params) := Fin (P.N + 1) ⊕ (Fin (P.N + 1) ⊕ ScalarCoin)

noncomputable def recoverySupport {P : Params} [NeZero P.q] (qap : QAPData P) :
    RecoveryVar P → Finset (Fq P)
  | .inl _ => Finset.univ
  | .inr (.inl _) => Finset.univ
  | .inr (.inr s) => scalarSupport qap s

def recoveryCoordinates {P : Params} {pp : PublicParams P} (a : ValidDraw pp) : RecoveryVar P → Fq P
  | .inl i => a.1.val.1 i
  | .inr (.inl i) => a.2 i
  | .inr (.inr s) => a.1.val.2.2 s

theorem recoveryCoordinates_mem {P : Params} [NeZero P.q] (pp : PublicParams P) (a : ValidDraw pp) :
    recoveryCoordinates a ∈ Fintype.piFinset (recoverySupport pp.qap) := by
  classical
  rw [Fintype.mem_piFinset]
  intro i
  cases i with
  | inl i => simp [recoverySupport]
  | inr i =>
    cases i with
    | inl i => simp [recoverySupport]
    | inr s =>
      simpa [recoverySupport, recoveryCoordinates, mem_scalarSupport] using
        (validCoins_iff_scalarValid pp.qap a.1.val).mp a.1.property s

noncomputable def recoveryCoordinatesEquiv {P : Params} [NeZero P.q] (pp : PublicParams P) :
    ValidDraw pp ≃ {x : RecoveryVar P → Fq P // x ∈ Fintype.piFinset (recoverySupport pp.qap)} ×
      SearchSample P where
  toFun a := (⟨recoveryCoordinates a, recoveryCoordinates_mem pp a⟩, a.1.val.2.1)
  invFun a := ⟨⟨⟨(fun i => a.1.val (.inl i)), a.2, (fun s => a.1.val (.inr (.inr s)))⟩,
    (validCoins_iff_scalarValid pp.qap _).mpr (by
      intro s
      have h := (Fintype.mem_piFinset.mp a.1.property) (.inr (.inr s))
      simpa [recoverySupport, mem_scalarSupport] using h)⟩,
    fun i => a.1.val (.inr (.inl i))⟩
  left_inv := by
    intro a
    rcases a with ⟨⟨⟨y, s, c⟩, hv⟩, r⟩
    rfl
  right_inv := by
    intro a
    rcases a with ⟨⟨x, hx⟩, s⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      cases i with
      | inl i => rfl
      | inr i => cases i <;> rfl
    · rfl

theorem recoveryCoordinates_law {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI : Nonempty {x : RecoveryVar P → Fq P // x ∈ Fintype.piFinset (recoverySupport pp.qap)} :=
      ⟨⟨recoveryCoordinates (⟨Classical.choice inferInstance, 0⟩ : ValidDraw pp),
        recoveryCoordinates_mem pp _⟩⟩
    letI := SampleableType.ofFintype (ValidDraw pp)
    letI := SampleableType.ofFintype {x : RecoveryVar P → Fq P // x ∈ Fintype.piFinset (recoverySupport pp.qap)}
    𝒮[(fun a : ValidDraw pp => (recoveryCoordinatesEquiv pp a).1) <$> ($ᵗ (ValidDraw pp))] =
      𝒮[$ᵗ {x : RecoveryVar P → Fq P // x ∈ Fintype.piFinset (recoverySupport pp.qap)}] := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  let G := {x : RecoveryVar P → Fq P // x ∈ Fintype.piFinset (recoverySupport pp.qap)}
  letI : Nonempty G := ⟨⟨recoveryCoordinates (⟨Classical.choice inferInstance, 0⟩ : ValidDraw pp),
    recoveryCoordinates_mem pp _⟩⟩
  letI := SampleableType.ofFintype (ValidDraw pp)
  letI := SampleableType.ofFintype G
  letI : Nonempty (SearchSample P) := ⟨(Classical.choice
    (show Nonempty {c : Coins P // ValidCoins pp.qap c} from inferInstance)).1.2.1⟩
  letI := SampleableType.ofFintype (SearchSample P)
  letI := SampleableType.ofFintype (G × SearchSample P)
  have he := evalSPMF_map_bijective_uniform_cross (ValidDraw pp)
    (recoveryCoordinatesEquiv pp) (recoveryCoordinatesEquiv pp).bijective
  have he' := evalSPMF_map_eq_of_evalSPMF_eq he (Prod.fst : G × SearchSample P → G)
  have hm : 𝒮[(Prod.fst : G × SearchSample P → G) <$> ($ᵗ (G × SearchSample P))] = 𝒮[$ᵗ G] :=
    evalSPMF_map_fst_uniformSample_prod
  simpa only [Functor.map_map, Function.comp_def] using he'.trans hm

theorem recoverySupport_card_lower {P : Params} [NeZero P.q] (hP : P.Valid)
    (qap : QAPData P) (hKD : P.K1 + 1 ≤ P.D) (i : RecoveryVar P) :
    P.q - P.D ≤ (recoverySupport qap i).card := by
  classical
  cases i with
  | inl i => simp [recoverySupport, Fq, ZMod.card]
  | inr i =>
    cases i with
    | inl i => simp [recoverySupport, Fq, ZMod.card]
    | inr s => exact scalarSupport_card_lower hP qap hKD s

theorem recoverySupport_nonempty {P : Params} [NeZero P.q] (hP : P.Valid)
    (qap : QAPData P) (hKD : P.K1 + 1 ≤ P.D) (hDq : P.D < P.q)
    (i : RecoveryVar P) : (recoverySupport qap i).Nonempty := by
  apply Finset.card_pos.mp
  have h := recoverySupport_card_lower hP qap hKD i
  omega

theorem recoveryGrid_roots {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (hP : P.Valid)
    (hKD : P.K1 + 1 ≤ P.D) (hDq : P.D < P.q)
    (p : MvPolynomial (RecoveryVar P) (Fq P)) (hp : p ≠ 0) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (ValidDraw pp)
    Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryCoordinates a) p = 0 |
      $ᵗ (ValidDraw pp)] ≤ (p.totalDegree : ENNReal) / ((P.q - P.D : ℕ) : ENNReal) := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  let G := {x : RecoveryVar P → Fq P // x ∈ Fintype.piFinset (recoverySupport pp.qap)}
  let e := Fintype.equivFin (RecoveryVar P)
  let H := {x : Fin (Fintype.card (RecoveryVar P)) → Fq P //
    x ∈ Fintype.piFinset (fun i => recoverySupport pp.qap (e.symm i))}
  let g : G := ⟨recoveryCoordinates (⟨Classical.choice inferInstance, 0⟩ : ValidDraw pp),
    recoveryCoordinates_mem pp _⟩
  letI : Nonempty G := ⟨g⟩
  letI : Nonempty H := ⟨gridReindexEquiv e (recoverySupport pp.qap) g⟩
  letI := SampleableType.ofFintype (ValidDraw pp)
  letI := SampleableType.ofFintype G
  letI := SampleableType.ofFintype H
  have hlaw := recoveryCoordinates_law pp
  change 𝒮[(fun a : ValidDraw pp => (recoveryCoordinatesEquiv pp a).1) <$> ($ᵗ (ValidDraw pp))] =
    𝒮[$ᵗ G] at hlaw
  have hprob : Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryCoordinates a) p = 0 |
      $ᵗ (ValidDraw pp)] = Pr[fun x : G => MvPolynomial.eval x.1 p = 0 | $ᵗ G] := by
    have hm := probEvent_map ($ᵗ (ValidDraw pp))
      (fun a : ValidDraw pp => (recoveryCoordinatesEquiv pp a).1)
      (fun x : G => MvPolynomial.eval x.1 p = 0)
    have hd : Pr[fun x : G => MvPolynomial.eval x.1 p = 0 |
        (fun a : ValidDraw pp => (recoveryCoordinatesEquiv pp a).1) <$> ($ᵗ (ValidDraw pp))] =
        Pr[fun x : G => MvPolynomial.eval x.1 p = 0 | $ᵗ G] := by
      simp only [probEvent_def, hlaw]
      rfl
    simpa only [Function.comp_def, recoveryCoordinatesEquiv, Equiv.coe_fn_mk] using hm.symm.trans hd
  rw [hprob]
  exact uniformGrid_roots_reindexed e (recoverySupport pp.qap)
    (recoverySupport_nonempty hP pp.qap hKD hDq) (P.q - P.D) (by omega)
    (recoverySupport_card_lower hP pp.qap hKD) p hp

end Praxis.Proofs.Monitor
