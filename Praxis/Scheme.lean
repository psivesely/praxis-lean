import Praxis.Reduction
import Praxis.Domain
import Praxis.Encryption.BN254
import Praxis.Dec
import Praxis.Enc
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Kummer
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Search
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Games
import Praxis.Algebra.Definitions.MSIS
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open OracleComp OracleSpec

open Praxis.Algebra (Vec CoeffVec RingMatrix MSISRing)

instance main_prime : Fact (Nat.Prime Params.main.q) :=
  ⟨Encryption.BN254.r_prime⟩

theorem main_d_ne_zero : Params.main.d ≠ 0 := by decide

theorem main_label_fit : Params.main.q ≤ 2 ^ Params.main.labelBits := by decide

instance main_encodings : Nonempty (ZMod Params.main.q ↪ Label Params.main) :=
  encoding_nonempty main_label_fit

theorem validCoins_nonempty {P : Params} [Fact (Nat.Prime P.q)] (Dm : QAPData P)
    (hD : Fintype.card (QAPIndex P) < P.q) (hK : P.K1 + 1 < P.q)
    (hr : Nonempty (SearchSample P)) : Nonempty {c : Coins P // ValidCoins Dm c} := by
  classical
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  have hcard : (Finset.univ : Finset (Fq P)).card = P.q := by simp [ZMod.card]
  obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Finset.univ.image Dm.point) (t := (Finset.univ : Finset (Fq P))) (by
      rw [hcard]
      exact lt_of_le_of_lt (Finset.card_image_le.trans (by simp)) hD)
  obtain ⟨ε, -, hε⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert 0 (Finset.univ.image fun k1 : Fin P.K1 => -(betaF P ^ (2 * k1.val))⁻¹))
    (t := (Finset.univ : Finset (Fq P))) (by
      rw [hcard]
      refine lt_of_le_of_lt (Finset.card_insert_le _ _) ?_
      refine lt_of_le_of_lt (Nat.add_le_add_right (Finset.card_image_le.trans (by simp)) 1) hK)
  obtain ⟨r⟩ := hr
  refine ⟨⟨(0, r, fun s => match s with
    | .tau => τ
    | .eps => ε
    | _ => 1), ?_, ?_, ?_, ?_⟩⟩
  · intro k hk
    exact hτ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩)
  · intro s hs
    cases s <;> simp_all [ScalarCoin.inUnits]
  · intro h
    exact hε (Finset.mem_insert.mpr (Or.inl h))
  · intro k1 h
    exact hε (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k1, Finset.mem_univ _, h.symm⟩))

theorem main_validCoins_nonempty (Dm : QAPData Params.main) :
    Nonempty {c : Coins Params.main // ValidCoins Dm c} := by
  have hg : 0 < Params.main.g := by decide
  have hcard : Fintype.card (QAPIndex Params.main) =
      (Params.main.N + 1) + (1 + Params.main.gatesMax * Params.main.U) := by
    simp [QAPIndex, Fintype.card_sum, Fintype.card_prod]
  refine validCoins_nonempty Dm ?_ (by decide) ⟨(⟨0, hg⟩, fun _ => ⟨0, hg⟩)⟩
  rw [hcard]
  decide

def canonLabel : ZMod Params.main.q ↪ Label Params.main :=
  ⟨_, Algebra.ofNat_val_injective main_label_fit⟩

def canonName : (expGroups Params.main.q).GT → ClassName Params.main :=
  labelName canonLabel

structure Scheme where

  params : Params
  [prime : Fact (Nat.Prime params.q)]
  [encodings : Nonempty (ZMod params.q ↪ Label params)]

  ring : MSISRing params.q params.d

  groups : BilinearGroups params.q

  className : groups.GT → ClassName params

  domain : DomainMap params

  setup : Relation params → PublicParams params

  coins_nonempty : ∀ S, Nonempty {c : Coins params // ValidCoins (setup S).qap c}

  enc : FormOracle params → KDF params → Relation params → Msg params →
    ProbComp (Ciphertext groups)

  dec : FormOracle params → KDF params → PublicParams params → Ciphertext groups →
    Vec (Fq params) params.N → Option (Msg params)

  extractor : SparseRelation params → PubView params → List (TrOp params) →
    UnitComp params.q (Option (Vec (Fq params) params.N))

  reduction : Relation params → Msg params → Adversary params →
    RingMatrix ring params.rows params.cols → ProbComp (Option (CoeffVec params.d params.cols))

attribute [instance] Scheme.prime Scheme.encodings

noncomputable def scheme (ch : AdmissibleChoice Params.main) : Scheme where
  params := Params.main
  ring := msisRing Params.main main_d_ne_zero
  groups := expGroups Params.main.q
  className := canonName
  domain := domainMap ch
  setup := Praxis.setup (domainMap ch)
  coins_nonempty := fun S => main_validCoins_nonempty (Praxis.setup (domainMap ch) S).qap
  enc := fun HF kdf S m =>
    haveI := main_validCoins_nonempty (Praxis.setup (domainMap ch) S).qap
    Enc (expGroups Params.main.q) HF kdf canonName (Praxis.setup (domainMap ch) S) m
  dec := fun HF kdf pp ct x => decRef (expGroups Params.main.q) HF kdf canonName pp ct x
  extractor := extractorC
  reduction := fun S m A =>
    haveI := main_validCoins_nonempty (Praxis.setup (domainMap ch) S).qap
    Praxis.reduction main_d_ne_zero (Praxis.setup (domainMap ch) S) m A

namespace Scheme

variable (sch : Scheme)

noncomputable def decExp (S : Relation sch.params) (m : Msg sch.params)
    (x : Vec (Fq sch.params) sch.params.N) : ProbComp (Option (Msg sch.params)) :=
  haveI : NeZero sch.params.q := ⟨(Fact.out : Nat.Prime sch.params.q).ne_zero⟩
  do
    let HF ← $ᵗ (FormOracle sch.params)
    let kdf ← $ᵗ (KDF sch.params)
    let ct ← sch.enc HF kdf S m
    pure (sch.dec HF kdf (sch.setup S) ct x)

noncomputable def extractorLaw : ExtractorLaw sch.params :=
  fun S pub tr => runUnits (sch.extractor (sparseOf S) pub tr)

noncomputable def extractExp (S : Relation sch.params) (m0 m1 : Msg sch.params)
    (A : Adversary sch.params) : ProbComp Bool :=
  haveI := sch.coins_nonempty S
  extractGame (sch.setup S) m0 m1 A sch.extractorLaw

noncomputable def extractInputs (S : Relation sch.params) (m0 m1 : Msg sch.params)
    (A : Adversary sch.params) : ProbComp (PubView sch.params × List (TrOp sch.params)) :=
  haveI := sch.coins_nonempty S
  haveI : NeZero sch.params.q := ⟨(Fact.out : Nat.Prime sch.params.q).ne_zero⟩
  do
    let b ← $ᵗ Bool
    let σ ← sampleEncoding
    let m := if b then m1 else m0
    let out ← runWith σ A (encGame σ (sch.setup S) m) OracleState.empty
    pure (out.1.1.pv, out.2.tr)

noncomputable def succ (S : Relation sch.params) (m : Msg sch.params) (A : Adversary sch.params) :
    ℝ :=
  haveI : NeZero sch.params.q := ⟨(Fact.out : Nat.Prime sch.params.q).ne_zero⟩
  msisSucc sch.ring sch.params.eta (sch.reduction S m A)

end Scheme

end Praxis
