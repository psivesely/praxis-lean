import Praxis.Proofs.GroupModel.Init.Pair
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

variable {P : Params} [Fact (Nat.Prime P.q)] [NeZero P.q]

def replaceSearch (d : QAPData P) (c : {c : Coins P // ValidCoins d c})
    (r : SearchSample P) : {c : Coins P // ValidCoins d c} :=
  ⟨(c.1.1, r, c.1.2.2), c.2⟩

def swapSearch (d : QAPData P) :
    ({c : Coins P // ValidCoins d c} × {c : Coins P // ValidCoins d c}) ≃
    ({c : Coins P // ValidCoins d c} × {c : Coins P // ValidCoins d c}) where
  toFun z := (replaceSearch d z.1 z.2.1.2.1, replaceSearch d z.2 z.1.1.2.1)
  invFun z := (replaceSearch d z.1 z.2.1.2.1, replaceSearch d z.2 z.1.1.2.1)
  left_inv z := by cases z with | mk a b => cases a; cases b; rfl
  right_inv z := by cases z with | mk a b => cases a; cases b; rfl

theorem e2At_replaceSearch (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (c : {c : Coins P // ValidCoins pp.qap c}) (s : SearchSample P)
    (r : Algebra.Vec (Fq P) P.N) (a : Option (G2Idx P)) :
    e2At pp v ⟨(replaceSearch pp.qap c s).1, r⟩ a = e2At pp v ⟨c.1, r⟩ a := by
  cases a with
  | none => rfl
  | some a =>
    cases a <;> simp [e2At, g2Exp, r1ExpAt, r2Exp, H2, legScale, legScaleAt, bOf, coin,
      sectorScale, legMask, gamma, piAt, crossVal, cTie, kummerAtU, replaceSearch]

theorem uniform_pair_law (T : Type) [Fintype T] [Nonempty T] :
    letI := SampleableType.ofFintype T
    letI := SampleableType.ofFintype (T × T)
    𝒮[(do let x ← $ᵗ T; let y ← $ᵗ T; pure (x, y))] = 𝒮[$ᵗ (T × T)] := by
  classical
  letI := SampleableType.ofFintype T
  letI := SampleableType.ofFintype (T × T)
  apply evalSPMF_ext
  intro z
  rw [probOutput_bind_bind_prod_mk_eq_mul']
  simp only [show (fun x : T => x) = id from rfl, id_map]
  simp only [probOutput_uniformSample, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]

noncomputable def validCoinLaw (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}] :
    ProbComp {c : Coins P // ValidCoins pp.qap c} :=
  letI := SampleableType.ofFintype {c : Coins P // ValidCoins pp.qap c}
  $ᵗ _

theorem swapSearch_law (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}] :
    let law := (do let c ← validCoinLaw pp; let d ← validCoinLaw pp; pure (c, d))
    𝒮[swapSearch pp.qap <$> law] = 𝒮[law] := by
  classical
  let C := {c : Coins P // ValidCoins pp.qap c}
  letI : SampleableType C := SampleableType.ofFintype C
  letI : SampleableType (C × C) := SampleableType.ofFintype (C × C)
  let law : ProbComp (C × C) := do
    let c ← validCoinLaw pp
    let d ← validCoinLaw pp
    pure (c, d)
  have hu : 𝒮[law] = 𝒮[$ᵗ (C × C)] := by
    exact uniform_pair_law C
  calc
    𝒮[swapSearch pp.qap <$> law] = 𝒮[swapSearch pp.qap <$> ($ᵗ (C × C))] :=
      evalSPMF_map_eq_of_evalSPMF_eq hu _
    _ = 𝒮[$ᵗ (C × C)] := by
      apply evalSPMF_ext
      exact probOutput_map_bijective_uniformSample (C × C) (swapSearch pp.qap).bijective
    _ = 𝒮[law] := hu.symm

theorem g2_pair_average (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (A : FormMatrix P) (a b : Option (G2Idx P)) (eps : ENNReal)
    (hbound : ∀ r : Algebra.Vec (Fq P) P.N,
      Pr[fun c => e2At pp (formVec A) ⟨c.1, r⟩ a =
        e2At pp (formVec A) ⟨c.1, r⟩ b | validCoinLaw pp] ≤ eps) :
    Pr[fun c => e2At pp (formVec A) (Assign.ofCoins c.1) a =
      e2At pp (formVec A) (Assign.ofCoins c.1) b | validCoinLaw pp] ≤ eps := by
  classical
  let C := {c : Coins P // ValidCoins pp.qap c}
  letI : SampleableType C := SampleableType.ofFintype C
  let law : ProbComp (C × C) := do
    let d ← validCoinLaw pp
    let c ← validCoinLaw pp
    pure (d, c)
  let E : C × C → Prop := fun z =>
    e2At pp (formVec A) (Assign.ofCoins z.2.1) a =
      e2At pp (formVec A) (Assign.ofCoins z.2.1) b
  have hs : Pr[E | law] = Pr[fun z => E (swapSearch pp.qap z) | law] := by
    have h := OracleComp.probEvent_congr' (p := E) (q := E)
      (fun _ _ => Iff.rfl) (swapSearch_law pp)
    simpa only [probEvent_map, Function.comp_def] using h.symm
  have he : Pr[E | law] =
      Pr[fun c => e2At pp (formVec A) (Assign.ofCoins c.1) a =
        e2At pp (formVec A) (Assign.ofCoins c.1) b | validCoinLaw pp] := by
    simp only [law, bind_pure_comp]
    rw [probEvent_bind_of_const (validCoinLaw pp)
      (r := Pr[fun c => e2At pp (formVec A) (Assign.ofCoins c.1) a =
        e2At pp (formVec A) (Assign.ofCoins c.1) b | validCoinLaw pp]) (by
      intro d hd
      simp only [probEvent_map, Function.comp_def, E])]
    have hz : Pr[⊥ | validCoinLaw pp] = 0 := by
      change Pr[⊥ | $ᵗ C] = 0
      exact probFailure_uniformSample C
    simp only [hz, tsub_zero, one_mul]
  rw [← he, hs]
  simp only [law, bind_pure_comp]
  apply probEvent_bind_le_of_forall_le
  intro d hd
  simp only [probEvent_map, Function.comp_def]
  have hev (c : C) : E (swapSearch pp.qap (d, c)) ↔
      e2At pp (formVec A) ⟨c.1, rField d.1.2.1⟩ a =
        e2At pp (formVec A) ⟨c.1, rField d.1.2.1⟩ b := by
    change e2At pp (formVec A) ⟨(replaceSearch pp.qap c d.1.2.1).1, rField d.1.2.1⟩ a =
      e2At pp (formVec A) ⟨(replaceSearch pp.qap c d.1.2.1).1, rField d.1.2.1⟩ b ↔ _
    rw [e2At_replaceSearch, e2At_replaceSearch]
  have heq : (fun c : C => E (swapSearch pp.qap (d, c))) =
      (fun c => e2At pp (formVec A) ⟨c.1, rField d.1.2.1⟩ a =
        e2At pp (formVec A) ⟨c.1, rField d.1.2.1⟩ b) := funext fun c => propext (hev c)
  rw [heq]
  exact hbound (rField d.1.2.1)

theorem g2_initial_pair_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (a b : Option (G2Idx P0))
    (hne : ¬ FormalEq2 (ppOf ch S) (formVec A) (Pi.single a 1) (Pi.single b 1)) :
    (Pr[fun c => e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) a =
      e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) b |
      coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ) := by
  have hb : Pr[fun c => e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) a =
      e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) b |
      coinLaw (ppOf ch S)] ≤ ENNReal.ofReal (Constants.eps_f : ℝ) := by
    apply g2_pair_average (ppOf ch S) A a b
    intro r
    have hn : ¬ ∀ c : Coins P0, ValidCoins (ppOf ch S).qap c →
        e2At (ppOf ch S) (formVec A) ⟨c, r⟩ a =
          e2At (ppOf ch S) (formVec A) ⟨c, r⟩ b := by
      intro h
      exact hne (g2_initial_identity_all_search ch S hS A a b r h)
    have h := g2_fixed_pair_bound ch S hS A a b r hn
    have ht : Pr[fun c => e2At (ppOf ch S) (formVec A) ⟨c.1, r⟩ a =
        e2At (ppOf ch S) (formVec A) ⟨c.1, r⟩ b |
        coinLaw (ppOf ch S)] ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one
    have he := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_toReal ht] at he
    exact he
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hn : 0 ≤ (Constants.eps_f : ℝ) := by
    exact_mod_cast (show 0 ≤ Constants.eps_f by norm_num [Constants.eps_f])
  simpa only [ENNReal.toReal_ofReal hn] using he

end Praxis.Proofs.GroupModel
