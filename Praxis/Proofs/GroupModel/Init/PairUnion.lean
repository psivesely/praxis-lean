import Praxis.Proofs.GroupModel.Init.Pair
import Praxis.Proofs.GroupModel.Init.Union
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Init.Counts
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

theorem keys1_length_general {P : Params} [Fact (Nat.Prime P.q)]
    (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (keys1 P).length = (pubView σ pp v c).g1.length := by
  rw [pubView_g1_length]
  simp [keys1]

theorem keys1_length_main (ch : AdmissibleChoice P0) (S : Relation P0) :
    (keys1 P0).length = Constants.L1 := by
  let σ : LabelEncoding P0 := fun _ => Classical.choice inferInstance
  let c := (Classical.choice (ppOf_coins ch S)).1
  rw [keys1_length_general σ (ppOf ch S) (fun _ => 0) c]
  exact pubView_g1_length_main σ (ppOf ch S) (fun _ => 0) c

def G1InitialCollision (pp : PublicParams P0) (c : Coins P0) : Prop :=
  ∃ a ∈ keys1 P0, ∃ b ∈ keys1 P0,
    e1At pp (Assign.ofCoins c) a = e1At pp (Assign.ofCoins c) b ∧
      ¬ FormalEq1 pp (Pi.single a 1) (Pi.single b 1)

theorem g1_initial_collision_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) :
    Pr[fun c => G1InitialCollision (ppOf ch S) c.1 | coinLaw (ppOf ch S)] ≤
      (Nat.choose Constants.L1 2 : ENNReal) * ENNReal.ofReal (Constants.eps_f : ℝ) := by
  classical
  let I := Fin (keys1 P0).length
  let E : I → I → {c : Coins P0 // ValidCoins (ppOf ch S).qap c} → Prop :=
    fun i j c => e1At (ppOf ch S) (Assign.ofCoins c.1) ((keys1 P0).get i) =
        e1At (ppOf ch S) (Assign.ofCoins c.1) ((keys1 P0).get j) ∧
      ¬ FormalEq1 (ppOf ch S) (Pi.single ((keys1 P0).get i) 1)
        (Pi.single ((keys1 P0).get j) 1)
  have hs : ∀ i j c, E i j c → E j i c := by
    intro i j c ⟨he, hn⟩
    refine ⟨he.symm, ?_⟩
    intro h
    apply hn
    intro ω hv
    exact (h ω hv).symm
  have hb : ∀ i j, i ≠ j → Pr[E i j | coinLaw (ppOf ch S)] ≤
      ENNReal.ofReal (Constants.eps_f : ℝ) := by
    intro i j _
    by_cases hn : ¬ FormalEq1 (ppOf ch S) (Pi.single ((keys1 P0).get i) 1)
        (Pi.single ((keys1 P0).get j) 1)
    · have h := g1_initial_pair_bound ch S hS A _ _ hn
      have hne : Pr[fun c => e1At (ppOf ch S) (Assign.ofCoins c.1) ((keys1 P0).get i) =
          e1At (ppOf ch S) (Assign.ofCoins c.1) ((keys1 P0).get j) |
          coinLaw (ppOf ch S)] ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one
      have hp := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_toReal hne] at hp
      exact (probEvent_mono'' (fun _ h => h.1)).trans hp
    · have hz : Pr[E i j | coinLaw (ppOf ch S)] = 0 := by
        apply probEvent_eq_zero
        intro c _ h
        exact hn h.2
      simp [hz]
  have hu := unordered_pair_union (coinLaw (ppOf ch S)) E
    (ENNReal.ofReal (Constants.eps_f : ℝ)) hs hb
  have hm : Pr[fun c => G1InitialCollision (ppOf ch S) c.1 | coinLaw (ppOf ch S)] ≤
      Pr[fun c => ∃ i j, i ≠ j ∧ E i j c | coinLaw (ppOf ch S)] := by
    apply probEvent_mono''
    rintro c ⟨a, ha, b, hb, he, hn⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hb
    refine ⟨i, j, ?_, he, hn⟩
    intro hij
    subst j
    exact hn (fun _ _ => rfl)
  apply hm.trans
  simpa only [I, Fintype.card_fin, keys1_length_main ch S] using hu

end Praxis.Proofs.GroupModel
