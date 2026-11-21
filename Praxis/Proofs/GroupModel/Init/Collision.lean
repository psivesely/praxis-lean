import Praxis.Proofs.GroupModel.Init.Monitor
import Praxis.Proofs.GroupModel.Init.Publication
import Praxis.Proofs.GroupModel.Init.PairUnion
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Init.Counts
import Praxis.Proofs.GroupModel.Init.Pair
import Praxis.Proofs.GroupModel.Init.Union
import Praxis.Proofs.GroupModel.Init.Values
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.GroupModel

open GroupModel.Sorted

open OracleComp OracleSpec

def G2InitialCollision (pp : PublicParams P0) (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N)
    (c : Coins P0) : Prop :=
  ∃ a ∈ keys2 P0, ∃ b ∈ keys2 P0,
    e2At pp v (Assign.ofCoins c) a = e2At pp v (Assign.ofCoins c) b ∧
      ¬ FormalEq2 pp v (Pi.single a 1) (Pi.single b 1)

def GTInitialCollision (pp : PublicParams P0) (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N)
    (c : Coins P0) : Prop :=
  ∃ a b : Option Unit,
    valT pp v (Assign.ofCoins c) (gtInit a) = valT pp v (Assign.ofCoins c) (gtInit b) ∧
      ¬ FormalEqT pp v (gtInit a) (gtInit b)

theorem firstMark_init_collision (pp : PublicParams P0) (w : WorldOut P0)
    (hpv : w.out.pv = pubView w.enc pp (formsOfRun w) w.out.coins)
    (hm : firstMark pp w = some .init) :
    G1InitialCollision pp w.out.coins ∨
      G2InitialCollision pp (formsOfRun w) w.out.coins ∨
      GTInitialCollision pp (formsOfRun w) w.out.coins := by
  have hc := firstMark_init_conflict pp w hm
  simp only [InitConflict, idealCtx] at hc
  rw [hpv, pubView_g1_keys, pubView_g2_keys, pubView_gt_keys] at hc
  rcases hc with hc | hc | hc
  · left
    rcases hc with ⟨a, ha, b, hb, he, hn⟩
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    exact ⟨a', ha', b', hb', (w.enc .g₁).injective he, hn⟩
  · right; left
    rcases hc with ⟨a, ha, b, hb, he, hn⟩
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    exact ⟨a', ha', b', hb', (w.enc .g₂).injective he, hn⟩
  · right; right
    rcases hc with ⟨a, ha, b, hb, he, hn⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
    refine ⟨a, b, ?_, hn⟩
    simp only [valT_init, Assign.ofCoins]
    exact (w.enc .gₜ).injective he

theorem gt_initial_collision_iff (pp : PublicParams P0)
    (v : Fin P0.n → Algebra.Vec (Fq P0) P0.N) (c : Coins P0) :
    GTInitialCollision pp v c ↔
      valT pp v (Assign.ofCoins c) (gtInit none) =
          valT pp v (Assign.ofCoins c) (gtInit (some ())) ∧
        ¬ FormalEqT pp v (gtInit none) (gtInit (some ())) := by
  constructor
  · rintro ⟨a, b, he, hn⟩
    cases a with
    | none =>
      cases b with
      | none => exact (hn (fun _ _ => rfl)).elim
      | some b => cases b; exact ⟨he, hn⟩
    | some a =>
      cases a
      cases b with
      | none =>
        refine ⟨he.symm, ?_⟩
        intro h
        exact hn (fun ω hv => (h ω hv).symm)
      | some b => cases b; exact (hn (fun _ _ => rfl)).elim
  · rintro ⟨he, hn⟩
    exact ⟨none, some (), he, hn⟩

theorem gt_initial_collision_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) :
    Pr[fun c => GTInitialCollision (ppOf ch S) (formVec A) c.1 | coinLaw (ppOf ch S)] ≤
      ENNReal.ofReal (Constants.eps_f : ℝ) := by
  classical
  by_cases hn : ¬ FormalEqT (ppOf ch S) (formVec A) (gtInit none) (gtInit (some ()))
  · have h := gt_initial_pair_bound ch S hS A none (some ()) hn
    have hne : Pr[fun c => valT (ppOf ch S) (formVec A) (Assign.ofCoins c.1) (gtInit none) =
        valT (ppOf ch S) (formVec A) (Assign.ofCoins c.1) (gtInit (some ())) |
        coinLaw (ppOf ch S)] ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one
    have hp := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_toReal hne] at hp
    exact (probEvent_mono'' (fun _ hc => ((gt_initial_collision_iff _ _ _).mp hc).1)).trans hp
  · have hz : Pr[fun c => GTInitialCollision (ppOf ch S) (formVec A) c.1 |
        coinLaw (ppOf ch S)] = 0 := by
      apply probEvent_eq_zero
      intro c _ hc
      exact hn ((gt_initial_collision_iff _ _ _).mp hc).2
    simp [hz]

theorem keys2_length_general {P : Params} [Fact (Nat.Prime P.q)]
    (σ : LabelEncoding P) (pp : PublicParams P)
    (v : Fin P.n → Algebra.Vec (Fq P) P.N) (c : Coins P) :
    (keys2 P).length = (pubView σ pp v c).g2.length := by
  rw [pubView_g2_length]
  simp [keys2]

theorem keys2_length_main (ch : AdmissibleChoice P0) (S : Relation P0) :
    (keys2 P0).length = Constants.L2 := by
  let σ : LabelEncoding P0 := fun _ => Classical.choice inferInstance
  let c := (Classical.choice (ppOf_coins ch S)).1
  rw [keys2_length_general σ (ppOf ch S) (fun _ => 0) c]
  exact pubView_g2_length_main σ (ppOf ch S) (fun _ => 0) c

theorem g2_initial_collision_of_pairs (ch : AdmissibleChoice P0) (S : Relation P0)
    (A : FormMatrix P0)
    (hpair : ∀ a b : Option (G2Idx P0),
      ¬ FormalEq2 (ppOf ch S) (formVec A) (Pi.single a 1) (Pi.single b 1) →
        (Pr[fun c => e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) a =
          e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) b |
          coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ)) :
    Pr[fun c => G2InitialCollision (ppOf ch S) (formVec A) c.1 | coinLaw (ppOf ch S)] ≤
      (Nat.choose Constants.L2 2 : ENNReal) * ENNReal.ofReal (Constants.eps_f : ℝ) := by
  classical
  let I := Fin (keys2 P0).length
  let E : I → I → {c : Coins P0 // ValidCoins (ppOf ch S).qap c} → Prop :=
    fun i j c => e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) ((keys2 P0).get i) =
        e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) ((keys2 P0).get j) ∧
      ¬ FormalEq2 (ppOf ch S) (formVec A) (Pi.single ((keys2 P0).get i) 1)
        (Pi.single ((keys2 P0).get j) 1)
  have hs : ∀ i j c, E i j c → E j i c := by
    intro i j c ⟨he, hn⟩
    refine ⟨he.symm, ?_⟩
    intro h
    exact hn (fun ω hv => (h ω hv).symm)
  have hb : ∀ i j, i ≠ j → Pr[E i j | coinLaw (ppOf ch S)] ≤
      ENNReal.ofReal (Constants.eps_f : ℝ) := by
    intro i j _
    by_cases hn : ¬ FormalEq2 (ppOf ch S) (formVec A) (Pi.single ((keys2 P0).get i) 1)
        (Pi.single ((keys2 P0).get j) 1)
    · have h := hpair _ _ hn
      have hne : Pr[fun c => e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) ((keys2 P0).get i) =
          e2At (ppOf ch S) (formVec A) (Assign.ofCoins c.1) ((keys2 P0).get j) |
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
  have hm : Pr[fun c => G2InitialCollision (ppOf ch S) (formVec A) c.1 |
      coinLaw (ppOf ch S)] ≤
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
  simpa only [I, Fintype.card_fin, keys2_length_main ch S] using hu

end Praxis.Proofs.GroupModel
