import Praxis.Proofs.Basic

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

theorem finite_event_union {M : Type → Type} [MonadLiftT M SPMF]
    {C I : Type} [DecidableEq I] (μ : M C)
    (s : Finset I) (E : I → C → Prop) :
    Pr[fun c => ∃ i ∈ s, E i c | μ] ≤ ∑ i ∈ s, Pr[E i | μ] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.mem_insert, exists_eq_or_imp, Finset.sum_insert hi]
    exact (probEvent_or_le μ _ _).trans (add_le_add_right ih _)

theorem unordered_pair_union {M : Type → Type} [MonadLiftT M SPMF]
    {C I : Type} [Fintype I] [DecidableEq I] (μ : M C)
    (E : I → I → C → Prop) (eps : ENNReal)
    (hsym : ∀ i j c, E i j c → E j i c)
    (hbound : ∀ i j, i ≠ j → Pr[E i j | μ] ≤ eps) :
    Pr[fun c => ∃ i j, i ≠ j ∧ E i j c | μ] ≤
      (Nat.choose (Fintype.card I) 2 : ENNReal) * eps := by
  classical
  let S : Finset (Finset I) := Finset.univ.powersetCard 2
  let F := fun (t : Finset I) c =>
    ∀ i ∈ t, ∀ j ∈ t, i ≠ j → E i j c
  have hf : ∀ t ∈ S, Pr[F t | μ] ≤ eps := by
    intro t ht
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp ht).2
    apply le_trans (probEvent_mono'' (fun c hc => ?_)) (hbound i j hij)
    exact hc i (by simp) j (by simp) hij
  calc
    _ ≤ Pr[fun c => ∃ t ∈ S, F t c | μ] := by
      apply probEvent_mono''
      rintro c ⟨i, j, hij, he⟩
      refine ⟨{i, j}, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp [hij]⟩, ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact he
      · exact hsym _ _ _ he
      · exact (hab rfl).elim
    _ ≤ ∑ t ∈ S, Pr[F t | μ] := finite_event_union μ S F
    _ ≤ ∑ _t ∈ S, eps := Finset.sum_le_sum hf
    _ = _ := by simp [S, Finset.card_powersetCard, nsmul_eq_mul]

end Praxis.Proofs.GroupModel
