import Praxis.Scheme
import VCVio.OracleComp.SimSemantics.StateT.Basic
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Params

namespace Praxis.Proofs

open OracleComp OracleSpec

variable {P : Params}

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def budgets (Q QH : ℕ) : QueryCount CallKind
  | .group => Q
  | .hf => QH
  | .kdf => QH

noncomputable def capComp (oa : OracleComp (AdvModel P) Bool)
    (left : QueryCount CallKind) : OracleComp (AdvModel P) Bool := by
  classical
  exact OracleComp.construct (C := fun _ => QueryCount CallKind → OracleComp (AdvModel P) Bool)
    (fun b _ => pure b)
    (fun t _ rec left =>
      if callCost t ≤ left then
        (liftM (OracleSpec.query t) : OracleComp (AdvModel P) _) >>= fun u => rec u (left - callCost t)
      else pure false) oa left

@[simp] theorem capComp_pure (b : Bool) (left : QueryCount CallKind) :
    capComp (pure b : OracleComp (AdvModel P) Bool) left = pure b := rfl

theorem capComp_query_bind (t : (AdvModel P).Domain)
    (k : (AdvModel P).Range t → OracleComp (AdvModel P) Bool)
    (left : QueryCount CallKind) :
    capComp ((liftM (OracleSpec.query t) : OracleComp (AdvModel P) _) >>= k) left =
      if callCost t ≤ left then
        (liftM (OracleSpec.query t) : OracleComp (AdvModel P) _) >>= fun u => capComp (k u) (left - callCost t)
      else pure false := rfl

noncomputable def cap (Q QH : ℕ) (A : Adversary P) : Adversary P :=
  ⟨fun pv hdr => capComp (A.run pv hdr) (budgets Q QH)⟩

private def counted {σ : Type} (impl : QueryImpl (AdvModel P) (StateT σ ProbComp))
    (oa : OracleComp (AdvModel P) Bool) (s : σ) :
    ProbComp ((Bool × QueryCount CallKind) × σ) :=
  ((simulateQ (impl.withCost callCost) oa).run).run s

private theorem counted_step {σ : Type}
    (impl : QueryImpl (AdvModel P) (StateT σ ProbComp))
    (t : (AdvModel P).Domain) (k : (AdvModel P).Range t → OracleComp (AdvModel P) Bool)
    (s : σ) :
    counted impl ((liftM (OracleSpec.query t) : OracleComp (AdvModel P) _) >>= k) s = (do
      let us ← (impl t).run s
      let z ← counted impl (k us.1) us.2
      pure ((z.1.1, callCost t + z.1.2), z.2)) := by
  simp [counted, simulateQ_bind, WriterT.run_bind,
    QueryImpl.withCost_apply, StateT.run_bind, monad_norm]

private theorem prob_support_nonempty {α : Type} (oa : ProbComp α) :
    (support oa).Nonempty := by
  induction oa using ProbComp.inductionOn with
  | pure a => exact ⟨a, by simp⟩
  | query_bind n k ih =>
    obtain ⟨a, ha⟩ := ih 0
    exact ⟨a, (mem_support_bind_iff ..).mpr ⟨0, by simp, ha⟩⟩

private theorem counted_cap_eq {σ : Type}
    (impl : QueryImpl (AdvModel P) (StateT σ ProbComp))
    (oa : OracleComp (AdvModel P) Bool) (left : QueryCount CallKind) (s : σ)
    (h : ∀ z ∈ support (counted impl oa s), z.1.2 ≤ left) :
    counted impl (capComp oa left) s = counted impl oa s := by
  induction oa using OracleComp.inductionOn generalizing left s with
  | pure b => rfl
  | query_bind t k ih =>
    have hstep : ∀ us ∈ support ((impl t).run s),
        ∀ z ∈ support (counted impl (k us.1) us.2), callCost t + z.1.2 ≤ left := by
      intro us hus z hz
      apply h ((z.1.1, callCost t + z.1.2), z.2)
      rw [counted_step]
      exact (mem_support_bind_iff ..).mpr ⟨us, hus,
        (mem_support_bind_iff ..).mpr ⟨z, hz, by simp⟩⟩
    have ht : callCost t ≤ left := by
      obtain ⟨us, hus⟩ := prob_support_nonempty ((impl t).run s)
      obtain ⟨z, hz⟩ := prob_support_nonempty (counted impl (k us.1) us.2)
      exact le_trans (by intro c; exact Nat.le_add_right _ _) (hstep us hus z hz)
    rw [capComp_query_bind, if_pos ht, counted_step, counted_step]
    apply bind_congr_of_forall_mem_support
    intro us hus
    rw [ih us.1 (left - callCost t) us.2]
    intro z hz c
    have hc := hstep us hus z hz c
    change callCost t c + z.1.2 c ≤ left c at hc
    change z.1.2 c ≤ left c - callCost t c
    omega

private theorem counted_forget {σ : Type}
    (impl : QueryImpl (AdvModel P) (StateT σ ProbComp))
    (oa : OracleComp (AdvModel P) Bool) (s : σ) :
    (fun z => (z.1.1, z.2)) <$> counted impl oa s = (simulateQ impl oa).run s := by
  have h := congrArg (fun x : StateT σ ProbComp Bool => x.run s)
    (QueryImpl.fst_map_run_withCost impl callCost oa)
  simpa [StateT.run_map, counted] using h

private theorem simulate_cap_eq {σ : Type}
    (impl : QueryImpl (AdvModel P) (StateT σ ProbComp))
    (oa : OracleComp (AdvModel P) Bool) (left : QueryCount CallKind) (s : σ)
    (h : ∀ z ∈ support (counted impl oa s), z.1.2 ≤ left) :
    (simulateQ impl (capComp oa left)).run s = (simulateQ impl oa).run s := by
  rw [← counted_forget, counted_cap_eq impl oa left s h, counted_forget]

private theorem countedRun_decompose [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (A : Adversary P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) :
    countedRun σ A pp m = (do
      let es ← (encGame σ pp m).run OracleState.empty
      let z ← counted (gameImpl σ) (A.run es.1.pv es.1.header) es.2
      pure ((es.1, z.1), z.2)) := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp [countedRun, counted, StateT.run_bind, monad_norm]

private theorem bound_after_enc [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (A : Adversary P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) (Q QH : ℕ)
    (h : ∀ z ∈ support (countedRun σ A pp m), z.1.2.2 ≤ budgets Q QH)
    (es : EncOut P × OracleState P)
    (hes : es ∈ support ((encGame σ pp m).run OracleState.empty)) :
    ∀ z ∈ support (counted (gameImpl σ) (A.run es.1.pv es.1.header) es.2),
      z.1.2 ≤ budgets Q QH := by
  intro z hz
  apply h ((es.1, z.1), z.2)
  rw [countedRun_decompose]
  exact (mem_support_bind_iff ..).mpr ⟨es, hes,
    (mem_support_bind_iff ..).mpr ⟨z, hz, by simp⟩⟩

private theorem runWith_decompose [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (A : Adversary P) (enc : GameM P (EncOut P)) (s : OracleState P) :
    runWith σ A enc s = (do
      let es ← enc.run s
      let z ← (simulateQ (gameImpl σ) (A.run es.1.pv es.1.header)).run es.2
      pure ((es.1, z.1), z.2)) := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  simp [runWith, StateT.run_bind, monad_norm]

theorem runWith_cap_eq [Fact (Nat.Prime P.q)] (σ : LabelEncoding P)
    (A : Adversary P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) (Q QH : ℕ)
    (h : ∀ z ∈ support (countedRun σ A pp m), z.1.2.2 ≤ budgets Q QH) :
    runWith σ (cap Q QH A) (encGame σ pp m) OracleState.empty =
      runWith σ A (encGame σ pp m) OracleState.empty := by
  rw [runWith_decompose, runWith_decompose]
  apply bind_congr_of_forall_mem_support
  intro es hes
  change ((simulateQ (gameImpl σ) (capComp (A.run es.1.pv es.1.header) (budgets Q QH))).run es.2 >>= _) = _
  rw [simulate_cap_eq (gameImpl σ) _ _ _ (bound_after_enc σ A pp m Q QH h es hes)]

end Praxis.Proofs
