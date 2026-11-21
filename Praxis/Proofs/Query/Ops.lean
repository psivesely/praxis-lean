import Praxis.Proofs.Basic
import Praxis.Semantics.Algorithms
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Params

namespace Praxis.Proofs.Query

open OracleComp OracleSpec

private lemma hfLazy_tr {P : Params} [NeZero P.q]
    (i : Seed P × FormIndex P) (st : OracleState P) :
    ∀ z ∈ support ((hfLazy i).run st), z.2.tr = st.tr := by
  intro z hz
  unfold hfLazy at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp at hz
    subst z
    rfl
  · simp [StateT.run_bind, StateT.run_modify] at hz
    obtain ⟨a, rfl⟩ := hz
    rfl

private lemma kdfLazy_tr {P : Params} (nm : ClassName P) (st : OracleState P) :
    ∀ z ∈ support ((kdfLazy nm).run st), z.2.tr = st.tr := by
  intro z hz
  unfold kdfLazy at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp at hz
    subst hz
    rfl
  · simp [StateT.run_bind, StateT.run_modify] at hz
    obtain ⟨a, rfl⟩ := hz
    rfl

private lemma handOut_tr {P : Params} (qr : GQuery P) (r : qr.Result)
    (st : OracleState P) :
    ∀ z ∈ support ((handOut qr r).run st), z.2.tr = st.tr := by
  cases qr with
  | lin s a b u v => simp [handOut]
  | pair u v => simp [handOut]
  | name v =>
    cases r with
    | none => simp [handOut]
    | some nm =>
      intro z hz
      simp only [handOut, StateT.run_map] at hz
      unfold nameRef at hz
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz <;> simp at hz <;> subst z <;> rfl

private lemma groupImpl_length {P : Params} (σ : LabelEncoding P) (qr : GQuery P)
    (st : OracleState P) :
    ∀ z ∈ support ((groupImpl σ qr).run st), z.2.tr.length ≤ st.tr.length + 1 := by
  intro z hz
  unfold groupImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · have h := handOut_tr qr _ _ z hz
    simp only [h, List.length_append, List.length_singleton]
    exact le_rfl
  · rw [handOut_tr qr _ _ z hz]
    exact Nat.le_succ _

private lemma kdfImpl_tr {P : Params} (qk : KdfQuery P) (st : OracleState P) :
    ∀ z ∈ support ((kdfImpl qk).run st), z.2.tr = st.tr := by
  intro z hz
  unfold kdfImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp at hz
    subst z
    rfl
  · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_map] at hz
    obtain ⟨y, hy, rfl⟩ := mem_support_map_peel _ _ hz
    have h := kdfLazy_tr _ _ y hy
    exact h

private lemma gameImpl_length {P : Params} [NeZero P.q] (σ : LabelEncoding P)
    (t : (AdvModel P).Domain) (st : OracleState P) :
    ∀ z ∈ support ((gameImpl σ t).run st),
      z.2.tr.length ≤ st.tr.length + callCost t .group := by
  rcases t with ((t | qr) | i) | qk
  · simp [gameImpl, QueryImpl.liftTarget, callCost, isGroupQuery]
  · simpa [gameImpl, callCost, isGroupQuery] using groupImpl_length σ qr st
  · intro z hz
    have h := hfLazy_tr i st z (by simpa [gameImpl] using hz)
    simp [h, callCost, isGroupQuery]
  · intro z hz
    have h := kdfImpl_tr qk st z (by simpa [gameImpl] using hz)
    simp [h, callCost, isGroupQuery]

private lemma mapM_tr {P : Params} {α β : Type} (f : α → GameM P β)
    (hf : ∀ a st z, z ∈ support ((f a).run st) → z.2.tr = st.tr)
    (l : List α) (st : OracleState P) :
    ∀ z ∈ support ((l.mapM f).run st), z.2.tr = st.tr := by
  induction l generalizing st with
  | nil => simp
  | cons a l ih =>
    intro z hz
    simp only [List.mapM_cons, StateT.run_bind] at hz
    obtain ⟨y, hy, hz⟩ := mem_support_bind_peel _ _ hz
    obtain ⟨v, hv, hz⟩ := mem_support_bind_peel _ _ hz
    have he := eq_of_mem_support_pure _ hz
    subst z
    exact (ih y.2 v hv).trans (hf a st y hy)

private lemma encGame_tr {P : Params} [Fact (Nat.Prime P.q)]
    (σ : LabelEncoding P) (pp : PublicParams P) (m : Msg P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (st : OracleState P) :
    ∀ z ∈ support ((encGame σ pp m).run st), z.2.tr = st.tr := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  intro z hz
  unfold encGame at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨seed, hseed, hz⟩ := mem_support_bind_peel _ _ hz
  unfold encAt at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨es, hes, hz⟩ := mem_support_bind_peel _ _ hz
  have hreads : es.2.tr = seed.2.tr := by
    apply mapM_tr _ _ _ _ es hes
    intro i s y hy
    simp only [StateT.run_bind] at hy
    obtain ⟨a, ha, hy⟩ := mem_support_bind_peel _ _ hy
    have he := eq_of_mem_support_pure _ hy
    subst y
    exact hfLazy_tr _ _ a ha
  obtain ⟨c, hc, hz⟩ := mem_support_bind_peel _ _ hz
  obtain ⟨pad, hpad, hz⟩ := mem_support_bind_peel _ _ hz
  have hpadtr := kdfLazy_tr _ _ pad hpad
  simp at hz
  subst z
  have hseedtr : seed.2 = st := by
    obtain ⟨a, ha, he⟩ := mem_support_bind_peel _ _ hseed
    exact congrArg Prod.snd (eq_of_mem_support_pure _ he)
  have hctr : c.2 = es.2 := by
    obtain ⟨a, ha, he⟩ := mem_support_bind_peel _ _ hc
    exact congrArg Prod.snd (eq_of_mem_support_pure _ he)
  simpa [hctr, hseedtr] using hpadtr.trans (by simpa [hctr, hseedtr] using hreads)

private lemma counted_length {P : Params} [NeZero P.q] {α : Type}
    (σ : LabelEncoding P) (oa : OracleComp (AdvModel P) α) (st : OracleState P) :
    ∀ z ∈ support (((simulateQ ((gameImpl σ).withCost callCost) oa).run).run st),
      z.2.tr.length ≤ st.tr.length + z.1.2 .group := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t oa ih =>
    intro z hz
    have step : (((simulateQ ((gameImpl σ).withCost callCost)
        ((liftM (OracleSpec.query t) : OracleComp (AdvModel P) _) >>= oa)).run).run st) =
        ((gameImpl σ t).run st >>= fun us =>
          (fun v => ((v.1.1, callCost t + v.1.2), v.2)) <$>
            (((simulateQ ((gameImpl σ).withCost callCost) (oa us.1)).run).run us.2)) := by
      simp [simulateQ_bind, QueryImpl.withCost_apply,
        WriterT.run_bind, StateT.run_bind, monad_norm]
    rw [step] at hz
    obtain ⟨us, hus, hz⟩ := mem_support_bind_peel _ _ hz
    obtain ⟨v, hv, rfl⟩ := mem_support_map_peel _ _ hz
    have hquery := gameImpl_length σ t st us hus
    have hrest := ih us.1 us.2 v hv
    change v.2.tr.length ≤ st.tr.length + (callCost t .group + v.1.2 .group)
    omega

private lemma countedRun_length {P : Params} [Fact (Nat.Prime P.q)]
    (σ : LabelEncoding P) (A : Adversary P) (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (m : Msg P) :
    ∀ z ∈ support (countedRun σ A pp m), z.2.tr.length ≤ z.1.2.2 .group := by
  have : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  intro z hz
  unfold countedRun at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨es, hes, hz⟩ := mem_support_bind_peel _ _ hz
  obtain ⟨oc, hoc, hz⟩ := mem_support_bind_peel _ _ hz
  have he := eq_of_mem_support_pure _ hz
  subst z
  have henc := encGame_tr σ pp m OracleState.empty es hes
  have hadv := counted_length σ (A.run es.1.pv es.1.header) es.2 oc hoc
  simpa [henc, OracleState.empty] using hadv

private lemma worldRun_length {P : Params} [Fact (Nat.Prime P.q)]
    [Nonempty (ZMod P.q ↪ Label P)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (A : Adversary P) (Q : ℕ) (hA : MaxCalls A .group Q) :
    ∀ w ∈ support (worldRun pp m A), w.st.tr.length ≤ Q := by
  intro w hw
  unfold worldRun at hw
  obtain ⟨σ, hσ, hw⟩ := mem_support_bind_peel _ _ hw
  obtain ⟨r, hr, hw⟩ := mem_support_bind_peel _ _ hw
  have he := eq_of_mem_support_pure _ hw
  subst w
  rw [← Semantics.countedRun_forget σ A pp m] at hr
  obtain ⟨z, hz, he⟩ := mem_support_map_peel _ _ hr
  subst r
  exact (countedRun_length σ A pp m z hz).trans (hA σ pp m z hz)

theorem sig_ops (pp : PublicParams P0) [Nonempty {c : Coins P0 // ValidCoins pp.qap c}]
    (m : Msg P0) (A : Adversary P0) (Q QH : ℕ) (hA : InClass A Q QH) :
    ∀ w ∈ support (worldRun pp m A), w.st.tr.length ≤ Q := by
  exact worldRun_length pp m A Q hA.group

end Praxis.Proofs.Query
