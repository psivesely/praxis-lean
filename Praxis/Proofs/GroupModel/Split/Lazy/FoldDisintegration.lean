import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.FieldMarginal
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Search
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.LightMarginal
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.BadTyped
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Source
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.BadNe
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.PendingVars
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.BadReal
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.GuessMarginal
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.CatalogBuild
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.GuessAssemble
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Mark
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Domination
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.Cover
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.View.NoKey
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold

open Classical

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

section Components

variable (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)

lemma lightSlot_marginal
    (hK1 : ∀ s : SearchSample P0, (∑' c : CoinDomain (ppOf ch S),
      if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) = Pr[= s | searchLaw])
    (pad : Bounds ch S .light) (fires : Record (ppOf ch S) → Option (Bounds ch S .light)) :
    (lightSlot pad fires).Marginal := by
  exact LightMarginal.lightSlot_marginal ch S hK1 pad fires

lemma fieldSlot_marginal
    (hK2 : ∀ (s : SearchSample P0) (c' : CoinDomain (ppOf ch S)),
      (∑' c : CoinDomain (ppOf ch S), if c.val.2.1 = s then
        Pr[= c | coinLaw (ppOf ch S)] * Pr[= c' | resample (ppOf ch S) c] else 0) =
      Pr[= s | searchLaw] * Pr[= c' | coinLaw (ppOf ch S)])
    (pad : Bounds ch S .field)
    (fires : Record (ppOf ch S) → Option (SearchSample P0 → Bounds ch S .field)) :
    (fieldSlot pad fires).Marginal := by
  exact FieldMarginal.fieldSlot_marginal ch S hK2 pad fires

lemma guessSlot_marginal (pad : SearchSample P0 × Bounds ch S .guess)
    (fires : Record (ppOf ch S) → Option (SearchSample P0 → Bounds ch S .guess))
    (hstd : ∀ r f, fires r = some f → ∀ s, ∃ t, f s = .guess t ∧ StdGuess (ppOf ch S) r s t) :
    (guessSlot pad fires).Marginal := by
  exact GuessMarginal.marginal pad fires hstd

lemma bad_real (ω : World (ppOf ch S)) (hω : ω ∈ support (observedRun (ppOf ch S) m A))
    (e : Collision (ppOf ch S)) (he : BadAt ω e)
    (hc : ValidCoins (ppOf ch S).qap ω.1.out.coins) :
    evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.new =
      evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.old := by
  have h := BadReal.bad_real ch S m A
  generalize observedRun (ppOf ch S) m A = obs at h hω ⊢
  exact h ω hω e he hc

lemma bad_ne (hS : InShape P0 S) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A))
    (e : Collision (ppOf ch S)) (he : BadAt ω e) : e.new ≠ e.old := by
  have h := BadNe.bad_ne ch S m A hS
  generalize observedRun (ppOf ch S) m A = obs at h hω ⊢
  exact h ω hω e he

lemma bad_typed (ω : World (ppOf ch S)) (hω : ω ∈ support (observedRun (ppOf ch S) m A))
    (e : Collision (ppOf ch S)) (he : BadAt ω e) :
    (e.sort = .g₁ → ∃ E : Expr1 P0, e.value = Exposure.value1 (ppOf ch S) E) ∧
    (e.sort = .g₂ → ∃ E : Expr2 P0,
      e.value = Exposure.value2 (ppOf ch S) (formVec ω.1.out.forms) E) ∧
    (e.sort = .gₜ → ∃ (D : ExprT P0) (ι : k),
      e.value = Exposure.valueT (ppOf ch S) (formVec ω.1.out.forms) D -
        ι • Exposure.valueKey (ppOf ch S)) := by
  have h := BadTyped.bad_typed (ppOf ch S) m A
  generalize observedRun (ppOf ch S) m A = obs at h hω ⊢
  exact h ω hω e he

lemma val_search_indep (c c' : Coins P0) (r : Vec k P0.N) (h1 : c'.1 = c.1)
    (h2 : c'.2.2 = c.2.2) :
    (∀ E, val1 (ppOf ch S) ⟨c', r⟩ E = val1 (ppOf ch S) ⟨c, r⟩ E) ∧
    (∀ v E, val2 (ppOf ch S) v ⟨c', r⟩ E = val2 (ppOf ch S) v ⟨c, r⟩ E) ∧
    (∀ v E, valT (ppOf ch S) v ⟨c', r⟩ E = valT (ppOf ch S) v ⟨c, r⟩ E) ∧
    kappa (ppOf ch S) c' = kappa (ppOf ch S) c := by
  exact Search.val_search_indep ch S c c' r h1 h2

lemma cover_bad (hS : InShape P0 S) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A)) (hc : ChargedCmp (ppOf ch S) ω.1) :
    ∃ e, BadAt ω e := by
  have h := Sync.cover_bad (ppOf ch S) m A
  generalize observedRun (ppOf ch S) m A = obs at h hω ⊢
  exact h ω hω hc

lemma cover_source (hS : InShape P0 S) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A))
    (e : Collision (ppOf ch S)) (he : BadAt ω e) (hg : GuessFree e) (hs : e.sort ≠ .gₜ) :
    ¬ IdentityAt e.value (realR ω.1) := by
  have hbt := bad_typed ch S m A
  have hbn := bad_ne ch S m A hS
  generalize observedRun (ppOf ch S) m A = obs at hbt hbn hω ⊢
  exact Source.cover_source ch S hS obs hbt hbn ω hω e he hg hs

lemma cover_mark (hS : InShape P0 S) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A)) (hc : ChargedCmp (ppOf ch S) ω.1)
    (e : Collision (ppOf ch S)) (he : BadAt ω e) (hg : GuessFree e) (hs : e.sort = .gₜ) :
    ∃ (D : ExprT P0) (ι : k),
      e.value = Exposure.valueT (ppOf ch S) (formVec ω.1.out.forms) D -
        ι • Exposure.valueKey (ppOf ch S) ∧
      ¬ GoodCmp (ppOf ch S) ω.1 D ι := by
  have h := Sync.cover_mark (ppOf ch S) (View.view_no_formal_key ch S hS) m A
  generalize observedRun (ppOf ch S) m A = obs at h hω ⊢
  exact h ω hω hc e he hg hs

lemma pending_vars_in_order (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A))
    (e : Collision (ppOf ch S)) (b : ℕ) (hb : ω.2.stop = some b) (he : badCmp ω = some e) :
    e.diff.vars ⊆ ((fullRecord ω).cut b).order.toFinset := by
  generalize hobs : observedRun (ppOf ch S) m A = obs at hω ⊢
  exact PendingVars.pending_vars_in_order (ppOf ch S) m A obs hobs ω hω e b hb he

lemma lf_catalog (hS : InShape P0 S) (Q QH : ℕ) (hA : InClass A Q QH) :
    ∃ cmp : Fin (quota (simBudget Q) .light) → Record (ppOf ch S) →
        Option (Collision (ppOf ch S)),
      ∀ ω ∈ support (observedRun (ppOf ch S) m A), ∀ e, BadAt ω e → GuessFree e →
        ∃ j, Catches cmp j ω e := by
  obtain ⟨cmp, hcmp⟩ := Catalog.catalog ch S m A Q QH hA
    (pending_vars_in_order ch S m A) .light (by simp)
  generalize observedRun (ppOf ch S) m A = obs at hcmp ⊢
  exact ⟨cmp, fun ω hω e he _ => hcmp ω hω e he⟩

lemma guess_catalog (hS : InShape P0 S) (Q QH : ℕ) (hA : InClass A Q QH) :
    ∃ cmp : Fin (quota (simBudget Q) .guess) → Record (ppOf ch S) →
        Option (Collision (ppOf ch S)),
      ∀ ω ∈ support (observedRun (ppOf ch S) m A), ∀ e, BadAt ω e → ¬ GuessFree e →
        ∃ j, Catches cmp j ω e := by
  obtain ⟨cmp, hcmp⟩ := Catalog.catalog ch S m A Q QH hA
    (pending_vars_in_order ch S m A) .guess (by simp)
  generalize observedRun (ppOf ch S) m A = obs at hcmp ⊢
  exact ⟨cmp, fun ω hω e he _ => hcmp ω hω e he⟩

lemma guess_build (hS : InShape P0 S) (Q QH : ℕ) (hA : InClass A Q QH) :
    ∃ build : Record (ppOf ch S) → Collision (ppOf ch S) → SearchSample P0 → Option GuessTest,
      (∀ r e s t, build r e s = some t → StdGuess (ppOf ch S) r s t) ∧
      ∀ ω ∈ support (observedRun (ppOf ch S) m A), ∀ e, BadAt ω e → ¬ GuessFree e →
        ∀ n e', Clean n ω → e'.sort = e.sort → e'.diff = e.diff →
          e'.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset →
          (∀ s, (build ((fullRecord ω).cut n) e' s).isSome) ∧
          ∃ t, build ((fullRecord ω).cut n) e' ω.1.out.coins.2.1 = some t ∧
            MvPolynomial.eval (encode ω.1.out.coins
              (guessValues ((fullRecord ω).cut n) ω)) t.polynomial = 0 := by
  exact GuessBuild.guess_build ch S m A hS Q QH hA (bad_real ch S m A)

end Components

section Helpers

variable {ch : AdmissibleChoice P0} {S : Relation P0}

lemma firstFire_eq {i : Kind} (F : FactorSlot ch S i) (R : FullRecord (ppOf ch S)) (n : ℕ)
    (hn : (F.fires (R.cut n)).isSome) (hlt : ∀ n' < n, F.fires (R.cut n') = none) :
    F.firstFire R = some n := by
  unfold FactorSlot.firstFire
  have h : ∃ n, (F.fires (R.cut n)).isSome := ⟨n, hn⟩
  rw [dif_pos h]
  congr 1
  apply le_antisymm (Nat.find_min' h hn)
  by_contra hc
  push Not at hc
  have hs := Nat.find_spec h
  rw [hlt _ hc] at hs
  simp at hs

lemma contextOf_eq {i : Kind} (F : FactorSlot ch S i) (R : FullRecord (ppOf ch S)) (n : ℕ)
    (f : SearchSample P0 → F.Context) (hf : F.fires (R.cut n) = some f)
    (hlt : ∀ n' < n, F.fires (R.cut n') = none) (s : SearchSample P0) :
    F.contextOf R s = f s := by
  have h1 := firstFire_eq F R n (by rw [hf]; rfl) hlt
  unfold FactorSlot.contextOf
  rw [h1]
  simp only [hf]

lemma valuesOf_eq {i : Kind} (F : FactorSlot ch S i) (ω : World (ppOf ch S)) (n : ℕ)
    (h : F.firstFire (fullRecord ω) = some n) :
    F.valuesOf ω = guessValues ((fullRecord ω).cut n) ω := by
  unfold FactorSlot.valuesOf
  rw [h]

lemma hitsOn_of {i : Kind} (F : FactorSlot ch S i)
    (event : World (ppOf ch S) → Prop) (obs : ProbComp (World (ppOf ch S)))
    (h : ∀ ω ∈ support obs, event ω → ∃ n f, F.fires ((fullRecord ω).cut n) = some f ∧
      (∀ n' < n, F.fires ((fullRecord ω).cut n') = none) ∧
      ∀ hv : ValidCoins (ppOf ch S).qap ω.1.out.coins,
        ∀ y ∈ support (F.draw (f ω.1.out.coins.2.1) ⟨ω.1.out.coins, hv⟩
          (guessValues ((fullRecord ω).cut n) ω)),
          (F.test (f ω.1.out.coins.2.1)).Hit y) :
    F.HitsOn event obs := by
  intro ω hω he hv
  obtain ⟨n, f, hf, hlt, hh⟩ := h ω hω he
  have hc := contextOf_eq F (fullRecord ω) n f hf hlt ω.1.out.coins.2.1
  have hvals := valuesOf_eq F ω n (firstFire_eq F _ n (by rw [hf]; rfl) hlt)
  rw [hc, hvals]
  exact hh hv

lemma valueT_sub_apply (pp : PublicParams P0) (v : Fin P0.n → Vec k P0.N) (D : ExprT P0)
    (ι : k) (a : {ω : Assign P0 // ValidCoins pp.qap ω.coins}) :
    (Exposure.valueT pp v D - ι • Exposure.valueKey pp) a =
      valT pp v a.val D - ι * kappa pp a.val.coins := rfl

lemma value_of_diff {pp : PublicParams P0} {e e' : Collision pp} (h : e'.diff = e.diff) :
    e'.value = e.value := by
  unfold Collision.value
  rw [h]

lemma value_ne_zero {pp : PublicParams P0} {e : Collision pp} (hg : GuessFree e)
    (hne : e.new ≠ e.old) : e.value ≠ 0 := by
  intro h0
  apply hne
  have hd : e.diff = 0 := by rw [hg, h0, map_zero]
  exact sub_eq_zero.mp hd

end Helpers

section Assembly

set_option maxRecDepth 200000

variable (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0)

lemma value_real_zero {pp : PublicParams P0} (σ : LabelEncoding P0) (c : CoinDomain pp)
    (e : Collision pp) (hg : GuessFree e) (h : evaluate pp σ c e.new = evaluate pp σ c e.old) :
    e.value ⟨Assign.ofCoins c.val, c.property⟩ = 0 := by
  have h2 : evaluate pp σ c e.diff = 0 := by
    unfold Collision.diff
    rw [map_sub, h, sub_self]
  rw [hg] at h2
  simpa [evaluate, atCoin] using h2

lemma cover_kinds (hS : InShape P0 S) (obs : ProbComp (World (ppOf ch S)))
    (hcb : ∀ ω ∈ support obs, ChargedCmp (ppOf ch S) ω.1 → ∃ e, BadAt ω e)
    (hbn : ∀ ω ∈ support obs, ∀ e, BadAt ω e → e.new ≠ e.old)
    (hcs : ∀ ω ∈ support obs, ∀ e, BadAt ω e → GuessFree e → e.sort ≠ .gₜ →
      ¬ IdentityAt e.value (realR ω.1))
    (hcm : ∀ ω ∈ support obs, ChargedCmp (ppOf ch S) ω.1 → ∀ e, BadAt ω e → GuessFree e →
      e.sort = .gₜ → ∃ (D : ExprT P0) (ι : k),
        e.value = Exposure.valueT (ppOf ch S) (formVec ω.1.out.forms) D -
          ι • Exposure.valueKey (ppOf ch S) ∧ ¬ GoodCmp (ppOf ch S) ω.1 D ι)
    (ω : World (ppOf ch S)) (hω : ω ∈ support obs) (hc : ChargedCmp (ppOf ch S) ω.1) :
    BadLight ω ∨ BadField ω ∨ BadGuess ω := by
  obtain ⟨e, he⟩ := hcb ω hω hc
  by_cases hg : GuessFree e
  swap
  · exact Or.inr (Or.inr ⟨e, he, hg⟩)
  by_cases hid : IdentityAt e.value (realR ω.1)
  swap
  · exact Or.inr (Or.inl ⟨e, he, hg, hid⟩)
  left
  by_cases hs : e.sort = .gₜ
  swap
  · exact absurd hid (hcs ω hω e he hg hs)
  obtain ⟨D, ι, hv, hng⟩ := hcm ω hω hc e he hg hs
  refine ⟨e, he, hg, hid, hs, D, ι, hv, ?_⟩
  have hI : IdentityAtR (ppOf ch S) (formVec ω.1.out.forms) (realR ω.1) D ι := by
    intro c hc'
    have h1 := hid c hc'
    rw [hv, valueT_sub_apply, sub_eq_zero] at h1
    exact h1
  by_cases hz : markStack D = 0
  · exfalso
    have hf := zero_formal ch S hS ω.1.out.forms D (realR ω.1) ι hI hz
    have h0 : e.value = 0 := by
      rw [hv]
      funext a
      rw [valueT_sub_apply, hf a.val a.property, sub_self]
      rfl
    exact value_ne_zero hg (hbn ω hω e he) h0
  · by_contra hl
    exact hng ⟨hI, hz, hl⟩

variable {ch S} in
def lightFires {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (r : Record (ppOf ch S)) : Option (Bounds ch S .light) :=
  (cmp j r).bind fun e => if e.sort = .gₜ then lightTestOf r.forms e.value else none

variable {ch S} in
def lightEvents {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (ω : World (ppOf ch S)) : Prop :=
  ChargedCmp (ppOf ch S) ω.1 ∧ ∃ e, BadAt ω e ∧ GuessFree e ∧ IdentityAt e.value (realR ω.1) ∧
    e.sort = .gₜ ∧ LightCmp (ppOf ch S) ω.1.out.forms e.value ∧ Catches cmp j ω e

lemma light_fires {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (pad : Bounds ch S .light) (ω : World (ppOf ch S)) (e : Collision (ppOf ch S))
    (hs : e.sort = .gₜ) (hl : LightCmp (ppOf ch S) ω.1.out.forms e.value)
    (hcat : Catches cmp j ω e) :
    ∃ n, Clean n ω ∧ (∀ n' < n, (lightSlot pad (lightFires cmp j)).fires
        ((fullRecord ω).cut n') = none) ∧
      ∃ (D : ExprT P0) (ι : k) (hl' : Light (markStack D)),
        e.value = Exposure.valueT (ppOf ch S) (formVec ω.1.out.forms) D -
          ι • Exposure.valueKey (ppOf ch S) ∧
        (lightSlot pad (lightFires cmp j)).fires ((fullRecord ω).cut n) =
          some (fun _ => .light ω.1.out.forms D ι hl') := by
  obtain ⟨n, hn, hlt, e', he', hs', hd', _⟩ := hcat
  refine ⟨n, hn, ?_, ?_⟩
  · intro n' hn'
    simp [lightSlot, lightFires, hlt n' hn']
  · have hv := value_of_diff hd'
    have hs'' : e'.sort = .gₜ := hs'.trans hs
    have h' : LightCmp (ppOf ch S) ((fullRecord ω).cut n).forms e'.value := by
      rw [hv]
      exact hl
    refine ⟨h'.choose, h'.choose_spec.choose, h'.choose_spec.choose_spec.2, ?_, ?_⟩
    · rw [← hv]
      exact h'.choose_spec.choose_spec.1
    · simp only [lightSlot, lightFires, he', Option.bind_some, hs'', if_true]
      unfold lightTestOf
      rw [dif_pos h']
      rfl

lemma light_firesOn {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (pad : Bounds ch S .light) (obs : ProbComp (World (ppOf ch S))) :
    (lightSlot pad (lightFires cmp j)).FiresOn (lightEvents cmp j) obs := by
  intro ω _ hev
  obtain ⟨-, e, -, -, -, hs, hl, hcat⟩ := hev
  obtain ⟨n, hn, hlt, D, ι, hl', -, hf⟩ := light_fires ch S cmp j pad ω e hs hl hcat
  exact ⟨n, firstFire_eq _ _ n (by rw [hf]; rfl) hlt, hn⟩

lemma light_hitsOn {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (pad : Bounds ch S .light) (obs : ProbComp (World (ppOf ch S))) :
    (lightSlot pad (lightFires cmp j)).HitsOn (lightEvents cmp j) obs := by
  apply hitsOn_of
  intro ω _ hev
  obtain ⟨-, e, -, -, hid, hs, hl, hcat⟩ := hev
  obtain ⟨n, hn, hlt, D, ι, hl', hD, hf⟩ := light_fires ch S cmp j pad ω e hs hl hcat
  refine ⟨n, _, hf, hlt, ?_⟩
  intro hc y hy
  change y ∈ support (pure ω.1.out.coins.2.1 : ProbComp (SearchSample P0)) at hy
  rw [support_pure] at hy
  have hy' : y = ω.1.out.coins.2.1 := hy
  subst hy'
  change IdentityAtR (ppOf ch S) (formVec ω.1.out.forms) (rField ω.1.out.coins.2.1) D ι
  intro c hc'
  have h1 := hid c hc'
  rw [hD, valueT_sub_apply, sub_eq_zero] at h1
  exact h1

variable {ch S} in
def fieldFires {J : Type} (pad : Bounds ch S .field)
    (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S))) (j : J)
    (r : Record (ppOf ch S)) : Option (SearchSample P0 → Bounds ch S .field) :=
  (cmp j r).map fun e s => (fieldTestOf r.forms e (rField s)).getD pad

variable {ch S} in
def fieldEvents {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (ω : World (ppOf ch S)) : Prop :=
  ChargedCmp (ppOf ch S) ω.1 ∧ ∃ e, BadAt ω e ∧ GuessFree e ∧
    ¬ IdentityAt e.value (realR ω.1) ∧ Catches cmp j ω e

lemma field_firesOn {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (pad : Bounds ch S .field) (obs : ProbComp (World (ppOf ch S))) :
    (fieldSlot pad (fieldFires pad cmp j)).FiresOn (fieldEvents cmp j) obs := by
  intro ω _ hev
  obtain ⟨-, e, -, -, -, n, hn, hlt, e', he', -⟩ := hev
  refine ⟨n, firstFire_eq _ _ n ?_ ?_, hn⟩
  · simp [fieldSlot, fieldFires, he']
  · intro n' hn'
    simp [fieldSlot, fieldFires, hlt n' hn']

lemma field_hitsOn {J : Type}
    (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (pad : Bounds ch S .field) (obs : ProbComp (World (ppOf ch S)))
    (hbr : ∀ ω ∈ support obs, ∀ e, BadAt ω e → ∀ hc : ValidCoins (ppOf ch S).qap ω.1.out.coins,
      evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.new =
        evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.old)
    (hbn : ∀ ω ∈ support obs, ∀ e, BadAt ω e → e.new ≠ e.old)
    (hbt : ∀ ω ∈ support obs, ∀ e, BadAt ω e →
      (e.sort = .g₁ → ∃ E : Expr1 P0, e.value = Exposure.value1 (ppOf ch S) E) ∧
      (e.sort = .g₂ → ∃ E : Expr2 P0,
        e.value = Exposure.value2 (ppOf ch S) (formVec ω.1.out.forms) E) ∧
      (e.sort = .gₜ → ∃ (D : ExprT P0) (ι : k),
        e.value = Exposure.valueT (ppOf ch S) (formVec ω.1.out.forms) D -
          ι • Exposure.valueKey (ppOf ch S))) :
    (fieldSlot pad (fieldFires pad cmp j)).HitsOn (fieldEvents cmp j) obs := by
  apply hitsOn_of
  intro ω hω hev
  obtain ⟨-, e, he, hg, hid, n, hn, hlt, e', he', hs', hd', -⟩ := hev
  refine ⟨n, fun s => (fieldTestOf ((fullRecord ω).cut n).forms e' (rField s)).getD pad,
    ?_, ?_, ?_⟩
  · simp only [fieldSlot, fieldFires, he', Option.map_some]
  · intro n' hn'
    simp [fieldSlot, fieldFires, hlt n' hn']
  intro hc
  have hv := value_of_diff hd'
  have hreal := value_real_zero ω.1.enc ⟨ω.1.out.coins, hc⟩ e hg (hbr ω hω e he hc)
  have hne := value_ne_zero hg (hbn ω hω e he)
  obtain ⟨h1, h2, h3⟩ := hbt ω hω e he
  change ∀ y ∈ support ((fieldSlot pad (fieldFires pad cmp j)).draw
      ((fieldTestOf ω.1.out.forms e' (realR ω.1)).getD pad) ⟨ω.1.out.coins, hc⟩ _),
    ((fieldTestOf ω.1.out.forms e' (realR ω.1)).getD pad).Hit y
  cases hsort : e.sort with
  | g₁ =>
    obtain ⟨E, hE⟩ := h1 hsort
    have hp : ∃ E' : Expr1 P0, e'.value = Exposure.value1 (ppOf ch S) E' ∧
        ¬ FormalEq1 (ppOf ch S) E' 0 := by
      refine ⟨E, hv.trans hE, fun hf => hne ?_⟩
      rw [hE, (Exposure.value1_eq_iff (ppOf ch S) E 0).mpr hf, map_zero]
    obtain ⟨⟨E', hE'⟩, hpick⟩ := Option.isSome_iff_exists.mp (pick_isSome hp)
    have hT : fieldTestOf ω.1.out.forms e' (realR ω.1) =
        some (.source1 E' 0 (realR ω.1) hE'.2) := by
      simp only [fieldTestOf, hs'.trans hsort, hpick, Option.map_some]
    rw [hT, Option.getD_some]
    show ∀ y ∈ support (resample (ppOf ch S) ⟨ω.1.out.coins, hc⟩),
      val1 (ppOf ch S) ⟨y.val, realR ω.1⟩ E' = val1 (ppOf ch S) ⟨y.val, realR ω.1⟩ 0
    intro y hy
    unfold resample at hy
    rw [support_map] at hy
    obtain ⟨s', _, rfl⟩ := hy
    have hi := (val_search_indep ch S ω.1.out.coins (ω.1.out.coins.1, s', ω.1.out.coins.2.2)
      (realR ω.1) rfl rfl).1
    have h0 : val1 (ppOf ch S) ⟨ω.1.out.coins, realR ω.1⟩ (0 : Expr1 P0) = 0 := by
      simp [val1]
    have := congrFun hE'.1 ⟨Assign.ofCoins ω.1.out.coins, hc⟩
    rw [hv, hreal] at this
    exact (hi E').trans (this.symm.trans ((hi 0).trans h0).symm)
  | g₂ =>
    obtain ⟨E, hE⟩ := h2 hsort
    have hp : ∃ E' : Expr2 P0, e'.value = Exposure.value2 (ppOf ch S) (formVec ω.1.out.forms) E' ∧
        ¬ FormalEq2 (ppOf ch S) (formVec ω.1.out.forms) E' 0 := by
      refine ⟨E, hv.trans hE, fun hf => hne ?_⟩
      rw [hE, (Exposure.value2_eq_iff (ppOf ch S) _ E 0).mpr hf, map_zero]
    obtain ⟨⟨E', hE'⟩, hpick⟩ := Option.isSome_iff_exists.mp (pick_isSome hp)
    have hT : fieldTestOf ω.1.out.forms e' (realR ω.1) =
        some (.source2 ω.1.out.forms E' 0 (realR ω.1) hE'.2) := by
      simp only [fieldTestOf, hs'.trans hsort, hpick, Option.map_some]
    rw [hT, Option.getD_some]
    show ∀ y ∈ support (resample (ppOf ch S) ⟨ω.1.out.coins, hc⟩),
      val2 (ppOf ch S) (formVec ω.1.out.forms) ⟨y.val, realR ω.1⟩ E' =
        val2 (ppOf ch S) (formVec ω.1.out.forms) ⟨y.val, realR ω.1⟩ 0
    intro y hy
    unfold resample at hy
    rw [support_map] at hy
    obtain ⟨s', _, rfl⟩ := hy
    have hi := (val_search_indep ch S ω.1.out.coins (ω.1.out.coins.1, s', ω.1.out.coins.2.2)
      (realR ω.1) rfl rfl).2.1 (formVec ω.1.out.forms)
    have h0 : val2 (ppOf ch S) (formVec ω.1.out.forms) ⟨ω.1.out.coins, realR ω.1⟩
        (0 : Expr2 P0) = 0 := by
      simp [val2]
    have := congrFun hE'.1 ⟨Assign.ofCoins ω.1.out.coins, hc⟩
    rw [hv, hreal] at this
    exact (hi E').trans (this.symm.trans ((hi 0).trans h0).symm)
  | gₜ =>
    obtain ⟨D, ι, hD⟩ := h3 hsort
    have hp : ∃ Dι : ExprT P0 × k,
        e'.value = Exposure.valueT (ppOf ch S) (formVec ω.1.out.forms) Dι.1 -
          Dι.2 • Exposure.valueKey (ppOf ch S) ∧
        ¬ IdentityAtR (ppOf ch S) (formVec ω.1.out.forms) (realR ω.1) Dι.1 Dι.2 := by
      refine ⟨(D, ι), hv.trans hD, fun hI => hid ?_⟩
      intro c hc'
      rw [hD, valueT_sub_apply, sub_eq_zero]
      exact hI c hc'
    obtain ⟨⟨Dι, hDι⟩, hpick⟩ := Option.isSome_iff_exists.mp (pick_isSome hp)
    have hT : fieldTestOf ω.1.out.forms e' (realR ω.1) =
        some (.field ω.1.out.forms Dι.1 Dι.2 (realR ω.1) hDι.2) := by
      simp only [fieldTestOf, hs'.trans hsort, hpick, Option.map_some]
    rw [hT, Option.getD_some]
    show ∀ y ∈ support (resample (ppOf ch S) ⟨ω.1.out.coins, hc⟩),
      valT (ppOf ch S) (formVec ω.1.out.forms) ⟨y.val, realR ω.1⟩ Dι.1 =
        Dι.2 * kappa (ppOf ch S) y.val
    intro y hy
    unfold resample at hy
    rw [support_map] at hy
    obtain ⟨s', _, rfl⟩ := hy
    have hi := val_search_indep ch S ω.1.out.coins (ω.1.out.coins.1, s', ω.1.out.coins.2.2)
      (realR ω.1) rfl rfl
    have := congrFun hDι.1 ⟨Assign.ofCoins ω.1.out.coins, hc⟩
    rw [hv, hreal, valueT_sub_apply] at this
    exact ((hi.2.2.1 (formVec ω.1.out.forms) Dι.1).trans (sub_eq_zero.mp this.symm)).trans
      (congrArg (Dι.2 * ·) hi.2.2.2.symm)

variable {ch S} in
def guessFires {J : Type} (pad : Bounds ch S .guess)
    (build : Record (ppOf ch S) → Collision (ppOf ch S) → SearchSample P0 → Option GuessTest)
    (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S))) (j : J)
    (r : Record (ppOf ch S)) : Option (SearchSample P0 → Bounds ch S .guess) :=
  (cmp j r).bind fun e =>
    @dite _ (∀ s, (build r e s).isSome) (Classical.propDecidable _)
      (fun h => some fun s => .guess ((build r e s).get (h s))) (fun _ => none)

variable {ch S} in
def guessEvents {J : Type} (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S)))
    (j : J) (ω : World (ppOf ch S)) : Prop :=
  ChargedCmp (ppOf ch S) ω.1 ∧ ∃ e, BadAt ω e ∧ ¬ GuessFree e ∧ Catches cmp j ω e

lemma guess_fires {J : Type}
    (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S))) (j : J)
    (pad : SearchSample P0 × Bounds ch S .guess) (padT : Bounds ch S .guess)
    (build : Record (ppOf ch S) → Collision (ppOf ch S) → SearchSample P0 → Option GuessTest)
    (obs : ProbComp (World (ppOf ch S)))
    (hbuild : ∀ ω ∈ support obs, ∀ e, BadAt ω e → ¬ GuessFree e →
        ∀ n e', Clean n ω → e'.sort = e.sort → e'.diff = e.diff →
          e'.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset →
          (∀ s, (build ((fullRecord ω).cut n) e' s).isSome) ∧
          ∃ t, build ((fullRecord ω).cut n) e' ω.1.out.coins.2.1 = some t ∧
            MvPolynomial.eval (encode ω.1.out.coins
              (guessValues ((fullRecord ω).cut n) ω)) t.polynomial = 0)
    (ω : World (ppOf ch S)) (hω : ω ∈ support obs)
    (hev : guessEvents cmp j ω) :
    ∃ n t, Clean n ω ∧ (∀ n' < n, (guessSlot pad (guessFires padT build cmp j)).fires
        ((fullRecord ω).cut n') = none) ∧
      ∃ f, (guessSlot pad (guessFires padT build cmp j)).fires ((fullRecord ω).cut n) = some f ∧
        f ω.1.out.coins.2.1 = (ω.1.out.coins.2.1, .guess t) ∧
        MvPolynomial.eval (encode ω.1.out.coins
          (guessValues ((fullRecord ω).cut n) ω)) t.polynomial = 0 := by
  obtain ⟨-, e, he, hg, n, hn, hlt, e', he', hs', hd', hvars⟩ := hev
  obtain ⟨hall, t, ht, hz⟩ := hbuild ω hω e he hg n e' hn hs' hd' hvars
  refine ⟨n, t, hn, ?_,
    fun s => (s, .guess ((build ((fullRecord ω).cut n) e' s).get (hall s))), ?_, ?_, hz⟩
  · intro n' hn'
    simp [guessSlot, guessFires, hlt n' hn']
  · simp only [guessSlot, guessFires, he', Option.bind_some]
    rw [dif_pos hall]
    rfl
  · show (ω.1.out.coins.2.1, Bounds.guess
      ((build ((fullRecord ω).cut n) e' ω.1.out.coins.2.1).get (hall _))) = _
    rw [Option.get_of_mem _ ht]

lemma guess_firesOn {J : Type}
    (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S))) (j : J)
    (pad : SearchSample P0 × Bounds ch S .guess) (padT : Bounds ch S .guess)
    (build : Record (ppOf ch S) → Collision (ppOf ch S) → SearchSample P0 → Option GuessTest)
    (obs : ProbComp (World (ppOf ch S)))
    (hbuild : ∀ ω ∈ support obs, ∀ e, BadAt ω e → ¬ GuessFree e →
        ∀ n e', Clean n ω → e'.sort = e.sort → e'.diff = e.diff →
          e'.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset →
          (∀ s, (build ((fullRecord ω).cut n) e' s).isSome) ∧
          ∃ t, build ((fullRecord ω).cut n) e' ω.1.out.coins.2.1 = some t ∧
            MvPolynomial.eval (encode ω.1.out.coins
              (guessValues ((fullRecord ω).cut n) ω)) t.polynomial = 0) :
    (guessSlot pad (guessFires padT build cmp j)).FiresOn (guessEvents cmp j)
      obs := by
  intro ω hω hev
  obtain ⟨n, t, hn, hlt, f, hf, -, -⟩ := guess_fires ch S cmp j pad padT build obs
    hbuild ω hω hev
  exact ⟨n, firstFire_eq _ _ n (by rw [hf]; rfl) hlt, hn⟩

lemma guess_hitsOn {J : Type}
    (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S))) (j : J)
    (pad : SearchSample P0 × Bounds ch S .guess) (padT : Bounds ch S .guess)
    (build : Record (ppOf ch S) → Collision (ppOf ch S) → SearchSample P0 → Option GuessTest)
    (obs : ProbComp (World (ppOf ch S)))
    (hbuild : ∀ ω ∈ support obs, ∀ e, BadAt ω e → ¬ GuessFree e →
        ∀ n e', Clean n ω → e'.sort = e.sort → e'.diff = e.diff →
          e'.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset →
          (∀ s, (build ((fullRecord ω).cut n) e' s).isSome) ∧
          ∃ t, build ((fullRecord ω).cut n) e' ω.1.out.coins.2.1 = some t ∧
            MvPolynomial.eval (encode ω.1.out.coins
              (guessValues ((fullRecord ω).cut n) ω)) t.polynomial = 0) :
    (guessSlot pad (guessFires padT build cmp j)).HitsOn (guessEvents cmp j)
      obs := by
  apply hitsOn_of
  intro ω hω hev
  obtain ⟨n, t, hn, hlt, f, hf, hfs, hz⟩ := guess_fires ch S cmp j pad padT
    build obs hbuild ω hω hev
  refine ⟨n, f, hf, hlt, ?_⟩
  intro hc
  rw [hfs]
  intro y hy
  change y ∈ support (pure (encode ω.1.out.coins (guessValues ((fullRecord ω).cut n) ω)) :
    ProbComp (ℕ → k)) at hy
  rw [support_pure] at hy
  have hy' : y = encode ω.1.out.coins (guessValues ((fullRecord ω).cut n) ω) := hy
  subst hy'
  exact hz

lemma guess_marginal {J : Type}
    (cmp : J → Record (ppOf ch S) → Option (Collision (ppOf ch S))) (j : J)
    (pad : SearchSample P0 × Bounds ch S .guess) (padT : Bounds ch S .guess)
    (build : Record (ppOf ch S) → Collision (ppOf ch S) → SearchSample P0 → Option GuessTest)
    (hstd : ∀ r e s t, build r e s = some t → StdGuess (ppOf ch S) r s t) :
    (guessSlot pad (guessFires padT build cmp j)).Marginal := by
  apply guessSlot_marginal
  intro r f hf s
  simp only [guessFires] at hf
  cases hc : cmp j r with
  | none => rw [hc] at hf; simp at hf
  | some e =>
    rw [hc, Option.bind_some] at hf
    by_cases hall : ∀ s, (build r e s).isSome
    · rw [dif_pos hall] at hf
      cases hf
      exact ⟨(build r e s).get (hall s), rfl, hstd r e s _ (Option.some_get _).symm⟩
    · rw [dif_neg hall] at hf
      cases hf

theorem fold_data (hS : InShape P0 S) (Q QH : ℕ) (hA : InClass A Q QH)
    (htest : ∀ i, Nonempty (Bounds ch S i))
    (hK1 : ∀ s : SearchSample P0, (∑' c : CoinDomain (ppOf ch S),
      if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) = Pr[= s | searchLaw])
    (hK2 : ∀ (s : SearchSample P0) (c' : CoinDomain (ppOf ch S)),
      (∑' c : CoinDomain (ppOf ch S), if c.val.2.1 = s then
        Pr[= c | coinLaw (ppOf ch S)] * Pr[= c' | resample (ppOf ch S) c] else 0) =
      Pr[= s | searchLaw] * Pr[= c' | coinLaw (ppOf ch S)]) :
    ∃ (events : EventsOn (WorldOut P0 × ObsState (ppOf ch S)) (simBudget Q))
      (slot : (i : Kind) → Fin (quota (simBudget Q) i) → FactorSlot ch S i),
      (∀ i j ω, events i j ω → ChargedCmp (ppOf ch S) ω.1) ∧
      (∀ ω ∈ support (observedRun (ppOf ch S) m A), ChargedCmp (ppOf ch S) ω.1 →
        ∃ i j, events i j ω) ∧
      (∀ i j, (slot i j).FiresOn (events i j) (observedRun (ppOf ch S) m A)) ∧
      (∀ i j, (slot i j).HitsOn (events i j) (observedRun (ppOf ch S) m A)) ∧
      (∀ i j, (slot i j).Marginal) := by
  obtain ⟨cmpLF, hLF⟩ := lf_catalog ch S m A hS Q QH hA
  obtain ⟨cmpG, hG⟩ := guess_catalog ch S m A hS Q QH hA
  obtain ⟨build, hstd, hbuild⟩ := guess_build ch S m A hS Q QH hA
  have hcb := cover_bad ch S m A hS
  have hbn := bad_ne ch S m A hS
  have hcs := cover_source ch S m A hS
  have hcm := cover_mark ch S m A hS
  have hbr := bad_real ch S m A
  have hbt := bad_typed ch S m A
  generalize observedRun (ppOf ch S) m A = obs at hLF hG hbuild hcb hbn hcs hcm hbr hbt ⊢
  let padL : Bounds ch S .light := Classical.choice (htest .light)
  let padF : Bounds ch S .field := Classical.choice (htest .field)
  let padG : Bounds ch S .guess := Classical.choice (htest .guess)
  let events : EventsOn (World (ppOf ch S)) (simBudget Q) := fun i => match i with
    | .light => fun j ω => lightEvents cmpLF j ω
    | .field => fun j ω => fieldEvents cmpLF j ω
    | .guess => fun j ω => guessEvents cmpG j ω
    | _ => fun _ _ => False
  let slot : (i : Kind) → Fin (quota (simBudget Q) i) → FactorSlot ch S i := fun i =>
    match i with
    | .light => fun j => lightSlot padL (lightFires cmpLF j)
    | .field => fun j => fieldSlot padF (fieldFires padF cmpLF j)
    | .guess => fun j =>
        guessSlot (Classical.arbitrary (SearchSample P0), padG) (guessFires padG build cmpG j)
    | .reservoir => fun _ =>
        FactorSlot.idle (Bounds ch S .reservoir) id (Classical.choice (htest .reservoir))
    | .kdf => fun _ => FactorSlot.idle (Bounds ch S .kdf) id (Classical.choice (htest .kdf))
    | .seed => fun _ => FactorSlot.idle (Bounds ch S .seed) id (Classical.choice (htest .seed))
  refine ⟨events, slot, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j ω h
    cases i
    · exact h.1
    · exact h.1
    · exact h.1
    · exact h.elim
    · exact h.elim
    · exact h.elim
  · intro ω hω hc
    rcases cover_kinds ch S hS obs hcb hbn hcs hcm ω hω hc with
      ⟨e, he, hg, hid, hs, hl⟩ | ⟨e, he, hg, hid⟩ | ⟨e, he, hg⟩
    · obtain ⟨j, hj⟩ := hLF ω hω e he hg
      exact ⟨.light, j, hc, e, he, hg, hid, hs, hl, hj⟩
    · obtain ⟨j, hj⟩ := hLF ω hω e he hg
      exact ⟨.field, j, hc, e, he, hg, hid, hj⟩
    · obtain ⟨j, hj⟩ := hG ω hω e he hg
      exact ⟨.guess, j, hc, e, he, hg, hj⟩
  · intro i j
    cases i
    · exact light_firesOn ch S cmpLF j padL obs
    · exact field_firesOn ch S cmpLF j padF obs
    · exact guess_firesOn ch S cmpG j _ padG build obs hbuild
    · exact FactorSlot.idle_firesOn _ _ _ obs
    · exact FactorSlot.idle_firesOn _ _ _ obs
    · exact FactorSlot.idle_firesOn _ _ _ obs
  · intro i j
    cases i
    · exact light_hitsOn ch S cmpLF j padL obs
    · exact field_hitsOn ch S cmpLF j padF obs hbr hbn hbt
    · exact guess_hitsOn ch S cmpG j _ padG build obs hbuild
    · exact FactorSlot.idle_hitsOn _ _ _ obs
    · exact FactorSlot.idle_hitsOn _ _ _ obs
    · exact FactorSlot.idle_hitsOn _ _ _ obs
  · intro i j
    cases i
    · exact lightSlot_marginal ch S hK1 padL _
    · exact fieldSlot_marginal ch S hK2 padF _
    · exact guess_marginal ch S cmpG j _ padG build hstd
    · exact FactorSlot.idle_marginal _ _ _
    · exact FactorSlot.idle_marginal _ _ _
    · exact FactorSlot.idle_marginal _ _ _

end Assembly

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold
