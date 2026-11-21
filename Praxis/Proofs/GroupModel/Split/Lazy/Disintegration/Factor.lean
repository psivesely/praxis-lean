import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Domination
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Relation
import Praxis.Search

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration

open Classical

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind}

namespace FactorSlot

variable (F : FactorSlot ch S i)

lemma r1_cut_eq_of_le {R R' : FullRecord (ppOf ch S)} {n j : ℕ}
    (h : R.cut n = R'.cut n) (hj : j ≤ n) : R.cut j = R'.cut j := by
  have hh := congrArg Record.header h
  have hf := congrArg Record.forms h
  have hp := congrArg Record.pv h
  have hs := congrArg Record.steps h
  have ht : R.steps.take j = R'.steps.take j := by
    have := congrArg (List.take j) hs
    simpa only [FullRecord.cut, List.take_take, min_eq_left hj] using this
  have hq : (R.steps[j]?).map (fun s => s.entry.1) =
      (R'.steps[j]?).map (fun s => s.entry.1) := by
    rcases lt_or_eq_of_le hj with hj | rfl
    · have := congrArg (fun l : List (Step (ppOf ch S)) =>
        (l[j]?).map fun s => s.entry.1) hs
      simpa only [FullRecord.cut, List.getElem?_take_of_lt hj] using this
    · exact congrArg Record.pending h
  have ho : (R.steps[j]?).map Step.order = (R'.steps[j]?).map Step.order := by
    rcases lt_or_eq_of_le hj with hj | rfl
    · have := congrArg (fun l : List (Step (ppOf ch S)) => (l[j]?).map Step.order) hs
      simpa only [FullRecord.cut, List.getElem?_take_of_lt hj] using this
    · exact congrArg Record.pendingOrder h
  cases R; cases R'; simp_all only [FullRecord.cut, Record.mk.injEq]

lemma r1_firstFire_spec {R : FullRecord (ppOf ch S)} {n : ℕ}
    (h : F.firstFire R = some n) :
    (F.fires (R.cut n)).isSome ∧ ∀ j < n, ¬ (F.fires (R.cut j)).isSome := by
  unfold firstFire at h
  split_ifs at h with he
  · have hn : Nat.find he = n := Option.some.inj h
    subst n
    exact ⟨Nat.find_spec he, fun j hj => Nat.find_min he hj⟩

lemma r1_firstFire_of_cut {R R' : FullRecord (ppOf ch S)} {n : ℕ}
    (h : F.firstFire R = some n) (hc : R.cut n = R'.cut n) :
    F.firstFire R' = some n := by
  obtain ⟨hf, hmin⟩ := F.r1_firstFire_spec h
  have hf' : (F.fires (R'.cut n)).isSome := hc ▸ hf
  unfold firstFire
  rw [dif_pos ⟨n, hf'⟩]
  congr 1
  apply le_antisymm
  · exact Nat.find_min' _ hf'
  · by_contra hn
    have hj : Nat.find (⟨n, hf'⟩ : ∃ j, (F.fires (R'.cut j)).isSome) < n := by omega
    have hcut := r1_cut_eq_of_le hc (Nat.le_of_lt hj)
    exact hmin _ hj (hcut.symm ▸ Nat.find_spec (show ∃ j, (F.fires (R'.cut j)).isSome from ⟨n, hf'⟩))

lemma r1_event_kernel_le {Ω J : Type} (obs : ProbComp Ω) (E : Ω → Prop)
    (K : Ω → ℝ≥0∞) (P : J → Ω → Prop) (w b : J → ℝ≥0∞)
    (hcover : ∀ ω ∈ support obs, E ω → ∃ j, P j ω ∧ K ω ≤ w j)
    (hb : ∀ j, Pr[P j | obs] ≤ b j) :
    (∑' ω, Pr[= ω | obs] * (if E ω then K ω else 0)) ≤ ∑' j, b j * w j := by
  calc
    _ ≤ ∑' ω, Pr[= ω | obs] * ∑' j, if P j ω then w j else 0 := by
      apply ENNReal.tsum_le_tsum
      intro ω
      by_cases hs : ω ∈ support obs
      · apply mul_le_mul_right
        split_ifs with he
        · obtain ⟨j, hp, hk⟩ := hcover ω hs he
          exact hk.trans (by simpa only [if_pos hp] using
            (ENNReal.le_tsum (f := fun j => if P j ω then w j else 0) j))
        · exact zero_le
      · simp [probOutput_eq_zero_of_not_mem_support hs]
    _ = ∑' j, Pr[P j | obs] * w j := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro j
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro ω
      split_ifs <;> simp
    _ ≤ _ := ENNReal.tsum_le_tsum fun j => mul_le_mul_left (hb j) _

lemma r1_sigma_mass {C : Type} {B : C → Type} (a b : C) (y : B a)
    (d : ProbComp (B b)) (h : b ≠ a) :
    Pr[= (⟨a, y⟩ : Sigma B) | Sigma.mk b <$> d] = 0 := by
  rw [probOutput_map_eq_tsum_ite]
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  rw [if_neg]
  intro he
  exact h (congrArg Sigma.fst he).symm

lemma r1_marginal (hK : F.Marginal) (r : Record (ppOf ch S))
    (f : SearchSample P0 → F.Context) (hf : F.fires r = some f)
    (a : F.Context) (y : (F.test a).Sample) :
    (∑' c : CoinDomain (ppOf ch S), Pr[= c | coinLaw (ppOf ch S)] *
      ∑' x, Pr[= x | guessDraw (ppOf ch S) r c] *
        Pr[= (⟨a,y⟩ : (b : F.Context) × (F.test b).Sample) |
          (fun z => ⟨f c.val.2.1, z⟩) <$> F.draw (f c.val.2.1) c x]) ≤
    (∑' s, if f s = a then Pr[= s | searchLaw] else 0) *
      Pr[= y | (F.test a).sample] := by
  refine le_trans (le_of_eq ?_) (hK r f hf a y)
  calc
    _ = ∑' s, ∑' c : CoinDomain (ppOf ch S),
        if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] *
          ∑' x, Pr[= x | guessDraw (ppOf ch S) r c] *
            Pr[= (⟨a,y⟩ : (b : F.Context) × (F.test b).Sample) |
              (fun z => ⟨f c.val.2.1, z⟩) <$> F.draw (f c.val.2.1) c x] else 0 := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro c
      simp
    _ = _ := by
      apply tsum_congr
      intro s
      by_cases hsa : f s = a
      · rw [if_pos hsa]
        apply tsum_congr
        intro c
        by_cases hcs : c.val.2.1 = s
        · rw [if_pos hcs, if_pos hcs]
          have hca : f c.val.2.1 = a := hcs ▸ hsa
          cases hca
          congr 1
          apply tsum_congr
          intro x
          rw [probOutput_map_injective (f := fun z =>
            (⟨f c.val.2.1, z⟩ : (b : F.Context) × (F.test b).Sample)) _
            (fun z z' h => eq_of_heq (Sigma.mk.inj_iff.mp h).2) y]
        · simp [hcs]
      · rw [if_neg hsa]
        apply ENNReal.tsum_eq_zero.mpr
        intro c
        by_cases hcs : c.val.2.1 = s
        · rw [if_pos hcs]
          have hca : f c.val.2.1 ≠ a := hcs ▸ hsa
          simp only [r1_sigma_mass (B := fun b : F.Context => (F.test b).Sample) a (f c.val.2.1) y _ hca, mul_zero, tsum_zero]
        · simp [hcs]

abbrev r1Stops := {nr : ℕ × Record (ppOf ch S) //
  ∃ R, F.firstFire R = some nr.1 ∧ R.cut nr.1 = nr.2}

lemma r1Stops_fire (u : F.r1Stops) (R : FullRecord (ppOf ch S))
    (hc : R.cut u.val.1 = u.val.2) : F.firstFire R = some u.val.1 := by
  obtain ⟨R', hf, hr⟩ := u.property
  exact F.r1_firstFire_of_cut hf (hr.trans hc.symm)

abbrev r1Context (r : Record (ppOf ch S)) (s : SearchSample P0) : F.Context :=
  ((F.fires r).getD (fun _ => F.pad)) s

lemma r1_contextOf {R : FullRecord (ppOf ch S)} {n : ℕ}
    (h : F.firstFire R = some n) (s : SearchSample P0) :
    F.contextOf R s = F.r1Context (R.cut n) s := by
  simp only [contextOf, h, r1Context]
  cases F.fires (R.cut n) <;> rfl

lemma r1_stopping_sum (gen : ProbComp (FullRecord (ppOf ch S)))
    (q : Record (ppOf ch S) → ℝ≥0∞) (K : FullRecord (ppOf ch S) → ℝ≥0∞)
    (hq : ∀ (u : F.r1Stops) R, R.cut u.val.1 = u.val.2 → q u.val.2 ≤ K R) :
    (∑' u : F.r1Stops, Pr[fun R => R.cut u.val.1 = u.val.2 | gen] * q u.val.2) ≤
      ∑' R, Pr[= R | gen] * K R := by
  calc
    _ = ∑' R, Pr[= R | gen] *
        ∑' u : F.r1Stops, if R.cut u.val.1 = u.val.2 then q u.val.2 else 0 := by
      simp_rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro R
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro u
      split_ifs <;> simp
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro R
      apply mul_le_mul_right
      cases hf : F.firstFire R with
      | none =>
        have hno (u : F.r1Stops) : R.cut u.val.1 ≠ u.val.2 := by
          intro hc
          have := F.r1Stops_fire u R hc
          rw [hf] at this
          contradiction
        simp only [if_neg (hno _), tsum_zero]
        exact zero_le
      | some n =>
        let u0 : F.r1Stops := ⟨(n, R.cut n), R, hf, rfl⟩
        rw [tsum_eq_single u0]
        · rw [if_pos rfl]
          exact hq u0 R rfl
        · intro u hu
          by_cases hc : R.cut u.val.1 = u.val.2
          · have hn : u.val.1 = n := Option.some.inj ((F.r1Stops_fire u R hc).symm.trans hf)
            have he : u = u0 := by
              apply Subtype.ext
              apply Prod.ext hn
              exact hc.symm.trans (congrArg R.cut hn)
            exact (hu he).elim
          · exact if_neg hc

lemma r1_sigma_bind {C : Type} {B : C → Type} (d : ProbComp C)
    (T : (b : C) → ProbComp (B b)) (a : C) (y : B a) :
    Pr[= (⟨a,y⟩ : Sigma B) | do
      let b ← d
      let z ← T b
      pure ⟨b,z⟩] = Pr[= a | d] * Pr[= y | T a] := by
  have hm (b : C) :
      (do let z ← T b; pure (⟨b,z⟩ : Sigma B)) = Sigma.mk b <$> T b := by
    exact (map_eq_bind_pure_comp ProbComp (Sigma.mk b) (T b)).symm
  simp_rw [hm]
  rw [probOutput_bind_eq_tsum, tsum_eq_single a]
  · rw [probOutput_map_injective _ (fun z z' h => eq_of_heq (Sigma.mk.inj_iff.mp h).2) y]
  · intro b hb
    rw [r1_sigma_mass a b y _ hb, mul_zero]

lemma r1_trials_mass (gen : ProbComp (FullRecord (ppOf ch S)))
    (a : F.Context) (y : (F.test a).Sample) :
    Pr[= (⟨a, y⟩ : (F.preparation gen).Trial) | (F.preparation gen).trials] =
      ∑' R, Pr[= R | gen] *
        ((∑' s, if F.contextOf R s = a then Pr[= s | searchLaw] else 0) *
          Pr[= y | (F.test a).sample]) := by
  have ht : Pr[= (⟨a,y⟩ : (F.preparation gen).Trial) | (F.preparation gen).trials] =
      Pr[= a | (F.preparation gen).prepare] * Pr[= y | (F.test a).sample] := by
    exact r1_sigma_bind (F.preparation gen).prepare (fun b => (F.test b).sample) a y
  rw [ht]
  simp only [preparation, probOutput_bind_eq_tsum, probOutput_pure, mul_ite,
    mul_one, mul_zero]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro R
  rw [mul_assoc]
  congr 1
  congr 1
  apply tsum_congr
  intro s
  simp only [eq_comm]

lemma r1_dominated (gen : ProbComp (FullRecord (ppOf ch S)))
    (obs : ProbComp (WorldOut P0 × ObsState (ppOf ch S)))
    (hvalid : ∀ ω ∈ support obs, ValidCoins (ppOf ch S).qap ω.1.out.coins)
    (hsimulation : ∀ (n : ℕ) (r : Record (ppOf ch S)) (c : CoinDomain (ppOf ch S)) (x : ℕ → k),
      Pr[fun ω => Clean n ω ∧ (fullRecord ω).cut n = r ∧ ω.1.out.coins = c.val ∧
          guessValues r ω = x | obs] ≤
        Pr[fun R => R.cut n = r | gen] * Pr[= c | coinLaw (ppOf ch S)] *
          Pr[= x | guessDraw (ppOf ch S) r c])
    (event : WorldOut P0 × ObsState (ppOf ch S) → Prop) (hfire : F.FiresOn event obs)
    (hK : F.Marginal) :
    (F.toDistribution gen).Dominated obs event := by
  unfold FiresOn at hfire
  change ∀ t : (a : F.Context) × (F.test a).Sample,
    (∑' ω, Pr[= ω | obs] * (if event ω then Pr[= t | F.extract gen ω] else 0)) ≤
      Pr[= t | (F.preparation gen).trials]
  intro ⟨a,y⟩
  let J := F.r1Stops × CoinDomain (ppOf ch S) × (ℕ → k)
  let ker (r : Record (ppOf ch S)) (c : CoinDomain (ppOf ch S)) (x : ℕ → k) : ℝ≥0∞ :=
    Pr[= (⟨a,y⟩ : (a : F.Context) × (F.test a).Sample) |
      (fun z => ⟨F.r1Context r c.val.2.1, z⟩) <$>
        F.draw (F.r1Context r c.val.2.1) c x]
  let q (r : Record (ppOf ch S)) : ℝ≥0∞ :=
    (∑' s, if F.r1Context r s = a then Pr[= s | searchLaw] else 0) *
      Pr[= y | (F.test a).sample]
  let K (R : FullRecord (ppOf ch S)) : ℝ≥0∞ :=
    (∑' s, if F.contextOf R s = a then Pr[= s | searchLaw] else 0) *
      Pr[= y | (F.test a).sample]
  let P (j : J) (ω : WorldOut P0 × ObsState (ppOf ch S)) : Prop :=
    Clean j.1.val.1 ω ∧ (fullRecord ω).cut j.1.val.1 = j.1.val.2 ∧
      ω.1.out.coins = j.2.1.val ∧ guessValues j.1.val.2 ω = j.2.2
  let b (j : J) : ℝ≥0∞ :=
    Pr[fun R => R.cut j.1.val.1 = j.1.val.2 | gen] *
      Pr[= j.2.1 | coinLaw (ppOf ch S)] * Pr[= j.2.2 | guessDraw (ppOf ch S) j.1.val.2 j.2.1]
  change (∑' ω, Pr[= ω | obs] *
    (if event ω then Pr[= ⟨a,y⟩ | F.extract gen ω] else 0)) ≤ _
  calc
    _ ≤ ∑' j : J, b j * ker j.1.val.2 j.2.1 j.2.2 := by
      apply r1_event_kernel_le
        (obs) event
        (fun ω => Pr[= ⟨a,y⟩ | F.extract gen ω]) P
        (fun j => ker j.1.val.2 j.2.1 j.2.2) b
      · intro ω hω he
        obtain ⟨n, hn, hclean⟩ := (hfire ω hω he :
          ∃ n, F.firstFire (fullRecord ω) = some n ∧ Clean n ω)
        have hv := hvalid ω hω
        let r := (fullRecord ω).cut n
        let c : CoinDomain (ppOf ch S) := ⟨ω.1.out.coins, hv⟩
        let u : F.r1Stops := ⟨(n,r), fullRecord ω, hn, rfl⟩
        refine ⟨(u,c,guessValues r ω), ⟨hclean,rfl,rfl,rfl⟩, le_of_eq ?_⟩
        dsimp only [ker]
        unfold extract
        rw [dif_pos hv]
        simp only [valuesOf, hn]
        rw [F.r1_contextOf hn]
        rfl
      · intro j
        exact hsimulation j.1.val.1 j.1.val.2 j.2.1 j.2.2
    _ = ∑' u : F.r1Stops, Pr[fun R => R.cut u.val.1 = u.val.2 | gen] *
        ∑' c : CoinDomain (ppOf ch S), Pr[= c | coinLaw (ppOf ch S)] *
          ∑' x, Pr[= x | guessDraw (ppOf ch S) u.val.2 c] * ker u.val.2 c x := by
      simp only [J, b, ENNReal.tsum_prod', mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' u : F.r1Stops, Pr[fun R => R.cut u.val.1 = u.val.2 | gen] * q u.val.2 := by
      apply ENNReal.tsum_le_tsum
      intro u
      apply mul_le_mul_right
      obtain ⟨R, hf, hr⟩ := u.property
      have hs := (F.r1_firstFire_spec hf).1
      rw [hr] at hs
      obtain ⟨f, he⟩ := Option.isSome_iff_exists.mp hs
      have hctx : F.r1Context u.val.2 = f := by
        change (F.fires u.val.2).getD (fun _ => F.pad) = f
        rw [he]
        rfl
      have hm := F.r1_marginal hK u.val.2 f he a y
      rw [← hctx] at hm
      exact hm
    _ ≤ ∑' R, Pr[= R | gen] * K R := by
      apply F.r1_stopping_sum gen q K
      intro u R hc
      have hf := F.r1Stops_fire u R hc
      have hctx (s : SearchSample P0) : F.contextOf R s = F.r1Context u.val.2 s := by
        rw [F.r1_contextOf hf, hc]
      exact le_of_eq (by simp only [q, K, hctx])
    _ = _ := (F.r1_trials_mass gen a y).symm

end FactorSlot

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration
