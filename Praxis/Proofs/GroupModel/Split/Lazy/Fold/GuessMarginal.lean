import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Domination
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.View.SZ.Grid
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Search

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option maxHeartbeats 1600000

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessMarginal

open Classical

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

attribute [local instance] Classical.propDecidable

local instance : DecidableEq (ℕ → k) := Classical.decEq _

attribute [local irreducible] nCoin coinIdx

abbrev Grid (sets : ℕ → Finset k) (n : ℕ) :=
  (i : Fin n) → {a : k // a ∈ sets i.val}

def gridSample (sets : ℕ → Finset k) (hne : ∀ i, (sets i).Nonempty) (n : ℕ) :
    ProbComp (Grid sets n) :=
  letI : ∀ i : Fin n, Nonempty {a : k // a ∈ sets i.val} := fun i => (hne i).to_subtype
  letI := SampleableType.ofFintype (Grid sets n)
  $ᵗ _

def extend (sets : ℕ → Finset k) (n : ℕ) (x : Grid sets n) : ℕ → k :=
  fun j => if h : j < n then (x ⟨j, h⟩).val else 0

lemma extend_snoc (sets : ℕ → Finset k) (n : ℕ)
    (x : Grid sets n) (a : {a : k // a ∈ sets n}) :
    extend sets (n + 1) (Fin.snoc x a) = Function.update (extend sets n x) n a.val := by
  funext j
  by_cases hj : j = n
  · subst j
    simp only [extend, Nat.lt_succ_self, ↓reduceDIte, Function.update_self]
    exact congrArg Subtype.val (Fin.snoc_last (α := fun i : Fin (n+1) => {a : k // a ∈ sets i.val}) a x)
  · by_cases hjn : j < n
    · simp only [extend, hjn, show j < n + 1 by omega, ↓reduceDIte,
        Function.update_of_ne hj]
      exact congrArg Subtype.val (Fin.snoc_castSucc (α := fun i : Fin (n+1) => {a : k // a ∈ sets i.val}) a x ⟨j,hjn⟩)
    · simp [extend, hjn, show ¬ j < n + 1 by omega, Function.update_of_ne hj]

lemma gridSample_snoc (sets : ℕ → Finset k) (hne : ∀ i, (sets i).Nonempty) (n : ℕ) :
    𝒮[do let x ← gridSample sets hne n
          let a ← (letI : Nonempty {a : k // a ∈ sets n} := (hne n).to_subtype
                   letI := SampleableType.ofFintype {a : k // a ∈ sets n}
                   $ᵗ {a : k // a ∈ sets n})
          pure (Fin.snoc x a)] = 𝒮[gridSample sets hne (n+1)] := by
  letI : ∀ i : ℕ, Nonempty {a : k // a ∈ sets i} := fun i => (hne i).to_subtype
  letI := SampleableType.ofFintype (Grid sets n)
  letI := SampleableType.ofFintype {a : k // a ∈ sets n}
  letI := SampleableType.ofFintype (Grid sets (n+1))
  let e : Grid sets n × {a : k // a ∈ sets n} ≃ Grid sets (n+1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun i : Fin (n+1) => {a : k // a ∈ sets i.val}))
  have h := evalSPMF_map_bijective_uniform_cross (α := Grid sets n × {a : k // a ∈ sets n}) e e.bijective
  change 𝒮[e <$> (Prod.mk <$> ($ᵗ (Grid sets n)) <*> ($ᵗ {a : k // a ∈ sets n}))] =
    𝒮[gridSample sets hne (n+1)] at h
  change 𝒮[do let x ← $ᵗ (Grid sets n)
               let a ← $ᵗ {a : k // a ∈ sets n}
               pure (e (x,a))] = _
  simpa only [map_eq_bind_pure_comp, seq_eq_bind_map, bind_assoc, pure_bind,
    Function.comp_apply] using h

lemma reservoir_fixed (pool : ℕ → (ℕ → k) → Finset k)
    (hne : ∀ j x, (pool j x).Nonempty) (sets : ℕ → Finset k)
    (hs : ∀ j, (sets j).Nonempty) (n : ℕ)
    (hpool : ∀ j < n, ∀ x, pool j x = sets j) :
    𝒮[reservoirDraw pool hne n] = 𝒮[extend sets n <$> gridSample sets hs n] := by
  induction n with
  | zero =>
      apply evalSPMF_ext
      intro y
      have he : extend sets 0 = fun _ => (fun _ : ℕ => (0 : k)) := by
        funext x j
        simp [extend]
      simp [reservoirDraw, he, probOutput_map_const]
  | succ n ih =>
      have hi := ih (fun j hj => hpool j (by omega))
      calc
        _ = 𝒮[do let x ← gridSample sets hs n
                  let a ← draw (sets n) (hs n)
                  pure (Function.update (extend sets n x) n a)] := by
          rw [reservoirDraw, evalSPMF_bind, hi, ← evalSPMF_bind]
          rw [bind_map_left]
          apply evalSPMF_bind_congr'
          intro x
          simp only [hpool n (by omega)]
        _ = 𝒮[extend sets (n+1) <$> (do
                  let x ← gridSample sets hs n
                  let a ← (letI : Nonempty {a : k // a ∈ sets n} := (hs n).to_subtype
                           letI := SampleableType.ofFintype {a : k // a ∈ sets n}
                           $ᵗ {a : k // a ∈ sets n})
                  pure (Fin.snoc x a))] := by
          simp only [draw, map_bind, map_pure, bind_map_left]
          congr 1
          congr 1
          funext x
          congr 1
          funext a
          rw [extend_snoc]
        _ = _ := evalSPMF_map_eq_of_evalSPMF_eq (gridSample_snoc sets hs n) _

lemma encode_tail (c : Coins P0) (x : ℕ → k) (j : ℕ) :
    encode c x (nCoin + j) = x j := by
  simp [encode]

lemma decode_encode (s : SearchSample P0) (c : Coins P0) (x : ℕ → k)
    (hc : c.2.1 = s) : decodeCoins s (encode c x) = c := by
  rcases c with ⟨c₁, c₂, c₃⟩
  dsimp at hc
  subst s
  simp only [decodeCoins, encode, Fin.is_lt, ↓reduceDIte, Equiv.symm_apply_apply,
    Fin.eta, View.coinVar, Sum.elim_inl, Sum.elim_inr]

lemma stdPool_encode (pp : PublicParams P0) (r : Record pp) (s : SearchSample P0)
    (c : CoinDomain pp) (hc : c.val.2.1 = s) (x : ℕ → k) (j : ℕ) :
    stdPool pp r s (nCoin+j) (encode c.val x) = guessPool pp r c j x := by
  have ht : (fun t => encode c.val x (nCoin+t)) = x := funext (encode_tail c.val x)
  simp only [stdPool, show ¬ nCoin+j < nCoin by omega, ↓reduceDIte,
    decode_encode s c.val x hc, c.property, Nat.add_sub_cancel_left, ht]

lemma encode_update (c : Coins P0) (x : ℕ → k) (j : ℕ) (a : k) :
    encode c (Function.update x j a) = Function.update (encode c x) (nCoin+j) a := by
  funext i
  by_cases hi : i < nCoin
  · simp [encode, hi, Function.update_of_ne (show i ≠ nCoin+j by omega)]
  · by_cases hij : i = nCoin+j
    · subst i
      simp [encode]
    · simp [encode, hi, Function.update_of_ne hij,
        Function.update_of_ne (show i-nCoin ≠ j by omega)]

def coinSets (pp : PublicParams P0) (j : ℕ) : Finset k :=
  if h : j < nCoin then View.sampleSet pp.qap (coinIdx.symm ⟨j,h⟩) else Finset.univ

lemma coinSets_at (pp : PublicParams P0) (i : Fin nCoin) :
    coinSets pp i.val = View.sampleSet pp.qap (coinIdx.symm i) := by
  unfold coinSets
  rw [dif_pos i.isLt]

lemma coinSets_idx (pp : PublicParams P0) (v : View.CoinVar P0) :
    coinSets pp (coinIdx v).val = View.sampleSet pp.qap v :=
  (coinSets_at pp (coinIdx v)).trans
    (congrArg (View.sampleSet pp.qap) (coinIdx.symm_apply_apply v))

lemma valid_iff_coordinates {P : Params} [Fact (Nat.Prime P.q)]
    (Dm : QAPData P) (c : Coins P) :
    ValidCoins Dm c ↔ ∀ v, View.coinVar c v ∈ View.sampleSet Dm v := by
  rw [← View.coinVar_valid Dm c, Fintype.mem_piFinset]

lemma coinSets_nonempty (pp : PublicParams P0) [Nonempty (CoinDomain pp)] (j : ℕ) :
    (coinSets pp j).Nonempty := by
  obtain ⟨⟨c,hc⟩⟩ := (inferInstance : Nonempty (CoinDomain pp))
  unfold coinSets
  split_ifs with h
  · exact ⟨View.coinVar c (coinIdx.symm ⟨j,h⟩),
      (valid_iff_coordinates pp.qap c).mp hc _⟩
  · exact Finset.univ_nonempty

def coinEquiv (pp : PublicParams P0) :
    CoinDomain pp ≃ SearchSample P0 × Grid (coinSets pp) nCoin where
  toFun c := (c.val.2.1, fun i => ⟨View.coinVar c.val (coinIdx.symm i), by
    rw [coinSets_at]
    exact (valid_iff_coordinates pp.qap c.val).mp c.property (coinIdx.symm i)⟩)
  invFun z := ⟨(fun i => (z.2 (coinIdx (.inl i))).val, z.1,
      fun sc => (z.2 (coinIdx (.inr sc))).val),
    (valid_iff_coordinates pp.qap _).mpr (fun v => by
      have hv : View.coinVar (fun i => (z.2 (coinIdx (.inl i))).val, z.1,
          fun sc => (z.2 (coinIdx (.inr sc))).val) v = (z.2 (coinIdx v)).val := by
        cases v <;> rfl
      rw [hv]
      have hp : (z.2 (coinIdx v)).val ∈ coinSets pp (coinIdx v).val :=
        (z.2 (coinIdx v)).property
      exact Eq.mp (congrArg (fun pool : Finset k => (z.2 (coinIdx v)).val ∈ pool)
        (coinSets_idx pp v)) hp)⟩
  left_inv c := by
    apply Subtype.ext
    rcases c with ⟨⟨c₁,s,c₃⟩,hc⟩
    simp only [Equiv.symm_apply_apply, View.coinVar, Sum.elim_inl, Sum.elim_inr]
  right_inv z := by
    rcases z with ⟨s,g⟩
    apply Prod.ext
    · rfl
    · funext i
      apply Subtype.ext
      change View.coinVar (fun i => (g (coinIdx (.inl i))).val, s,
        fun sc => (g (coinIdx (.inr sc))).val) (coinIdx.symm i) = _
      have hv (v : View.CoinVar P0) : View.coinVar (fun i => (g (coinIdx (.inl i))).val, s,
          fun sc => (g (coinIdx (.inr sc))).val) v = (g (coinIdx v)).val := by
        cases v <;> rfl
      rw [hv, Equiv.apply_symm_apply]

def gridCoins (pp : PublicParams P0) (s : SearchSample P0) (x : Grid (coinSets pp) nCoin) :
    CoinDomain pp := (coinEquiv pp).symm (s,x)

lemma gridCoins_search (pp : PublicParams P0) (s : SearchSample P0)
    (x : Grid (coinSets pp) nCoin) : (gridCoins pp s x).val.2.1 = s := rfl

lemma gridCoins_encode (pp : PublicParams P0) (s : SearchSample P0)
    (x : Grid (coinSets pp) nCoin) :
    encode (gridCoins pp s x).val (fun _ => 0) = extend (coinSets pp) nCoin x := by
  funext j
  unfold encode extend
  split_ifs with h
  · change View.coinVar _ (coinIdx.symm ⟨j,h⟩) = _
    have hv (v : View.CoinVar P0) :
        View.coinVar (gridCoins pp s x).val v = (x (coinIdx v)).val := by
      cases v <;> rfl
    rw [hv, Equiv.apply_symm_apply]
  · rfl

lemma stdPool_nonempty (pp : PublicParams P0) [Nonempty (CoinDomain pp)]
    (r : Record pp) (s : SearchSample P0) (j : ℕ) (x : ℕ → k) :
    (stdPool pp r s j x).Nonempty := by
  unfold stdPool
  split_ifs with hj hv
  · simpa [coinSets, hj] using coinSets_nonempty pp j
  · exact guessPool_nonempty pp r _ _ _
  · exact Finset.univ_nonempty

lemma std_reservoir_law (pp : PublicParams P0) [Nonempty (CoinDomain pp)]
    (r : Record pp) (s : SearchSample P0) (n : ℕ) :
    𝒮[reservoirDraw (stdPool pp r s) (stdPool_nonempty pp r s) (nCoin+n)] =
      𝒮[do let g ← gridSample (coinSets pp) (coinSets_nonempty pp) nCoin
            let x ← reservoirDraw (guessPool pp r (gridCoins pp s g))
              (guessPool_nonempty pp r (gridCoins pp s g)) n
            pure (encode (gridCoins pp s g).val x)] := by
  induction n with
  | zero =>
      have hz (g : Grid (coinSets pp) nCoin) :
          reservoirDraw (guessPool pp r (gridCoins pp s g))
            (guessPool_nonempty pp r (gridCoins pp s g)) 0 = pure (fun _ => 0) := rfl
      simp only [Nat.add_zero, hz, map_pure, bind_pure_comp]
      have hf := reservoir_fixed (stdPool pp r s) (stdPool_nonempty pp r s)
          (coinSets pp) (coinSets_nonempty pp) nCoin (by
            intro j hj x
            simp [stdPool, coinSets, hj])
      have he : extend (coinSets pp) nCoin =
          (fun g => encode (gridCoins pp s g).val (fun _ => 0)) := by
        funext g
        exact (gridCoins_encode pp s g).symm
      exact hf.trans (congrArg (fun z => 𝒮[z <$>
        gridSample (coinSets pp) (coinSets_nonempty pp) nCoin]) he)

  | succ n ih =>
      rw [show nCoin + (n+1) = (nCoin+n)+1 by omega, reservoirDraw]
      calc
        _ = 𝒮[do let g ← gridSample (coinSets pp) (coinSets_nonempty pp) nCoin
                  let x ← reservoirDraw (guessPool pp r (gridCoins pp s g))
                    (guessPool_nonempty pp r (gridCoins pp s g)) n
                  let a ← draw (stdPool pp r s (nCoin+n) (encode (gridCoins pp s g).val x))
                    (stdPool_nonempty pp r s (nCoin+n) (encode (gridCoins pp s g).val x))
                  pure (Function.update (encode (gridCoins pp s g).val x) (nCoin+n) a)] := by
          rw [evalSPMF_bind, ih, ← evalSPMF_bind]
          simp only [bind_assoc, pure_bind]
        _ = _ := by
          simp only [reservoirDraw, bind_assoc]
          apply evalSPMF_bind_congr'
          intro g
          apply evalSPMF_bind_congr'
          intro x
          simp only [stdPool_encode pp r s _ (gridCoins_search pp s g)]
          apply evalSPMF_bind_congr'
          intro a
          simp only [pure_bind, encode_update]

lemma coin_mass (pp : PublicParams P0) [Nonempty (CoinDomain pp)] (c : CoinDomain pp) :
    Pr[= c | coinLaw pp] =
      (Fintype.card (SearchSample P0) : ℝ≥0∞)⁻¹ *
        (Fintype.card (Grid (coinSets pp) nCoin) : ℝ≥0∞)⁻¹ := by
  simp only [coinLaw, probOutput_uniformSample]
  rw [Fintype.card_congr (coinEquiv pp), Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

lemma search_marginal (pp : PublicParams P0) [Nonempty (CoinDomain pp)]
    (r : Record pp) (s : SearchSample P0) (y : ℕ → k) :
    (∑' c : CoinDomain pp, (if c.val.2.1 = s then Pr[= c | coinLaw pp] else 0) *
      Pr[= y | encode c.val <$> guessDraw pp r c]) =
      Pr[= s | searchLaw] *
        Pr[= y | reservoirDraw (stdPool pp r s) (stdPool_nonempty pp r s)
          (nCoin+r.order.length)] := by
  classical
  have hgrid (g : (Grid (coinSets pp) nCoin)) :
      Pr[= g | gridSample (coinSets pp) (coinSets_nonempty pp) nCoin] =
        (Fintype.card (Grid (coinSets pp) nCoin) : ℝ≥0∞)⁻¹ := by
    simp only [gridSample, probOutput_uniformSample]
  have hlaw := std_reservoir_law pp r s r.order.length
  have hs : Pr[= s | searchLaw] = (Fintype.card (SearchSample P0) : ℝ≥0∞)⁻¹ := by
    simp only [searchLaw, probOutput_uniformSample]
  calc
    _ = ∑' g : (Grid (coinSets pp) nCoin), Pr[= s | searchLaw] *
        Pr[= g | gridSample (coinSets pp) (coinSets_nonempty pp) nCoin] *
        Pr[= y | encode (gridCoins pp s g).val <$> guessDraw pp r (gridCoins pp s g)] := by
      rw [← (coinEquiv pp).symm.tsum_eq (fun c : CoinDomain pp =>
        (if c.val.2.1 = s then Pr[= c | coinLaw pp] else 0) *
          Pr[= y | encode c.val <$> guessDraw pp r c])]
      change (∑' z : SearchSample P0 × (Grid (coinSets pp) nCoin),
        (if z.1 = s then Pr[= gridCoins pp z.1 z.2 | coinLaw pp] else 0) *
          Pr[= y | encode (gridCoins pp z.1 z.2).val <$>
            guessDraw pp r (gridCoins pp z.1 z.2)]) = _
      rw [ENNReal.tsum_prod']
      rw [tsum_eq_single s]
      · simp only [coin_mass, hs, hgrid, ite_true]
      · intro s' hne
        simp only [if_neg hne, zero_mul, tsum_zero]
    _ = Pr[= s | searchLaw] *
        Pr[= y | (do let g ← gridSample (coinSets pp) (coinSets_nonempty pp) nCoin
                     encode (gridCoins pp s g).val <$> guessDraw pp r (gridCoins pp s g))] := by
      simp only [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left, mul_assoc]
    _ = _ := by
      have hp := evalSPMF_ext_iff.mp hlaw.symm y
      simp only [bind_pure_comp] at hp
      exact congrArg (fun z : ℝ≥0∞ => Pr[= s | searchLaw] * z) hp

lemma marginal {ch : AdmissibleChoice P0} {S : Relation P0}
    (pad : SearchSample P0 × Bounds ch S .guess)
    (fires : Record (ppOf ch S) → Option (SearchSample P0 → Bounds ch S .guess))
    (hstd : ∀ r f, fires r = some f → ∀ s, ∃ t, f s = .guess t ∧ StdGuess (ppOf ch S) r s t) :
    (guessSlot pad fires).Marginal := by
  classical
  intro r f hf a y
  cases hh : fires r with
  | none => simp only [guessSlot, hh, Option.map_none, reduceCtorEq] at hf
  | some g =>
      have hfg : (fun s => (s,g s)) = f := by
        have hhf : some (fun s => (s,g s)) = some f := by
          simpa only [guessSlot, hh, Option.map_some] using hf
        exact Option.some.inj hhf
      subst f
      rcases a with ⟨s,t⟩
      cases t with
      | guess t =>
          dsimp only [guessSlot, Bounds.Sample] at y
          dsimp only [guessSlot, Bounds.sample]
          by_cases hs : g s = .guess t
          · have heq (s' : SearchSample P0) :
                (s', g s') = (s, Bounds.guess t) ↔ s' = s := by
              constructor
              · exact fun h => congrArg Prod.fst h
              · intro h; subst s'; exact congrArg (Prod.mk s) hs
            simp only [heq, tsum_ite_eq]
            obtain ⟨t', ht', hshape⟩ := hstd r g hh s
            have htt : t' = t := by simpa only [hs, Bounds.guess.injEq] using ht'.symm
            subst t'
            rcases hshape with ⟨hnc,hng,hpool⟩
            have hm := search_marginal (ppOf ch S) r s y
            simp only [probOutput_map_eq_tsum] at hm
            exact hm.le.trans (by
              simp only [hnc,hng,hpool]
              exact le_rfl)
          · have heq (s' : SearchSample P0) : (s',g s') ≠ (s,Bounds.guess t) := by
              intro h
              have h1 : s' = s := congrArg Prod.fst h
              have h2 : g s' = .guess t := congrArg Prod.snd h
              subst s'
              exact hs h2
            simp only [heq, ↓reduceIte, tsum_zero, zero_mul, le_refl]

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessMarginal
