import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.QAP.Valid
import Praxis.Proofs.View.SZ.Degree
import Praxis.Proofs.View.SZ.Eval
import Praxis.Proofs.View.SZ.Grid
import Praxis.Proofs.View.SZ.Model
import Praxis.Proofs.View.SZ.PolyDegree
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

lemma encode_coin (c : Coins P0) (x : ℕ → k) (i : View.CoinVar P0) :
    encode c x (coinIdx i) = View.coinVar c i := by
  simp [encode, (coinIdx i).isLt]

lemma encode_guess (c : Coins P0) (x : ℕ → k) (j : ℕ) :
    encode c x (nCoin + j) = x j := by
  simp [encode, Nat.not_lt.mpr (Nat.le_add_right nCoin j)]

lemma guessValues_idxOf {pp : PublicParams P0} (r : Record pp) (ω : World pp)
    (v : GuessVar) (hv : v ∈ r.order) :
    guessValues r ω (r.order.idxOf v) = (Algebra.decodeLabel (ω.1.enc v.1) v.2).getD 0 := by
  simp [guessValues, List.getElem?_idxOf hv]

lemma valueAt_guessValues {pp : PublicParams P0} (r : Record pp) (ω : World pp)
    (hc : ValidCoins pp.qap ω.1.out.coins) (p : Poly pp)
    (hv : p.vars ⊆ r.order.toFinset) :
    valueAt pp r.order ⟨ω.1.out.coins, hc⟩ (guessValues r ω) p =
      evaluate pp ω.1.enc ⟨ω.1.out.coins, hc⟩ p := by
  unfold valueAt evaluate
  simp only [MvPolynomial.coe_eval₂Hom]
  apply MvPolynomial.eval₂_congr
  intro v d hd hvd
  apply guessValues_idxOf
  apply List.mem_toFinset.mp
  apply hv
  rw [MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨d, MvPolynomial.mem_support_iff.mpr hvd, hd⟩

lemma sampleSet_card (pp : PublicParams P0) (i : View.CoinVar P0) :
    P0.q - Constants.D ≤ (View.sampleSet pp.qap i).card := by
  apply View.sampleSet_card_lower
  · rw [View.SZ.qapIndex_card]
    decide
  · decide
  · decide

lemma stdPool_nonempty (pp : PublicParams P0) (r : Record pp) (s : SearchSample P0)
    (j : ℕ) (x : ℕ → k) : (stdPool pp r s j x).Nonempty := by
  unfold stdPool
  split_ifs
  · apply Finset.card_pos.mp
    exact lt_of_lt_of_le (by decide : 0 < P0.q - Constants.D) (sampleSet_card pp _)
  · exact guessPool_nonempty pp r _ _ _
  · exact Finset.univ_nonempty

lemma stdPool_coin_card (pp : PublicParams P0) (r : Record pp) (s : SearchSample P0)
    (j : ℕ) (hj : j < nCoin) (x : ℕ → k) :
    P0.q - Constants.D ≤ (stdPool pp r s j x).card := by
  simpa only [stdPool, dif_pos hj] using sampleSet_card pp (coinIdx.symm ⟨j, hj⟩)

lemma guessPool_card (pp : PublicParams P0) (r : Record pp) (c : CoinDomain pp)
    (t used : ℕ) (x : ℕ → k) (h : (usedBefore pp r c t x).card ≤ used) :
    P0.q - used ≤ (guessPool pp r c t x).card := by
  unfold guessPool
  split_ifs
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card]
    exact Nat.sub_le_sub_left h _
  · simpa only [Finset.card_univ, ZMod.card] using Nat.sub_le P0.q used

lemma stdPool_guess_card (pp : PublicParams P0) (r : Record pp) (s : SearchSample P0)
    (used : ℕ)
    (hused : ∀ j < r.order.length, ∀ (c : CoinDomain pp) (x : ℕ → k),
      (usedBefore pp r c j x).card ≤ used)
    (j : ℕ) (hj : j < r.order.length) (x : ℕ → k) :
    P0.q - used ≤ (stdPool pp r s (nCoin + j) x).card := by
  unfold stdPool
  rw [dif_neg (Nat.not_lt.mpr (Nat.le_add_right nCoin j))]
  split_ifs with hv
  · simpa only [Nat.add_sub_cancel_left] using
      guessPool_card pp r ⟨decodeCoins s x, hv⟩ j used _ (hused j hj _ _)
  · simpa only [Finset.card_univ, ZMod.card] using Nat.sub_le P0.q used

def Clears (pp : PublicParams P0) (s : SearchSample P0)
    (f : Exposure.Coeff pp) (p : View.SZ.Poly) : Prop :=
  ∀ c : CoinDomain pp, MvPolynomial.eval (View.coinVar c.val) p =
    View.SZ.denom c.val * f ⟨⟨c.val, rField s⟩, c.property⟩

def source1P (pp : PublicParams P0) (E : Expr1 P0) : View.SZ.Poly :=
  View.SZ.denomP * ((keys1 P0).map fun a =>
    MvPolynomial.C (E a) * View.SZ.e1P pp a).sum

def source2P (pp : PublicParams P0) (forms : FormMatrix P0) (s : SearchSample P0)
    (E : Expr2 P0) : View.SZ.Poly :=
  ((keys2 P0).map fun b =>
    MvPolynomial.C (E b) * View.SZ.e2P pp (formVec forms) (rField s) b).sum

lemma source1P_clears (pp : PublicParams P0) (s : SearchSample P0) (E : Expr1 P0) :
    Clears pp s (Exposure.value1 pp E) (source1P pp E) := by
  intro c
  simp only [source1P, map_mul, map_list_sum, List.map_map, Function.comp_def,
    MvPolynomial.eval_C, View.SZ.eval_denomP, View.SZ.eval_e1P pp c.val (rField s)]
  rfl

lemma source2P_clears (pp : PublicParams P0) (forms : FormMatrix P0)
    (s : SearchSample P0) (E : Expr2 P0) :
    Clears pp s (Exposure.value2 pp (formVec forms) E) (source2P pp forms s E) := by
  intro c
  simp only [source2P, map_list_sum, List.map_map, Function.comp_def,
    map_mul, MvPolynomial.eval_C, View.SZ.eval_e2P pp c.val _ _ _ c.property]
  change ((keys2 P0).map fun b => E b *
    (View.SZ.denom c.val * e2At pp (formVec forms) ⟨c.val, rField s⟩ b)).sum =
      View.SZ.denom c.val * ((keys2 P0).map fun b =>
        E b * e2At pp (formVec forms) ⟨c.val, rField s⟩ b).sum
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b hb
  ring

lemma targetP_clears (pp : PublicParams P0) (forms : FormMatrix P0)
    (s : SearchSample P0) (D : ExprT P0) (ι : k) :
    Clears pp s (Exposure.valueT pp (formVec forms) D - ι • Exposure.valueKey pp)
      (View.SZ.differenceP pp (formVec forms) (rField s) D ι) := by
  intro c
  exact View.SZ.eval_differenceP pp c.val _ _ D ι c.property

lemma scalarP_clears (pp : PublicParams P0) (s : SearchSample P0) (a : k) :
    Clears pp s (fun _ => a) (View.SZ.denomP * MvPolynomial.C a) := by
  intro c
  simp

lemma source1P_degree (ch : AdmissibleChoice P0) (S : Relation P0) (E : Expr1 P0) :
    (source1P (ppOf ch S) E).totalDegree ≤ Constants.view_degree_total + 5 := by
  have hD := QAP.domainMap_valid ch S
  have hs : (((keys1 P0).map fun a => MvPolynomial.C (E a) *
      View.SZ.e1P (ppOf ch S) a).sum).totalDegree ≤ Constants.view_degree_d1 := by
    apply View.SZ.list_degree_le
    intro a ha
    have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (E a))
      (View.SZ.e1P (ppOf ch S) a)
    have h' := View.SZ.e1P_degree (ppOf ch S) S hD a
    simp only [MvPolynomial.totalDegree_C, zero_add] at h
    exact h.trans h'
  have h := MvPolynomial.totalDegree_mul View.SZ.denomP
    (((keys1 P0).map fun a => MvPolynomial.C (E a) *
      View.SZ.e1P (ppOf ch S) a).sum)
  have hd := View.SZ.denomP_degree
  change (View.SZ.denomP * _).totalDegree ≤ _
  have hnum : Constants.view_degree_d1 ≤ Constants.view_degree_total := by decide
  omega

lemma source2P_degree (ch : AdmissibleChoice P0) (S : Relation P0)
    (forms : FormMatrix P0) (s : SearchSample P0) (E : Expr2 P0) :
    (source2P (ppOf ch S) forms s E).totalDegree ≤ Constants.view_degree_total + 5 := by
  apply (show Constants.view_degree_d2 ≤ Constants.view_degree_total + 5 by decide).trans'
  apply View.SZ.list_degree_le
  intro b hb
  have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (E b))
    (View.SZ.e2P (ppOf ch S) (formVec forms) (rField s) b)
  have h' := View.SZ.e2P_degree (ppOf ch S) S (QAP.domainMap_valid ch S)
    (formVec forms) (rField s) b
  simp only [MvPolynomial.totalDegree_C, zero_add] at h
  exact h.trans h'

lemma targetP_degree (ch : AdmissibleChoice P0) (S : Relation P0)
    (forms : FormMatrix P0) (s : SearchSample P0) (D : ExprT P0) (ι : k) :
    (View.SZ.differenceP (ppOf ch S) (formVec forms) (rField s) D ι).totalDegree ≤
      Constants.view_degree_total + 5 := by
  apply (Nat.le_add_right Constants.view_degree_total 5).trans'
  exact View.SZ.differenceP_degree_of_e2 (ppOf ch S) S (QAP.domainMap_valid ch S)
    (formVec forms) (rField s) D ι
    (View.SZ.e2P_degree (ppOf ch S) S (QAP.domainMap_valid ch S) (formVec forms) (rField s))

def clearedPolynomial {pp : PublicParams P0} (ord : List GuessVar) (p : Poly pp)
    (q : (GuessVar →₀ ℕ) → View.SZ.Poly) : MvPolynomial ℕ k :=
  ∑ m ∈ p.support, MvPolynomial.rename (fun i => (coinIdx i : ℕ)) (q m) *
    ∏ v ∈ m.support, MvPolynomial.X (nCoin + ord.idxOf v) ^ m v

lemma eval_coinLift (c : Coins P0) (x : ℕ → k) (p : View.SZ.Poly) :
    MvPolynomial.eval (encode c x)
      (MvPolynomial.rename (fun i => (coinIdx i : ℕ)) p) =
        MvPolynomial.eval (View.coinVar c) p := by
  simp only [MvPolynomial.eval_rename, Function.comp_def, encode_coin]

lemma eval_clearedPolynomial {pp : PublicParams P0} (ord : List GuessVar) (p : Poly pp)
    (q : (GuessVar →₀ ℕ) → View.SZ.Poly) (c : CoinDomain pp) (x : ℕ → k)
    (hq : ∀ m ∈ p.support, Clears pp c.val.2.1 (p.coeff m) (q m)) :
    MvPolynomial.eval (encode c.val x) (clearedPolynomial ord p q) =
      View.SZ.denom c.val * valueAt pp ord c x p := by
  simp only [clearedPolynomial, map_sum, map_mul, map_prod, map_pow,
    MvPolynomial.eval_X, eval_coinLift, encode_guess]
  unfold valueAt
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hq m hm c]
  change (View.SZ.denom c.val * p.coeff m _) * _ =
    View.SZ.denom c.val * (p.coeff m _ * _)
  rw [mul_assoc]
  rfl

def unpack (c : Coins P0) (ord : List GuessVar) :
    MvPolynomial ℕ k →+* MvPolynomial GuessVar k :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j =>
    if h : j < nCoin then MvPolynomial.C (View.coinVar c (coinIdx.symm ⟨j, h⟩))
    else MvPolynomial.X ((ord[j - nCoin]?).getD (.g₁, 0))

lemma unpack_coinLift (c : Coins P0) (ord : List GuessVar) (p : View.SZ.Poly) :
    unpack c ord (MvPolynomial.rename (fun i => (coinIdx i : ℕ)) p) =
      MvPolynomial.C (MvPolynomial.eval (View.coinVar c) p) := by
  have h : (unpack c ord).comp
      (MvPolynomial.rename (fun i => (coinIdx i : ℕ))).toRingHom =
      MvPolynomial.C.comp (MvPolynomial.eval (View.coinVar c)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [unpack]
    · intro i
      simp [unpack, (coinIdx i).isLt]
  exact DFunLike.congr_fun h p

lemma unpack_guess (c : Coins P0) (ord : List GuessVar) (v : GuessVar) (hv : v ∈ ord) :
    unpack c ord (MvPolynomial.X (nCoin + ord.idxOf v)) = MvPolynomial.X v := by
  simp [unpack, Nat.not_lt.mpr (Nat.le_add_right nCoin (ord.idxOf v)),
    List.getElem?_idxOf hv]

lemma unpack_clearedPolynomial {pp : PublicParams P0} (ord : List GuessVar) (p : Poly pp)
    (q : (GuessVar →₀ ℕ) → View.SZ.Poly) (c : Coins P0) (hv : p.vars ⊆ ord.toFinset) :
    unpack c ord (clearedPolynomial ord p q) =
      ∑ m ∈ p.support, MvPolynomial.monomial m (MvPolynomial.eval (View.coinVar c) (q m)) := by
  simp only [clearedPolynomial, map_sum, map_mul, map_prod, map_pow, unpack_coinLift]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.monomial_eq, Finsupp.prod]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv'
  rw [unpack_guess c ord v]
  apply List.mem_toFinset.mp
  apply hv
  rw [MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨m, hm, hv'⟩

lemma clearedPolynomial_nonzero {pp : PublicParams P0} (ord : List GuessVar) (p : Poly pp)
    (q : (GuessVar →₀ ℕ) → View.SZ.Poly) (hv : p.vars ⊆ ord.toFinset)
    (m : GuessVar →₀ ℕ) (hm : m ∈ p.support) (c : Coins P0)
    (hq : MvPolynomial.eval (View.coinVar c) (q m) ≠ 0) :
    clearedPolynomial ord p q ≠ 0 := by
  intro hp
  have h := unpack_clearedPolynomial ord p q c hv
  rw [hp, map_zero] at h
  have he := congrArg (MvPolynomial.coeff m) h
  simp only [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial] at he
  have hs : (∑ m' ∈ p.support, if m' = m then
      MvPolynomial.eval (View.coinVar c) (q m') else 0) =
        MvPolynomial.eval (View.coinVar c) (q m) := by
    exact Finset.sum_ite_eq' p.support m (fun m' => MvPolynomial.eval (View.coinVar c) (q m'))
      |>.trans (if_pos hm)
  exact hq (hs ▸ he.symm)

lemma partial_sum_le (m : ℕ →₀ ℕ) (s : Finset ℕ) :
    ∑ j ∈ s, m j ≤ m.sum (fun _ e => e) := by
  change _ ≤ ∑ j ∈ m.support, m j
  calc
    ∑ j ∈ s, m j = ∑ j ∈ s ∩ m.support, m j := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro j hjs hj
      apply Finsupp.notMem_support_iff.mp
      intro hm
      exact hj (Finset.mem_inter.mpr ⟨hjs, hm⟩)
    _ ≤ _ := Finset.sum_le_sum_of_subset Finset.inter_subset_right

lemma shifted_sum_le (m : ℕ →₀ ℕ) (nc ng : ℕ) :
    ∑ j ∈ Finset.range ng, m (nc + j) ≤ m.sum (fun _ e => e) := by
  have h : (∑ j ∈ Finset.range ng, m (nc + j)) =
      ∑ j ∈ (Finset.range ng).image (fun j => nc + j), m j := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Nat.add_left_cancel hab
  rw [h]
  exact partial_sum_le _ _

lemma exponent_zero {p : MvPolynomial ℕ k} {m : ℕ →₀ ℕ}
    (hm : m ∈ p.support) (j : ℕ) (hj : j ∉ p.vars) : m j = 0 := by
  by_contra h
  apply hj
  rw [MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨m, hm, Finsupp.mem_support_iff.mpr h⟩

lemma bidegree_coin (p : MvPolynomial ℕ k) (nc ng dc : ℕ)
    (hv : p.vars ⊆ Finset.range nc) (hd : p.totalDegree ≤ dc) :
    BiDegree p nc ng dc 0 := by
  refine ⟨hv.trans (Finset.range_mono (Nat.le_add_right nc ng)), ?_⟩
  intro m hm
  refine ⟨(partial_sum_le m _).trans ((MvPolynomial.le_totalDegree hm).trans hd), ?_⟩
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro j hj
  apply exponent_zero hm
  intro hv'
  have h := Finset.mem_range.mp (hv hv')
  omega

lemma bidegree_guess (p : MvPolynomial ℕ k) (nc ng dg : ℕ)
    (hv : p.vars ⊆ Finset.Ico nc (nc + ng)) (hd : p.totalDegree ≤ dg) :
    BiDegree p nc ng 0 dg := by
  refine ⟨fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp (hv hj)).2, ?_⟩
  intro m hm
  refine ⟨?_, (shifted_sum_le m nc ng).trans ((MvPolynomial.le_totalDegree hm).trans hd)⟩
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro j hj
  apply exponent_zero hm
  intro hv'
  have h := (Finset.mem_Ico.mp (hv hv')).1
  have h' := Finset.mem_range.mp hj
  omega

lemma bidegree_mul (p q : MvPolynomial ℕ k) (nc ng dc₁ dc₂ dg₁ dg₂ : ℕ)
    (hp : BiDegree p nc ng dc₁ dg₁) (hq : BiDegree q nc ng dc₂ dg₂) :
    BiDegree (p * q) nc ng (dc₁ + dc₂) (dg₁ + dg₂) := by
  constructor
  · exact (MvPolynomial.vars_mul p q).trans (Finset.union_subset hp.1 hq.1)
  · intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
    obtain ⟨ha₁, ha₂⟩ := hp.2 a ha
    obtain ⟨hb₁, hb₂⟩ := hq.2 b hb
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    exact ⟨Nat.add_le_add ha₁ hb₁, Nat.add_le_add ha₂ hb₂⟩

lemma bidegree_sum {α : Type} (s : Finset α) (f : α → MvPolynomial ℕ k)
    (nc ng dc dg : ℕ) (h : ∀ a ∈ s, BiDegree (f a) nc ng dc dg) :
    BiDegree (∑ a ∈ s, f a) nc ng dc dg := by
  constructor
  · intro j hj
    obtain ⟨a, ha, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset s f hj)
    exact (h a ha).1 hj
  · intro m hm
    obtain ⟨a, ha, hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    exact (h a ha).2 m hm

lemma clearedPolynomial_degree {pp : PublicParams P0} (ord : List GuessVar) (p : Poly pp)
    (q : (GuessVar →₀ ℕ) → View.SZ.Poly) (hv : p.vars ⊆ ord.toFinset)
    (dc dg : ℕ) (hdeg : p.totalDegree ≤ dg)
    (hq : ∀ m ∈ p.support, (q m).totalDegree ≤ dc) :
    BiDegree (clearedPolynomial ord p q) nCoin ord.length dc dg := by
  apply bidegree_sum
  intro m hm
  have hcoin : BiDegree (MvPolynomial.rename (fun i => (coinIdx i : ℕ)) (q m))
      nCoin ord.length dc 0 := by
    apply bidegree_coin
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := MvPolynomial.mem_vars_rename _ _ hj
      exact Finset.mem_range.mpr (coinIdx i).isLt
    · exact (MvPolynomial.totalDegree_rename_le _ _).trans (hq m hm)
  have hmon : (∏ v ∈ m.support,
      (MvPolynomial.X (nCoin + ord.idxOf v) : MvPolynomial ℕ k) ^ m v) =
      MvPolynomial.rename (fun v => nCoin + ord.idxOf v)
        (MvPolynomial.monomial m (1 : k)) := by
    simp only [MvPolynomial.monomial_eq, map_one, one_mul,
      Finsupp.prod, map_prod, map_pow, MvPolynomial.rename_X]
  rw [hmon]
  have hguess : BiDegree (MvPolynomial.rename (fun v => nCoin + ord.idxOf v)
      (MvPolynomial.monomial m (1 : k))) nCoin ord.length 0 dg := by
    apply bidegree_guess
    · intro j hj
      obtain ⟨v, hv', rfl⟩ := MvPolynomial.mem_vars_rename _ _ hj
      have hv'' : v ∈ p.vars := by
        rw [MvPolynomial.mem_vars_iff_mem_support]
        refine ⟨m, hm, ?_⟩
        simpa only [MvPolynomial.vars_monomial one_ne_zero] using hv'
      have ht := List.idxOf_lt_length_of_mem (List.mem_toFinset.mp (hv hv''))
      exact Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ht _⟩
    · exact (MvPolynomial.totalDegree_rename_le _ _).trans
        ((MvPolynomial.totalDegree_monomial_le m 1).trans
          ((MvPolynomial.le_totalDegree hm).trans hdeg))
  simpa only [Nat.add_zero, Nat.zero_add] using
    bidegree_mul _ _ nCoin ord.length dc 0 0 dg hcoin hguess

def SourceCoefficient (pp : PublicParams P0) (forms : FormMatrix P0)
    (f : Exposure.Coeff pp) : Prop :=
  (∃ a : k, f = fun _ => a) ∨
    (∃ E : Expr1 P0, f = Exposure.value1 pp E) ∨
    (∃ E : Expr2 P0, f = Exposure.value2 pp (formVec forms) E)

def CoinCoefficient (pp : PublicParams P0) (forms : FormMatrix P0)
    (f : Exposure.Coeff pp) : Prop :=
  SourceCoefficient pp forms f ∨ ∃ (D : ExprT P0) (ι : k),
    f = Exposure.valueT pp (formVec forms) D - ι • Exposure.valueKey pp

lemma coefficient_clears (ch : AdmissibleChoice P0) (S : Relation P0)
    (forms : FormMatrix P0) (s : SearchSample P0) (f : Exposure.Coeff (ppOf ch S))
    (hf : CoinCoefficient (ppOf ch S) forms f) :
    ∃ p : View.SZ.Poly, Clears (ppOf ch S) s f p ∧
      p.totalDegree ≤ Constants.view_degree_total + 5 := by
  rcases hf with (⟨a, rfl⟩ | ⟨E, rfl⟩ | ⟨E, rfl⟩) | ⟨D, ι, rfl⟩
  · refine ⟨View.SZ.denomP * MvPolynomial.C a, scalarP_clears _ _ _, ?_⟩
    have h := MvPolynomial.totalDegree_mul View.SZ.denomP (MvPolynomial.C a)
    have hd := View.SZ.denomP_degree
    simp only [MvPolynomial.totalDegree_C, Nat.add_zero] at h
    exact h.trans (hd.trans (Nat.le_add_left 5 Constants.view_degree_total))
  · exact ⟨source1P _ E, source1P_clears _ _ _, source1P_degree ch S E⟩
  · exact ⟨source2P _ forms s E, source2P_clears _ _ _ _, source2P_degree ch S forms s E⟩
  · exact ⟨View.SZ.differenceP _ _ _ D ι, targetP_clears _ _ _ _ _,
      targetP_degree ch S forms s D ι⟩

lemma sourceCoefficient_rigid (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (forms : FormMatrix P0) (s : SearchSample P0)
    (f : Exposure.Coeff (ppOf ch S)) (hf : SourceCoefficient (ppOf ch S) forms f)
    (hn : f ≠ 0) : ∃ c : CoinDomain (ppOf ch S), f ⟨⟨c.val, rField s⟩, c.property⟩ ≠ 0 := by
  rcases hf with ⟨a, rfl⟩ | ⟨E, rfl⟩ | ⟨E, rfl⟩
  · refine ⟨Classical.arbitrary _, ?_⟩
    intro ha
    apply hn
    funext ω
    exact ha
  · have hE : ¬ FormalEq1 (ppOf ch S) E 0 := by
      intro h
      exact hn (by simpa using (Exposure.value1_eq_iff (ppOf ch S) E 0).mpr h)
    have h := source1_rigid ch S E 0 hE (rField s)
    push Not at h
    obtain ⟨c, hc, h⟩ := h
    exact ⟨⟨c, hc⟩, by simpa [Exposure.value1, val1] using h⟩
  · have hE : ¬ FormalEq2 (ppOf ch S) (formVec forms) E 0 := by
      intro h
      exact hn (by simpa using (Exposure.value2_eq_iff (ppOf ch S) (formVec forms) E 0).mpr h)
    have h := source2_rigid ch S hS forms E 0 hE (rField s)
    push Not at h
    obtain ⟨c, hc, h⟩ := h
    exact ⟨⟨c, hc⟩, by simpa [Exposure.value2, val2] using h⟩

lemma nonconstant_coefficient {pp : PublicParams P0} (p : Poly pp)
    (hp : p ≠ MvPolynomial.C (MvPolynomial.constantCoeff p)) :
    ∃ m ∈ p.support, m ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0
  · subst m
    rw [MvPolynomial.coeff_C]
    rfl
  · have hm' : m ∉ p.support := fun h' => hm (h m h')
    simp only [MvPolynomial.notMem_support_iff.mp hm', MvPolynomial.coeff_C,
      if_neg (Ne.symm hm)]

structure Certificate (pp : PublicParams P0) (r : Record pp) (e : Collision pp) : Prop where
  vars : e.diff.vars ⊆ r.order.toFinset
  guess_degree : e.diff.totalDegree ≤ 2
  coefficients : ∀ m ∈ e.diff.support, CoinCoefficient pp r.forms (e.diff.coeff m)
  nonconstant : ∀ m ∈ e.diff.support, m ≠ 0 →
    SourceCoefficient pp r.forms (e.diff.coeff m)
  used : ∀ j < r.order.length, ∀ (c : CoinDomain pp) (x : ℕ → k),
    (usedBefore pp r c j x).card ≤ Constants.L + 3 * Constants.W_budget + 1

def Interprets (pp : PublicParams P0) (r : Record pp) (e : Collision pp)
    (s : SearchSample P0) (t : GuessTest) : Prop :=
  StdGuess pp r s t ∧ ∀ (c : CoinDomain pp) (x : ℕ → k), c.val.2.1 = s →
    MvPolynomial.eval (encode c.val x) t.polynomial =
      View.SZ.denom c.val * valueAt pp r.order c x e.diff

set_option maxRecDepth 200000 in
lemma exists_test (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (r : Record (ppOf ch S)) (e : Collision (ppOf ch S)) (hg : ¬ GuessFree e)
    (h : Certificate (ppOf ch S) r e) (s : SearchSample P0) :
    ∃ t, Interprets (ppOf ch S) r e s t := by
  have hex : ∀ m : {m // m ∈ e.diff.support}, ∃ q : View.SZ.Poly,
      Clears (ppOf ch S) s (e.diff.coeff m.val) q ∧
        q.totalDegree ≤ Constants.view_degree_total + 5 :=
    fun m => coefficient_clears ch S r.forms s _ (h.coefficients m.val m.property)
  let q : (GuessVar →₀ ℕ) → View.SZ.Poly := fun m =>
    if hm : m ∈ e.diff.support then (hex ⟨m, hm⟩).choose else 0
  have hq : ∀ m ∈ e.diff.support, Clears (ppOf ch S) s (e.diff.coeff m) (q m) ∧
      (q m).totalDegree ≤ Constants.view_degree_total + 5 := by
    intro m hm
    simpa only [q, dif_pos hm] using (hex ⟨m, hm⟩).choose_spec
  obtain ⟨m, hm, hm0⟩ := nonconstant_coefficient e.diff hg
  obtain ⟨c, hc⟩ := sourceCoefficient_rigid ch S hS r.forms s _
    (h.nonconstant m hm hm0) (MvPolynomial.mem_support_iff.mp hm)
  have hne : clearedPolynomial r.order e.diff q ≠ 0 := by
    apply clearedPolynomial_nonzero _ _ _ h.vars m hm c.val
    rw [(hq m hm).1 c]
    exact mul_ne_zero (View.SZ.denom_ne_zero _ c.val c.property) hc
  let t : GuessTest := {
    polynomial := clearedPolynomial r.order e.diff q
    nonzero := hne
    nc := nCoin
    ng := r.order.length
    dc := Constants.view_degree_total + 5
    dg := 2
    used := Constants.L + 3 * Constants.W_budget + 1
    degree := clearedPolynomial_degree _ _ _ h.vars _ _ h.guess_degree
      (fun m hm => (hq m hm).2)
    coin_slack := by decide
    guess_degree := le_rfl
    used_le := le_rfl
    pool := stdPool (ppOf ch S) r s
    nonempty := stdPool_nonempty _ _ _
    coin_pool := stdPool_coin_card _ _ _
    guess_pool := stdPool_guess_card _ _ _ _ h.used }
  have ht : StdGuess (ppOf ch S) r s t := by
    dsimp only [StdGuess, t]
    exact ⟨rfl, rfl, rfl⟩
  refine ⟨t, ht, ?_⟩
  intro c x hs
  apply eval_clearedPolynomial
  intro m hm
  rw [hs]
  exact (hq m hm).1

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild
