import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Proofs.GroupModel.Split.Lazy.Exposure
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Keys
import Praxis.Ledger
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Shared
import Praxis.Proofs.View.Locus
import Praxis.Params
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search
import Praxis.Algebra.Definitions.Relation

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 4096

namespace Praxis.Proofs.GroupModel.Split.Lazy

open Classical

def quota (w : ℕ) : Kind → ℕ
  | .light | .field => w * Constants.L + w * (w + 1) / 2
  | .guess => (Constants.L + 3*w).choose 2 + (Constants.L + 3*w)
  | .reservoir => 2 * Constants.L + 4*w + 2*Constants.T
  | .kdf => 4*w
  | .seed => 1

def rate : Kind → ℚ
  | .light => Constants.theta
  | .field | .guess => Constants.eps_f
  | .reservoir => 1 / Constants.N_free
  | .kdf => 1 / 2^126
  | .seed => Constants.statistical_seed

lemma quota_rate (w : ℕ) (i : Kind) :
    (quota w i : ℚ) * rate i = allowance w i := by
  have hcastJ : ((w * Constants.L + w * (w+1) / 2 : ℕ) : ℚ) = ledgerJ w := by
    rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_div (Nat.two_dvd_mul_add_one w) (by norm_num : (2 : ℚ) ≠ 0)]
    simp [ledgerJ]
  have hchoose (n : ℕ) : (n.choose 2 : ℚ) = Praxis.choose2 n := by
    simpa [Praxis.choose2] using Nat.cast_choose_two ℚ n
  cases i <;> simp only [quota, rate, allowance]
  · rw [hcastJ]
  · rw [hcastJ]
  · rw [Nat.cast_add, hchoose]
    ring
  · push_cast
    ring
  · push_cast
    ring
  · simp

def draw {α : Type} (pool : Finset α) (hne : pool.Nonempty) : ProbComp α :=
  letI : Nonempty {x // x ∈ pool} := hne.to_subtype
  letI := SampleableType.ofFintype {x // x ∈ pool}
  Subtype.val <$> ($ᵗ {x // x ∈ pool})

lemma draw_hit {α : Type} (pool : Finset α) (hne : pool.Nonempty) (target : α) :
    (Pr[fun x => x = target | draw pool hne]).toReal ≤ 1 / (pool.card : ℝ) := by
  classical
  let : Nonempty {x // x ∈ pool} := hne.to_subtype
  let := SampleableType.ofFintype {x // x ∈ pool}
  let : DecidablePred (fun x : {x // x ∈ pool} => x.val = target) :=
    fun _ => Classical.propDecidable _
  rw [draw, probEvent_map]
  change (Pr[fun x : {x // x ∈ pool} => x.val = target |
    ($ᵗ {x // x ∈ pool})]).toReal ≤ _
  rw [@probEvent_uniformSample {x // x ∈ pool} inferInstance inferInstance
    (fun x => x.val = target) (fun _ => Classical.propDecidable _)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_coe]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : (Finset.univ.filter fun x : {x // x ∈ pool} => x.val = target).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact Subtype.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  exact_mod_cast hc

def reservoirDraw (pool : ℕ → (ℕ → k) → Finset k)
    (hne : ∀ j x, (pool j x).Nonempty) : ℕ → ProbComp (ℕ → k)
  | 0 => pure (fun _ => 0)
  | n+1 => do
      let x ← reservoirDraw pool hne n
      let a ← draw (pool n x) (hne n x)
      pure (Function.update x n a)

def BiDegree (p : MvPolynomial ℕ k) (nc ng dc dg : ℕ) : Prop :=
  p.vars ⊆ Finset.range (nc + ng) ∧
  ∀ m ∈ p.support,
    (∑ j ∈ Finset.range nc, m j) ≤ dc ∧
    (∑ j ∈ Finset.range ng, m (nc + j)) ≤ dg

lemma draw_root (p : Polynomial k) (hp : p ≠ 0)
    (pool : Finset k) (hne : pool.Nonempty) :
    (Pr[fun x => p.eval x = 0 | draw pool hne]).toReal ≤
      p.natDegree / (pool.card : ℝ) := by
  simpa only [draw, probEvent_map, Function.comp_def] using guess_fiber p hp pool hne

lemma fiber_step {α : Type} (c : ProbComp α) (p : α → Polynomial k)
    (pool : α → Finset k) (hne : ∀ a, (pool a).Nonempty)
    (d m : ℕ) (hm : 0 < m)
    (hd : ∀ a ∈ support c, (p a).natDegree ≤ d)
    (hs : ∀ a ∈ support c, m ≤ (pool a).card) :
    (Pr[fun b => b = true | c >>= fun a =>
      (fun x => decide ((p a).eval x = 0)) <$> draw (pool a) (hne a)]).toReal ≤
        (Pr[fun a => p a = 0 | c]).toReal + (d : ℝ) / m := by
  have htail (a : α) (ha : a ∈ support c) (hp : p a ≠ 0) :
      (Pr[fun b => b = true |
        (fun x => decide ((p a).eval x = 0)) <$> draw (pool a) (hne a)]).toReal ≤
          (d : ℝ) / m := by
    rw [probEvent_map]
    simp only [Function.comp_def, decide_eq_true_eq]
    calc
      _ ≤ (p a).natDegree / ((pool a).card : ℝ) := draw_root (p a) hp (pool a) (hne a)
      _ ≤ (d : ℝ) / ((pool a).card : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hd a ha) (by positivity)
      _ ≤ (d : ℝ) / m := div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast hm) (by exact_mod_cast hs a ha)
  have h : Pr[fun b => b = true | c >>= fun a =>
      (fun x => decide ((p a).eval x = 0)) <$> draw (pool a) (hne a)] ≤
      Pr[fun a => p a = 0 | c] + ENNReal.ofReal ((d : ℝ) / m) := by
    apply probEvent_bind_le_probEvent_add
    intro a ha hp
    rw [← ENNReal.ofReal_toReal probEvent_ne_top]
    exact ENNReal.ofReal_le_ofReal (htail a ha hp)
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, ENNReal.ofReal_ne_top⟩) h
  simpa only [ENNReal.toReal_add probEvent_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (d : ℝ) / m)] using hr

private def reversePrefix (n : ℕ) (x : ℕ → k) : Fin n → k :=
  fun i => x (n - 1 - i.val)

private lemma reversePrefix_update (n : ℕ) (x : ℕ → k) (a : k) :
    reversePrefix (n+1) (Function.update x n a) = Fin.cons a (reversePrefix n x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [reversePrefix]
  · have he : n + 1 - 1 - j.succ.val = n - 1 - j.val := by
      have := j.isLt
      simp only [Fin.val_succ]
      omega
    have hn : n - 1 - j.val ≠ n := by have := j.isLt; omega
    change Function.update x n a (n + 1 - 1 - j.succ.val) = x (n - 1 - j.val)
    rw [he, Function.update_of_ne hn]

private lemma reservoir_weighted (pool : ℕ → (ℕ → k) → Finset k)
    (hne : ∀ j x, (pool j x).Nonempty) (sizes : ℕ → ℕ)
    (hpos : ∀ j, 0 < sizes j)
    (hsize : ∀ j x, sizes j ≤ (pool j x).card) :
    ∀ n (p : MvPolynomial (Fin n) k) (_hp : p ≠ 0) (B : ℝ),
      (∀ m ∈ p.support, (∑ i : Fin n, (m i : ℝ) / sizes (n - 1 - i.val)) ≤ B) →
      (Pr[fun x => MvPolynomial.eval (reversePrefix n x) p = 0 |
        reservoirDraw pool hne n]).toReal ≤ B := by
  intro n
  induction n with
  | zero =>
      intro p hp B hB
      obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hp
      have hB0 : 0 ≤ B := by simpa using hB m hm
      rw [MvPolynomial.eq_C_of_isEmpty p] at hp ⊢
      simpa [reservoirDraw, MvPolynomial.C_ne_zero.mp hp] using hB0
  | succ n ih =>
      intro p hp B hB
      let p' := MvPolynomial.finSuccEquiv k n p
      let d := p'.natDegree
      let q := p'.leadingCoeff
      have hp' : p' ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hp
      have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
      have hqB : ∀ m ∈ q.support,
          (∑ i : Fin n, (m i : ℝ) / sizes (n - 1 - i.val)) ≤
            B - (d : ℝ) / sizes n := by
        intro m hm
        have hm' : m.cons d ∈ p.support :=
          MvPolynomial.mem_support_coeff_finSuccEquiv.mp hm
        have hb := hB (m.cons d) hm'
        rw [Fin.sum_univ_succ] at hb
        have he (i : Fin n) : n - i.succ.val = n - 1 - i.val := by
          have := i.isLt
          simp only [Fin.val_succ]
          omega
        simp only [Finsupp.cons_zero, Finsupp.cons_succ, Fin.val_zero, Nat.sub_zero,
          Nat.add_sub_cancel, he] at hb
        linarith
      let polys (x : ℕ → k) := p'.map (MvPolynomial.eval (reversePrefix n x))
      have heval (x : ℕ → k) (a : k) :
          MvPolynomial.eval (reversePrefix (n+1) (Function.update x n a)) p =
            (polys x).eval a := by
        rw [reversePrefix_update]
        exact MvPolynomial.eval_eq_eval_mv_eval' _ _ _
      have hevent :
          Pr[fun x => MvPolynomial.eval (reversePrefix (n+1) x) p = 0 |
            reservoirDraw pool hne (n+1)] =
          Pr[fun b => b = true | reservoirDraw pool hne n >>= fun x =>
            (fun a => decide ((polys x).eval a = 0)) <$>
              draw (pool n x) (hne n x)] := by
        conv_lhs => rw [reservoirDraw, probEvent_bind_eq_tsum]
        conv_rhs => rw [probEvent_bind_eq_tsum]
        apply tsum_congr
        intro x
        congr 1
        conv_lhs => rw [probEvent_bind_eq_tsum]
        conv_rhs => rw [probEvent_map, probEvent_eq_tsum_ite]
        apply tsum_congr
        intro a
        simp only [probEvent_pure, Function.comp_def, heval, decide_eq_true_eq]
        split_ifs <;> simp
      rw [hevent]
      have hf := fiber_step (reservoirDraw pool hne n) polys (pool n) (hne n)
        d (sizes n) (hpos n) (fun _ _ => Polynomial.natDegree_map_le)
        (fun x _ => hsize n x)
      have hzero :
          (Pr[fun x => polys x = 0 | reservoirDraw pool hne n]).toReal ≤
          (Pr[fun x => MvPolynomial.eval (reversePrefix n x) q = 0 |
            reservoirDraw pool hne n]).toReal := by
        apply Shared.prob_mono
        intro x _ hx
        have h : (polys x).coeff d = 0 := by rw [hx, Polynomial.coeff_zero]
        dsimp only [polys] at h
        rw [Polynomial.coeff_map] at h
        exact h
      have hind := ih q hq (B - (d : ℝ) / sizes n) hqB
      linarith

lemma reservoir_sz (p : MvPolynomial ℕ k) (hp : p ≠ 0)
    (nc ng dc dg used : ℕ) (hdeg : BiDegree p nc ng dc dg)
    (pool : ℕ → (ℕ → k) → Finset k) (hne : ∀ j x, (pool j x).Nonempty)
    (hc : ∀ j < nc, ∀ x, P0.q - Constants.D ≤ (pool j x).card)
    (hg : ∀ j < ng, ∀ x, P0.q - used ≤ (pool (nc+j) x).card)
    (hu : used < P0.q) :
    (Pr[fun x => MvPolynomial.eval x p = 0 |
      reservoirDraw pool hne (nc+ng)]).toReal ≤
        (dc : ℝ) / ((P0.q : ℝ) - Constants.D) +
        (dg : ℝ) / ((P0.q : ℝ) - used) := by
  have hD : Constants.D < P0.q := by
    norm_num [P0, Params.main, Constants.q, Constants.D]
  let sizes (j : ℕ) := if j < nc then P0.q - Constants.D
    else if j < nc + ng then P0.q - used else 1
  have hpos (j : ℕ) : 0 < sizes j := by
    dsimp [sizes]
    split_ifs <;> omega
  have hsize (j : ℕ) (x : ℕ → k) : sizes j ≤ (pool j x).card := by
    dsimp [sizes]
    split_ifs with hj hj'
    · exact hc j hj x
    · have he : j = nc + (j - nc) := by omega
      rw [he]
      exact hg (j - nc) (by omega) x
    · exact (hne j x).card_pos
  let f : Fin (nc+ng) → ℕ := fun i => nc + ng - 1 - i.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    dsimp [f] at hij
    omega
  obtain ⟨p', he⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p f hf (by
    intro j hj
    have hj' := Finset.mem_range.mp (hdeg.1 hj)
    refine ⟨⟨nc + ng - 1 - j, by omega⟩, ?_⟩
    dsimp [f]
    omega)
  have hp' : p' ≠ 0 := by
    intro hz
    apply hp
    rw [← he, hz, map_zero]
  have hB (m : Fin (nc+ng) →₀ ℕ) (hm : m ∈ p'.support) :
      (∑ i : Fin (nc+ng), (m i : ℝ) / sizes (nc+ng-1-i.val)) ≤
        (dc : ℝ) / ((P0.q : ℝ) - Constants.D) +
        (dg : ℝ) / ((P0.q : ℝ) - used) := by
    let m' := Finsupp.mapDomain f m
    have hm' : m' ∈ p.support := by
      rw [← he, MvPolynomial.support_rename_of_injective hf]
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    have hmdeg := hdeg.2 m' hm'
    have hsum : (∑ i : Fin (nc+ng), (m i : ℝ) / sizes (nc+ng-1-i.val)) =
        ∑ j ∈ Finset.range (nc+ng), (m' j : ℝ) / sizes j := by
      apply Finset.sum_bij (fun i _ => f i)
      · intro i _
        have := i.isLt
        simp only [Finset.mem_range, f]
        omega
      · intro i _ j _ hij
        exact hf hij
      · intro j hj
        have hj' := Finset.mem_range.mp hj
        refine ⟨⟨nc+ng-1-j, by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp [f]
        omega
      · intro i _
        dsimp [m']
        rw [Finsupp.mapDomain_apply hf]
    rw [hsum, Finset.sum_range_add]
    have hcsize (j : ℕ) (hj : j ∈ Finset.range nc) :
        (sizes j : ℝ) = (P0.q : ℝ) - Constants.D := by
      simp only [sizes, if_pos (Finset.mem_range.mp hj)]
      exact Nat.cast_sub hD.le
    have hgsize (j : ℕ) (hj : j ∈ Finset.range ng) :
        (sizes (nc+j) : ℝ) = (P0.q : ℝ) - used := by
      have hj' := Finset.mem_range.mp hj
      simp only [sizes, if_neg (by omega : ¬nc+j < nc),
        if_pos (by omega : nc+j < nc+ng)]
      exact Nat.cast_sub hu.le
    have hcoin : (∑ j ∈ Finset.range nc, (m' j : ℝ) / sizes j) =
        (∑ j ∈ Finset.range nc, m' j : ℕ) / ((P0.q : ℝ) - Constants.D) := by
      rw [Nat.cast_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun j hj => by rw [hcsize j hj]
    have hguess : (∑ j ∈ Finset.range ng, (m' (nc+j) : ℝ) / sizes (nc+j)) =
        (∑ j ∈ Finset.range ng, m' (nc+j) : ℕ) / ((P0.q : ℝ) - used) := by
      rw [Nat.cast_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun j hj => by rw [hgsize j hj]
    rw [hcoin, hguess]
    exact add_le_add
      (div_le_div_of_nonneg_right (by exact_mod_cast hmdeg.1)
        (sub_nonneg.mpr (by exact_mod_cast hD.le)))
      (div_le_div_of_nonneg_right (by exact_mod_cast hmdeg.2)
        (sub_nonneg.mpr (by exact_mod_cast hu.le)))
  have hb := reservoir_weighted pool hne sizes hpos hsize (nc+ng) p' hp' _ hB
  have hevent :
      Pr[fun x => MvPolynomial.eval x p = 0 | reservoirDraw pool hne (nc+ng)] =
      Pr[fun x => MvPolynomial.eval (reversePrefix (nc+ng) x) p' = 0 |
        reservoirDraw pool hne (nc+ng)] := by
    apply probEvent_congr' _ rfl
    intro x _
    rw [← he, MvPolynomial.eval_rename]
    rfl
  rw [hevent]
  exact hb

lemma source1_rigid (ch : AdmissibleChoice P0) (S : Relation P0)
    (E F : Expr1 P0) (hn : ¬ FormalEq1 (ppOf ch S) E F) (r : Vec k P0.N) :
    ¬ (∀ c : Coins P0, ValidCoins (ppOf ch S).qap c →
      val1 (ppOf ch S) ⟨c,r⟩ E = val1 (ppOf ch S) ⟨c,r⟩ F) := by
  intro hi
  apply hn
  intro ω hω
  exact hi ω.coins hω

lemma source2_rigid (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (forms : FormMatrix P0) (E F : Expr2 P0)
    (hn : ¬ FormalEq2 (ppOf ch S) (formVec forms) E F) (r : Vec k P0.N) :
    ¬ (∀ c : Coins P0, ValidCoins (ppOf ch S).qap c →
      val2 (ppOf ch S) (formVec forms) ⟨c,r⟩ E =
        val2 (ppOf ch S) (formVec forms) ⟨c,r⟩ F) := by
  intro hi
  let D := pairExpr (Pi.single none 1) (E-F)
  have hD : IdentityAtR (ppOf ch S) (formVec forms) r D 0 := by
    intro c hc
    simpa [D, source2_aux_val, sub_eq_zero] using hi c hc
  apply hn
  intro ω hω
  have hD' := View.view_locus ch S hS forms D r 0 hD ω.r (by
    intro σ c
    simp [D, source2_aux_stack, source2_aux_sc])
  have hv := hD' ω.coins hω
  simpa [D, source2_aux_val, sub_eq_zero] using hv

structure GuessTest where
  polynomial : MvPolynomial ℕ k
  nonzero : polynomial ≠ 0
  nc : ℕ
  ng : ℕ
  dc : ℕ
  dg : ℕ
  used : ℕ
  degree : BiDegree polynomial nc ng dc dg
  coin_slack : dc + 3 ≤ Constants.eps_f_numerator
  guess_degree : dg ≤ 2
  used_le : used ≤ Constants.L + 3 * Constants.W_budget + 1
  pool : ℕ → (ℕ → k) → Finset k
  nonempty : ∀ j x, (pool j x).Nonempty
  coin_pool : ∀ j < nc, ∀ x, P0.q - Constants.D ≤ (pool j x).card
  guess_pool : ∀ j < ng, ∀ x, P0.q - used ≤ (pool (nc+j) x).card

def GuessTest.run (t : GuessTest) : ProbComp Bool :=
  (fun x => decide (MvPolynomial.eval x t.polynomial = 0)) <$>
    reservoirDraw t.pool t.nonempty (t.nc + t.ng)

lemma guess_test_bound (t : GuessTest) :
    (Pr[fun b => b = true | t.run]).toReal ≤ (Constants.eps_f : ℝ) := by
  have hu : t.used < P0.q := by
    have hmax : Constants.L + 3 * Constants.W_budget + 1 < P0.q := by
      norm_num [Constants.L, Constants.W_budget, P0, Params.main, Constants.q]
    exact t.used_le.trans_lt hmax
  have hs := reservoir_sz t.polynomial t.nonzero t.nc t.ng t.dc t.dg t.used
    t.degree t.pool t.nonempty t.coin_pool t.guess_pool hu
  have he : Pr[fun b => b = true | t.run] =
      Pr[fun x => MvPolynomial.eval x t.polynomial = 0 |
        reservoirDraw t.pool t.nonempty (t.nc + t.ng)] := by
    rw [GuessTest.run, probEvent_map]
    simp only [Function.comp_def, decide_eq_true_eq]
  rw [he]
  exact hs.trans (guess_allowance t.dc t.dg t.used t.coin_slack t.guess_degree t.used_le)

inductive Bounds (ch : AdmissibleChoice P0) (S : Relation P0) : Kind → Type
  | light (forms : FormMatrix P0) (D : ExprT P0) (ι : k)
      (hl : Light (markStack D)) : Bounds ch S .light
  | field (forms : FormMatrix P0) (D : ExprT P0) (ι : k) (r : Vec k P0.N)
      (hn : ¬ IdentityAtR (ppOf ch S) (formVec forms) r D ι) : Bounds ch S .field
  | source1 (E F : Expr1 P0) (r : Vec k P0.N)
      (hn : ¬ FormalEq1 (ppOf ch S) E F) : Bounds ch S .field
  | source2 (forms : FormMatrix P0) (E F : Expr2 P0) (r : Vec k P0.N)
      (hn : ¬ FormalEq2 (ppOf ch S) (formVec forms) E F) : Bounds ch S .field
  | guess (t : GuessTest) : Bounds ch S .guess
  | reservoir (pool : Finset (Label P0)) (hne : pool.Nonempty)
      (hsize : Constants.N_free ≤ pool.card) (target : Label P0) : Bounds ch S .reservoir
  | kdf (target : Fin (2^126)) : Bounds ch S .kdf
  | seed (target : Fin (2^128)) : Bounds ch S .seed

def Bounds.run {ch : AdmissibleChoice P0} {S : Relation P0} {i : Kind} :
    Bounds ch S i → ProbComp Bool
  | .light forms D ι _ =>
      (fun s => decide (IdentityAtR (ppOf ch S) (formVec forms) (rField s) D ι)) <$> searchLaw
  | .field forms D ι r _ =>
      (fun c => decide (valT (ppOf ch S) (formVec forms) ⟨c.val,r⟩ D =
        ι * kappa (ppOf ch S) c.val)) <$> coinLaw (ppOf ch S)
  | .source1 E F r _ =>
      (fun c => decide (val1 (ppOf ch S) ⟨c.val,r⟩ E =
        val1 (ppOf ch S) ⟨c.val,r⟩ F)) <$> coinLaw (ppOf ch S)
  | .source2 forms E F r _ =>
      (fun c => decide (val2 (ppOf ch S) (formVec forms) ⟨c.val,r⟩ E =
        val2 (ppOf ch S) (formVec forms) ⟨c.val,r⟩ F)) <$> coinLaw (ppOf ch S)
  | .guess t => t.run
  | .reservoir pool hne _ target => (fun x => decide (x = target)) <$> draw pool hne
  | .kdf target => (fun x => decide (x = target)) <$> ($ᵗ Fin (2^126))
  | .seed target => (fun x => decide (x = target)) <$> ($ᵗ Fin (2^128))

lemma test_bound (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (i : Kind) (t : Bounds ch S i) :
    (Pr[fun b => b = true | t.run]).toReal ≤ (rate i : ℝ) := by
  cases t with
  | light forms D ι hl =>
      simpa only [Bounds.run, probEvent_map, Function.comp_def, decide_eq_true_eq, rate]
        using fixed_light ch S hS forms D ι hl
  | field forms D ι r hn =>
      simpa only [Bounds.run, probEvent_map, Function.comp_def, decide_eq_true_eq, rate]
        using fixed_field ch S hS forms D ι r hn
  | source1 E F r hn =>
      simpa only [Bounds.run, probEvent_map, Function.comp_def, decide_eq_true_eq, rate]
        using Praxis.Proofs.GroupModel.Split.source1 ch S hS E F r hn
  | source2 forms E F r hn =>
      simpa only [Bounds.run, probEvent_map, Function.comp_def, decide_eq_true_eq, rate]
        using Praxis.Proofs.GroupModel.Split.source2 ch S hS forms E F r hn
  | guess t => exact guess_test_bound t
  | reservoir pool hne hsize target =>
      have hr := draw_hit pool hne target
      have hn : 0 < (Constants.N_free : ℝ) := by norm_num [Constants.N_free]
      have hs : (Constants.N_free : ℝ) ≤ pool.card := by exact_mod_cast hsize
      have he : (Pr[fun b => b = true |
          (Bounds.reservoir pool hne hsize target : Bounds ch S .reservoir).run]).toReal =
          (Pr[fun x => x = target | draw pool hne]).toReal := by
        rw [Bounds.run, probEvent_map]
        simp only [Function.comp_def, decide_eq_true_eq]
      rw [he]
      calc
        _ ≤ 1 / (pool.card : ℝ) := hr
        _ ≤ 1 / (Constants.N_free : ℝ) := one_div_le_one_div_of_le hn hs
        _ = (rate Kind.reservoir : ℝ) := by push_cast [rate]; rfl
  | kdf target =>
      rw [Bounds.run, probEvent_map]
      simp only [Function.comp_def, decide_eq_true_eq, probEvent_eq_eq_probOutput,
        probOutput_uniformSample, Fintype.card_fin, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      norm_num [rate]
  | seed target =>
      rw [Bounds.run, probEvent_map]
      simp only [Function.comp_def, decide_eq_true_eq, probEvent_eq_eq_probOutput,
        probOutput_uniformSample, Fintype.card_fin, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      norm_num [rate, Constants.statistical_seed]

lemma rate_nonneg (i : Kind) : 0 ≤ (rate i : ℝ) := by
  cases i <;> norm_num [rate, Constants.theta, Constants.eps_f,
    Constants.statistical_seed]

abbrev EventsOn (Ω : Type) (w : ℕ) := (i : Kind) → Fin (quota w i) → Ω → Prop

end Praxis.Proofs.GroupModel.Split.Lazy
