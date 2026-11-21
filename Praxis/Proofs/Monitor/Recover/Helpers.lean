import Praxis.Proofs.Monitor.Stop
import Praxis.Algebra.Probe.Span
import Praxis.Enc
import Praxis.Grid
import Praxis.Kummer
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Probe.SZ
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Stmt.ProbeSZ

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

open scoped BigOperators

def scalarValid {P : Params} (qap : QAPData P) (s : ScalarCoin) (a : Fq P) : Prop :=
  match s with
  | .tau => ∀ k, a ≠ qap.point k
  | .Om12 => True
  | .eps => a ≠ 0 ∧ ∀ k : Fin P.K1, a ≠ -(betaF P ^ (2 * k.val))⁻¹
  | _ => a ≠ 0

theorem validCoins_iff_scalarValid {P : Params} (qap : QAPData P) (c : Coins P) :
    ValidCoins qap c ↔ ∀ s, scalarValid qap s (c.2.2 s) := by
  constructor
  · rintro ⟨ht, hu, he, hk⟩ s
    cases s <;> simp_all [scalarValid, ScalarCoin.inUnits]
  · intro h
    refine ⟨h .tau, ?_, (h .eps).1, (h .eps).2⟩
    intro s hs
    have hh := h s
    cases s <;> simp_all [scalarValid, ScalarCoin.inUnits]

noncomputable def scalarExcluded {P : Params} (qap : QAPData P) : ScalarCoin → Finset (Fq P)
  | .tau => qap.pointSet
  | .Om12 => ∅
  | .eps => insert 0 (Finset.univ.image fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹)
  | _ => {0}

theorem scalarValid_iff_not_excluded {P : Params} (qap : QAPData P)
    (s : ScalarCoin) (a : Fq P) : scalarValid qap s a ↔ a ∉ scalarExcluded qap s := by
  classical
  cases s <;> simp [scalarValid, scalarExcluded, QAPData.pointSet, eq_comm]

theorem scalarExcluded_card_le {P : Params} (hP : P.Valid) (qap : QAPData P)
    (hKD : P.K1 + 1 ≤ P.D) (s : ScalarCoin) : (scalarExcluded qap s).card ≤ P.D := by
  classical
  have hD : 1 ≤ P.D := by omega
  have hpoint : qap.pointSet.card ≤ P.D := by
    unfold QAPData.pointSet
    calc
      _ ≤ Fintype.card (QAPIndex P) := by simpa using (Finset.card_image_le (s := (Finset.univ : Finset (QAPIndex P))) (f := qap.point))
      _ = P.D := by simp [QAPIndex, hP.D_eq, Nat.mul_comm]; omega
  have heps : (insert 0 (Finset.univ.image fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹)).card ≤ P.D := by
    calc
      _ ≤ (Finset.univ.image fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹).card + 1 := Finset.card_insert_le _ _
      _ ≤ P.K1 + 1 := by gcongr; simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin P.K1))) (f := fun k : Fin P.K1 => -(betaF P ^ (2 * k.val))⁻¹))
      _ ≤ P.D := hKD
  cases s <;> simp_all [scalarExcluded]

noncomputable def scalarSupport {P : Params} [NeZero P.q] (qap : QAPData P) (s : ScalarCoin) : Finset (Fq P) :=
  Finset.univ \ scalarExcluded qap s

theorem mem_scalarSupport {P : Params} [NeZero P.q] (qap : QAPData P) (s : ScalarCoin) (a : Fq P) :
    a ∈ scalarSupport qap s ↔ scalarValid qap s a := by
  classical
  simp [scalarSupport, scalarValid_iff_not_excluded]

theorem scalarSupport_card_lower {P : Params} [NeZero P.q] (hP : P.Valid) (qap : QAPData P)
    (hKD : P.K1 + 1 ≤ P.D) (s : ScalarCoin) :
    P.q - P.D ≤ (scalarSupport qap s).card := by
  classical
  have h := scalarExcluded_card_le hP qap hKD s
  have hc : (scalarSupport qap s).card + (scalarExcluded qap s).card = P.q := by
    unfold scalarSupport
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card]
    have he := Finset.card_le_univ (scalarExcluded qap s)
    simp only [ZMod.card] at he
    omega
  omega

theorem uniformProb_eq_probEvent {Ω : Type} [Fintype Ω] [SampleableType Ω] (E : Ω → Prop) :
    Algebra.ProbeSZ.uniformProb E = (Pr[E | $ᵗ Ω]).toReal := by
  classical
  rw [probEvent_uniformSample]
  simp [Algebra.ProbeSZ.uniformProb, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ENNReal.toReal_div]

theorem threeGradients_bound {P : Params} [Fact (Nat.Prime P.q)]
    {Ω : Type} [Fintype Ω] [SampleableType Ω] [SampleableType (Fin 3 → Ω)]
    (pp : PublicParams P) (D : ExprT P) (σ : Sector) (as : Ω → Assign P)
    (W : Stack P) (ε : ℝ) (hε : 0 ≤ ε)
    (hmem : ∀ a, rGrad pp (as a) D σ ∈ jointSpace W)
    (hrank : Module.finrank (Fq P) (jointSpace W) ≤ 3)
    (hbound : ∀ U : Submodule (Fq P) (Vec (Fq P) P.N), U < jointSpace W →
      (Pr[fun a => rGrad pp (as a) D σ ∈ U | $ᵗ Ω]).toReal ≤ ε) :
    (Pr[fun z : Fin 3 → Ω =>
      Submodule.span (Fq P) (Set.range (fun l => rGrad pp (as (z l)) D σ)) ≠ jointSpace W |
        $ᵗ (Fin 3 → Ω)]).toReal ≤ 3 * ε := by
  letI : FiniteDimensional (Fq P) (jointSpace W) := inferInstance
  have h := Algebra.ProbeSZ.uniformProb_triple_span (jointSpace W) (fun a => rGrad pp (as a) D σ)
    hmem hrank ε hε (fun U hU => by rw [uniformProb_eq_probEvent]; exact hbound U hU)
  simpa only [uniformProb_eq_probEvent, Function.comp_def] using h

theorem rcv_goodMark_unique {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    (w : WorldOut P) {D D' : ExprT P} {ι ι' : Fq P}
    (h : GoodMark pp w D ι) (h' : GoodMark pp w D' ι') : D = D' ∧ ι = ι' := by
  obtain ⟨k, hk, hd, _⟩ := h
  obtain ⟨k', hk', hd', _⟩ := h'
  have he : k = k' := Option.some.inj (hk.symm.trans hk')
  subst k'
  exact Prod.mk.inj (Option.some.inj (hd.symm.trans hd'))

theorem goodRecovery_iff {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    (w : WorldOut P) (D : ExprT P) (ι : Fq P) (h : GoodMark pp w D ι)
    (ω0 ω1 : Fin 3 → Assign P) :
    (∃ D' ι', GoodMark pp w D' ι' ∧
      gradSpan pp (recAssign ω0 ω1) D' (markSector D') ≠ jointSpace (markStack D')) ↔
    gradSpan pp (recAssign ω0 ω1) D (markSector D) ≠ jointSpace (markStack D) := by
  constructor
  · rintro ⟨D', ι', h', hf⟩
    obtain ⟨rfl, _⟩ := rcv_goodMark_unique pp w h' h
    exact hf
  · intro hf
    exact ⟨D, ι, h, hf⟩

theorem jointSpace_exists_column {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (U : Submodule (Fq P) (Vec (Fq P) P.N))
    (hU : U < jointSpace W) : ∃ c j, (fun i => W c i j) ∉ U := by
  classical
  by_contra! h
  apply hU.not_ge
  unfold jointSpace
  refine iSup_le fun c => ?_
  rintro x ⟨v, rfl⟩
  change (W c).mulVec v ∈ U
  rw [Algebra.ProbeSZ.mulVec_columns]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h c j)

theorem jointSpace_separating {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (U : Submodule (Fq P) (Vec (Fq P) P.N)) (hU : U < jointSpace W) :
    ∃ (cl : Cell P) (j : Fin (P.N + 1)) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P),
      φ (fun i => W cl i j) ≠ 0 ∧ U.map φ = ⊥ := by
  obtain ⟨cl, j, hj⟩ := jointSpace_exists_column W U hU
  obtain ⟨φ, hφ, hvan⟩ := U.exists_dual_map_eq_bot_of_notMem hj inferInstance
  exact ⟨cl, j, φ, hφ, hvan⟩

theorem cellExp_inj_kind {P : Params} {c c' : Cell P}
    (hk : c.2.1 = c'.2.1) (he : cellExp c = cellExp c') : c = c' := by
  rcases c with ⟨i, k, j⟩
  rcases c' with ⟨i', k', j'⟩
  dsimp at hk
  subst k'
  simp only [cellExp, legExp] at he
  have hi := i.isLt
  have hi' := i'.isLt
  have hj : j.val = j'.val := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hmul := Nat.mul_le_mul_left P.K1 (Nat.succ_le_of_lt hlt)
      nlinarith
    · have hmul := Nat.mul_le_mul_left P.K1 (Nat.succ_le_of_lt hgt)
      nlinarith
  have hii : i.val = i'.val := by rw [hj] at he; omega
  have : i = i' := Fin.ext hii
  have : j = j' := Fin.ext hj
  subst i'
  subst j'
  rfl

theorem gamma_expanded {P : Params} [Fact (Nat.Prime P.q)]
    (c : Coins P) (cl : Cell P) :
    gamma c cl = coin c .pi * bOf c cl.2.1 * coin c .u ^ (cellExp cl) *
      (1 + coin c .eps * thetaAt cl.1.val) := by
  simp only [gamma, piAt, legScale, legScaleAt, cellExp, legExp, pow_add]
  ring

theorem cellExp_lt {P : Params} (hP : P.Valid) (c : Cell P) : cellExp c < P.n := by
  have hi := c.1.isLt
  have hj := c.2.2.isLt
  have hb : c.2.1.base ≤ 1 := by cases c.2.1 <;> decide
  have hm := Nat.mul_le_mul_left P.K1 (Nat.succ_le_of_lt hj)
  simp only [cellExp, legExp]
  rw [hP.n_eq, ← hP.legs]
  nlinarith

abbrev ProbeVar (P : Params) := Fin (P.N + 1) ⊕ (LegKind ⊕ Bool)

noncomputable def recoveryPolynomial {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P) : MvPolynomial (ProbeVar P) (Fq P) :=
  ∑ cl : Cell P, ∑ j : Fin (P.N + 1),
    MvPolynomial.C (φ (fun i => W cl i j)) * MvPolynomial.X (.inr (.inl cl.2.1)) *
      MvPolynomial.X (.inr (.inr false)) ^ cellExp cl *
      (1 + MvPolynomial.X (.inr (.inr true)) * MvPolynomial.C (thetaAt cl.1.val)) *
      MvPolynomial.X (.inl j)

def recoveryValues {P : Params} [Fact (Nat.Prime P.q)] (c : Coins P) : ProbeVar P → Fq P
  | .inl i => c.1 i
  | .inr (.inl k) => bOf c k
  | .inr (.inr false) => coin c .u
  | .inr (.inr true) => coin c .eps

theorem recoveryPolynomial_eval {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P) (c : Coins P) :
    MvPolynomial.eval (recoveryValues c) (recoveryPolynomial W φ) =
      φ (∑ cl : Cell P,
        (bOf c cl.2.1 * coin c .u ^ cellExp cl *
          (1 + coin c .eps * thetaAt cl.1.val)) • (W cl).mulVec c.1) := by
  classical
  simp only [recoveryPolynomial, map_sum, map_mul, map_pow, map_add, map_one,
    MvPolynomial.eval_C, MvPolynomial.eval_X, recoveryValues, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro cl _
  rw [Algebra.ProbeSZ.mulVec_columns, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul, smul_eq_mul]
  ring

theorem recoveryPolynomial_degree {P : Params} [Fact (Nat.Prime P.q)]
    (hP : P.Valid) (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P) :
    (recoveryPolynomial W φ).totalDegree ≤ P.n + 2 := by
  classical
  unfold recoveryPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro cl _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  have h0 := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (φ (fun i => W cl i j)) : MvPolynomial (ProbeVar P) (Fq P)) (MvPolynomial.X (.inr (.inl cl.2.1)))
  have h1 := MvPolynomial.totalDegree_mul
    ((MvPolynomial.C (φ (fun i => W cl i j)) : MvPolynomial (ProbeVar P) (Fq P)) * MvPolynomial.X (.inr (.inl cl.2.1)))
    (MvPolynomial.X (.inr (.inr false)) ^ cellExp cl)
  have h2 := MvPolynomial.totalDegree_mul
    (MvPolynomial.X (.inr (.inr true)) : MvPolynomial (ProbeVar P) (Fq P))
    (MvPolynomial.C (thetaAt cl.1.val))
  have h3 := MvPolynomial.totalDegree_add
    (1 : MvPolynomial (ProbeVar P) (Fq P))
    (MvPolynomial.X (.inr (.inr true)) * MvPolynomial.C (thetaAt cl.1.val))
  have h4 := MvPolynomial.totalDegree_mul
    ((MvPolynomial.C (φ (fun i => W cl i j)) : MvPolynomial (ProbeVar P) (Fq P)) * MvPolynomial.X (.inr (.inl cl.2.1)) *
      MvPolynomial.X (.inr (.inr false)) ^ cellExp cl)
    (1 + MvPolynomial.X (.inr (.inr true)) * MvPolynomial.C (thetaAt cl.1.val))
  have h5 := MvPolynomial.totalDegree_mul
    ((MvPolynomial.C (φ (fun i => W cl i j)) : MvPolynomial (ProbeVar P) (Fq P)) * MvPolynomial.X (.inr (.inl cl.2.1)) *
      MvPolynomial.X (.inr (.inr false)) ^ cellExp cl *
      (1 + MvPolynomial.X (.inr (.inr true)) * MvPolynomial.C (thetaAt cl.1.val)))
    (MvPolynomial.X (.inl j))
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X,
    MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_one] at h0 h1 h2 h3 h4 h5
  have hc := cellExp_lt hP cl
  omega

noncomputable def probeMonomial {P : Params} (cl : Cell P) (j : Fin (P.N + 1)) : ProbeVar P →₀ ℕ :=
  Finsupp.single (.inr (.inl cl.2.1)) 1 + Finsupp.single (.inr (.inr false)) (cellExp cl) +
    Finsupp.single (.inl j) 1

theorem probeMonomial_inj {P : Params} {cl cl' : Cell P} {j j' : Fin (P.N + 1)}
    (h : probeMonomial cl j = probeMonomial cl' j') : cl = cl' ∧ j = j' := by
  classical
  have hk : cl.2.1 = cl'.2.1 := by
    have ht := congrArg (fun d : ProbeVar P →₀ ℕ => d (.inr (.inl cl.2.1))) h
    by_contra hn
    simp [probeMonomial, Finsupp.add_apply, Finsupp.single_apply, hn, Ne.symm hn] at ht
  have hj : j = j' := by
    have ht := congrArg (fun d : ProbeVar P →₀ ℕ => d (.inl j)) h
    by_contra hn
    simp [probeMonomial, Finsupp.add_apply, Finsupp.single_apply, hn, Ne.symm hn] at ht
  have he : cellExp cl = cellExp cl' := by
    have ht := congrArg (fun d : ProbeVar P →₀ ℕ => d (.inr (.inr false))) h
    simpa [probeMonomial, Finsupp.add_apply, Finsupp.single_apply] using ht
  exact ⟨cellExp_inj_kind hk he, hj⟩

theorem probeMonomial_eps_ne {P : Params} (cl cl' : Cell P) (j j' : Fin (P.N + 1)) :
    probeMonomial cl j + Finsupp.single (.inr (.inr true)) 1 ≠ probeMonomial cl' j' := by
  intro h
  have ht := congrArg (fun d : ProbeVar P →₀ ℕ => d (.inr (.inr true))) h
  simp [probeMonomial, Finsupp.add_apply, Finsupp.single_apply] at ht

theorem recoveryPolynomial_term {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P)
    (cl : Cell P) (j : Fin (P.N + 1)) :
    MvPolynomial.C (φ (fun i => W cl i j)) * MvPolynomial.X (.inr (.inl cl.2.1)) *
      MvPolynomial.X (.inr (.inr false)) ^ cellExp cl *
      (1 + MvPolynomial.X (.inr (.inr true)) * MvPolynomial.C (thetaAt cl.1.val)) *
      MvPolynomial.X (.inl j) =
    MvPolynomial.monomial (probeMonomial cl j) (φ (fun i => W cl i j)) +
      MvPolynomial.monomial (probeMonomial cl j + Finsupp.single (.inr (.inr true)) 1)
        (φ (fun i => W cl i j) * thetaAt cl.1.val) := by
  classical
  calc
    _ = (MvPolynomial.C (φ (fun i => W cl i j)) * MvPolynomial.X (.inr (.inl cl.2.1)) *
          MvPolynomial.X (.inr (.inr false)) ^ cellExp cl * MvPolynomial.X (.inl j)) +
        (MvPolynomial.C (φ (fun i => W cl i j) * thetaAt cl.1.val) *
          MvPolynomial.X (.inr (.inl cl.2.1)) * MvPolynomial.X (.inr (.inr false)) ^ cellExp cl *
          MvPolynomial.X (.inl j) * MvPolynomial.X (.inr (.inr true))) := by
      rw [map_mul]
      ring
    _ = _ := by
      rw [MvPolynomial.X_pow_eq_monomial]
      simp only [MvPolynomial.X, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul,
        mul_one, probeMonomial]

theorem recoveryPolynomial_coeff {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P)
    (cl : Cell P) (j : Fin (P.N + 1)) :
    (recoveryPolynomial W φ).coeff (probeMonomial cl j) = φ (fun i => W cl i j) := by
  classical
  have hm (cl' : Cell P) (j' : Fin (P.N + 1)) :
      probeMonomial cl' j' = probeMonomial cl j ↔ cl' = cl ∧ j' = j := by
    constructor
    · exact probeMonomial_inj
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [recoveryPolynomial, MvPolynomial.coeff_sum, recoveryPolynomial_term,
    MvPolynomial.coeff_add, MvPolynomial.coeff_monomial,
    probeMonomial_eps_ne, if_false, add_zero, hm]
  rw [Finset.sum_eq_single cl]
  · rw [Finset.sum_eq_single j]
    · simp only [true_and, if_true]
    · intro b _ hb
      simp only [true_and, hb, if_false]
    · intro h
      exact (h (Finset.mem_univ j)).elim
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro b _
    simp only [hc, false_and, if_false]
  · intro h
    exact (h (Finset.mem_univ cl)).elim

theorem recoveryPolynomial_ne_zero {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P)
    (cl : Cell P) (j : Fin (P.N + 1))
    (h : φ (fun i => W cl i j) ≠ 0) : recoveryPolynomial W φ ≠ 0 := by
  intro hz
  have hc := recoveryPolynomial_coeff W φ cl j
  rw [hz, MvPolynomial.coeff_zero] at hc
  exact h hc.symm

theorem weighted_stack_mem {P : Params} [Fact (Nat.Prime P.q)]
    (W : Stack P) (f : Cell P → Fq P) (y : Vec (Fq P) P.N) (a : Fq P) :
    a • (∑ cl : Cell P, f cl • (W cl).mulVec y) ∈ jointSpace W := by
  classical
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro cl _
  apply Submodule.smul_mem
  apply (le_iSup (fun cl => LinearMap.range (W cl).mulVecLin) cl)
  exact ⟨y, rfl⟩

theorem normalGradient_mem {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (D : ExprT P) (ω : Assign P) (σ : Sector)
    (hsym : ∀ cl, (exprStack D σ cl).IsSymm)
    (h : rGrad pp ω D σ = sectorScale ω.coins σ •
      ∑ cl : Cell P, gamma ω.coins cl • ((exprStack D σ cl).transpose.mulVec ω.coins.1)) :
    rGrad pp ω D σ ∈ jointSpace (exprStack D σ) := by
  rw [h]
  have heq : (∑ cl : Cell P, gamma ω.coins cl •
      ((exprStack D σ cl).transpose.mulVec ω.coins.1)) =
      ∑ cl : Cell P, gamma ω.coins cl • ((exprStack D σ cl).mulVec ω.coins.1) := by
    apply Finset.sum_congr rfl
    intro cl _
    rw [hsym cl]
  rw [heq]
  exact weighted_stack_mem (exprStack D σ) (gamma ω.coins) ω.coins.1 (sectorScale ω.coins σ)

theorem recoveryPolynomial_zero_of_mem {P : Params} [Fact (Nat.Prime P.q)]
    (qap : QAPData P) (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P)
    (U : Submodule (Fq P) (Vec (Fq P) P.N)) (c : Coins P) (σ : Sector)
    (hc : ValidCoins qap c) (hφ : U.map φ = ⊥)
    (hu : sectorScale c σ • (∑ cl : Cell P, gamma c cl • (W cl).mulVec c.1) ∈ U) :
    MvPolynomial.eval (recoveryValues c) (recoveryPolynomial W φ) = 0 := by
  classical
  have hpi : coin c .pi ≠ 0 := hc.2.1 .pi rfl
  have hsec : sectorScale c σ ≠ 0 := by
    cases σ with
    | plain => exact one_ne_zero
    | alpha => exact hc.2.1 .alpha rfl
  have hz : φ (sectorScale c σ • (∑ cl : Cell P, gamma c cl • (W cl).mulVec c.1)) = 0 := by
    have hh : φ (sectorScale c σ • (∑ cl : Cell P, gamma c cl • (W cl).mulVec c.1)) ∈ U.map φ :=
      Submodule.mem_map_of_mem hu
    rw [hφ, Submodule.mem_bot] at hh
    exact hh
  rw [recoveryPolynomial_eval]
  have heq : φ (sectorScale c σ • (∑ cl : Cell P, gamma c cl • (W cl).mulVec c.1)) =
      (sectorScale c σ * coin c .pi) *
        φ (∑ cl : Cell P,
          (bOf c cl.2.1 * coin c .u ^ cellExp cl *
            (1 + coin c .eps * thetaAt cl.1.val)) • (W cl).mulVec c.1) := by
    simp only [map_smul, map_sum, smul_eq_mul, gamma_expanded, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cl _
    ring
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hsec hpi)

end Praxis.Proofs.Monitor
