import Praxis.Proofs.GroupModel.Split.Shared
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Grid
import Praxis.Keys
import Praxis.Ledger
import Praxis.Proofs.Basic
import Praxis.Proofs.Sampling.Locus
import Praxis.Proofs.View.Forward
import Praxis.Proofs.View.Locus
import Praxis.Proofs.View.SZ
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Games
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 4096

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split

abbrev k := Fq P0

lemma zero_sectors (D : ExprT P0) (h : markStack D = 0) :
    exprStack D .plain = 0 ∧ exprStack D .alpha = 0 := by
  by_cases hp : exprStack D .plain = 0
  · exact ⟨hp, by simpa [markStack, markSector, hp] using h⟩
  · have : exprStack D .plain = 0 := by simpa [markStack, markSector, hp] using h
    exact (hp this).elim

lemma zero_formal (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) (r : Vec k P0.N) (ι : k)
    (hi : IdentityAtR (ppOf ch S) (formVec A) r D ι) (hz : markStack D = 0) :
    ∀ ω : Assign P0, ValidCoins (ppOf ch S).qap ω.coins →
      valT (ppOf ch S) (formVec A) ω D = ι * kappa (ppOf ch S) ω.coins := by
  have hzero : ∀ σ, exprStack D σ = 0 := by
    intro σ
    cases σ with
    | plain => exact (zero_sectors D hz).1
    | alpha => exact (zero_sectors D hz).2
  have heq := (View.view_forward ch S hS A D r ι hi).2
  intro ω hω
  have hi' : IdentityAtR (ppOf ch S) (formVec A) ω.r D ι :=
    View.view_locus ch S hS A D r ι hi ω.r (by
      intro σ c
      simpa [hzero σ] using heq σ c)
  exact hi' ω.coins hω

lemma fixed_light (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) (ι : k) (hl : Light (markStack D)) :
    (Pr[fun s => IdentityAtR (ppOf ch S) (formVec A) (rField s) D ι | searchLaw]).toReal ≤
      (Constants.theta : ℝ) := by
  calc
    _ ≤ (Pr[fun s => ∀ c, (markStack D c).mulVec (rField s) =
        exprSC D (markSector D) c | searchLaw]).toReal := by
      apply ENNReal.toReal_mono probEvent_ne_top
      exact probEvent_mono fun s _ hi =>
        (View.view_forward ch S hS A D (rField s) ι hi).2 (markSector D)
    _ ≤ gp (markStack D) := Sampling.light_locus (markStack D) (exprSC D (markSector D))
    _ ≤ (Constants.theta : ℝ) := hl

lemma fixed_field (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (D : ExprT P0) (ι : k) (r : Vec k P0.N)
    (hn : ¬ IdentityAtR (ppOf ch S) (formVec A) r D ι) :
    (Pr[fun c => valT (ppOf ch S) (formVec A) ⟨c.val,r⟩ D = ι * kappa (ppOf ch S) c.val |
      coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ) := by
  exact Praxis.Proofs.View.view_sz ch S hS A D r ι hn

lemma source1_aux_pair_value {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    (v : Fin P.n → Vec (Fq P) P.N) (ω : Assign P) (E : Expr1 P) :
    valT pp v ω (pairExpr E (Pi.single none 1)) = val1 pp ω E := by
  classical
  simp [pairExpr, valT, val1, keys2, e2At, Pi.single_apply, Function.comp_def]

lemma source1_aux_sub (pp : PublicParams P0) (ω : Assign P0) (E F : Expr1 P0) :
    val1 pp ω (E - F) = val1 pp ω E - val1 pp ω F := by
  simp only [val1, Pi.sub_apply, sub_mul]
  generalize keys1 P0 = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

lemma source1 (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (E F : Expr1 P0) (r : Vec k P0.N) (hn : ¬ FormalEq1 (ppOf ch S) E F) :
    (Pr[fun c => val1 (ppOf ch S) ⟨c.val,r⟩ E = val1 (ppOf ch S) ⟨c.val,r⟩ F |
      coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ) := by
  classical
  let D : ExprT P0 := pairExpr (E - F) (Pi.single none 1)
  have hn' : ¬ IdentityAtR (ppOf ch S) (formVec (0 : FormMatrix P0)) r D 0 := by
    intro hi
    apply hn
    intro ω hω
    have h := hi ω.coins hω
    simp only [D, source1_aux_pair_value, source1_aux_sub,
      zero_mul, sub_eq_zero] at h
    exact h
  have hb := View.view_sz ch S hS (0 : FormMatrix P0) D r 0 hn'
  simpa only [D, source1_aux_pair_value, source1_aux_sub, zero_mul, sub_eq_zero] using hb

lemma source2_aux_pair_val {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (ω : Assign P) (B : Expr2 P) :
    valT pp v ω (pairExpr (Pi.single none 1) B) = val2 pp v ω B := by
  classical
  simp [valT, pairExpr, keys1, e1At, val2, Function.comp_def]

lemma source2_aux_sub_val {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (ω : Assign P) (E F : Expr2 P) :
    val2 pp v ω (E - F) = val2 pp v ω E - val2 pp v ω F := by
  unfold val2
  simp only [Pi.sub_apply, sub_mul]
  induction keys2 P with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    abel

lemma source2_aux_val {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (ω : Assign P) (E F : Expr2 P) :
    valT pp v ω (pairExpr (Pi.single none 1) (E - F)) =
      val2 pp v ω E - val2 pp v ω F := by
  rw [source2_aux_pair_val, source2_aux_sub_val]

lemma source2_aux_stack {P : Params} (E F : Expr2 P) (σ : Sector) :
    exprStack (pairExpr (Pi.single none 1) (E - F)) σ = 0 := by
  classical
  funext c i j
  simp [exprStack, pairExpr]

lemma source2_aux_sc {P : Params} (E F : Expr2 P) (σ : Sector) (c : Cell P) :
    exprSC (pairExpr (Pi.single none 1) (E - F)) σ c = 0 := by
  classical
  funext i
  simp [exprSC, pairExpr]

lemma source2 (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (A : FormMatrix P0) (E F : Expr2 P0) (r : Vec k P0.N)
    (hn : ¬ FormalEq2 (ppOf ch S) (formVec A) E F) :
    (Pr[fun c => val2 (ppOf ch S) (formVec A) ⟨c.val,r⟩ E =
      val2 (ppOf ch S) (formVec A) ⟨c.val,r⟩ F | coinLaw (ppOf ch S)]).toReal ≤
      (Constants.eps_f : ℝ) := by
  let D : ExprT P0 := pairExpr (Pi.single none 1) (E - F)
  have hD : ¬ IdentityAtR (ppOf ch S) (formVec A) r D 0 := by
    intro hi
    apply hn
    intro ω hω
    have hi' := View.view_locus ch S hS A D r 0 hi ω.r (by
      intro σ c
      simp [D, source2_aux_stack, source2_aux_sc])
    have hv := hi' ω.coins hω
    simpa [D, source2_aux_val, sub_eq_zero] using hv
  have hb := View.view_sz ch S hS A D r 0 hD
  simpa only [D, source2_aux_val, zero_mul, sub_eq_zero] using hb

inductive Kind | light | field | guess | reservoir | kdf | seed
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.light, .field, .guess, .reservoir, .kdf, .seed}
  complete := fun i => by cases i <;> simp

private def lazyRun_auxEncodingEquiv :
    ((k ↪ Label P0) × (k ↪ Label P0) × (k ↪ Label P0)) ≃ LabelEncoding P0 where
  toFun t := fun s => match s with | .g₁ => t.1 | .g₂ => t.2.1 | .gₜ => t.2.2
  invFun σ := (σ .g₁, σ .g₂, σ .gₜ)
  left_inv _ := rfl
  right_inv σ := by funext s; cases s <;> rfl

private noncomputable instance lazyRun_auxFintype : Fintype (LabelEncoding P0) :=
  Fintype.ofEquiv _ lazyRun_auxEncodingEquiv

private noncomputable instance lazyRun_auxDecEq : DecidableEq (LabelEncoding P0) :=
  Classical.decEq _

private noncomputable def lazyRun_auxUniform {H : Type} [Fintype H] [Nonempty H]
    (W : Finset H) : ProbComp H := by
  classical
  exact if h : W.Nonempty then
    letI : Nonempty {σ // σ ∈ W} := h.to_subtype
    letI := SampleableType.ofFintype {σ // σ ∈ W}
    Subtype.val <$> ($ᵗ {σ // σ ∈ W})
  else pure (Classical.arbitrary H)

private inductive lazyRun_auxQuery
  | initial (pp : PublicParams P0) (forms : FormMatrix P0) (c : Coins P0)
  | group (issued : Finset (Label P0)) (q : GQuery P0)

private def lazyRun_auxRange : lazyRun_auxQuery → Type
  | .initial .. => (PubView P0 × ClassName P0) × (Label P0 × Label P0)
  | .group _ q => (Option k × Option k) × q.Result

private abbrev lazyRun_auxModel := OracleSpec.ofFn lazyRun_auxRange

private abbrev lazyRun_auxMixed := unifSpec + lazyRun_auxModel

private abbrev lazyRun_auxM := StateT (OracleState P0) (OracleComp lazyRun_auxMixed)

private noncomputable def lazyRun_auxOperands (σ : LabelEncoding P0)
    (issued : Finset (Label P0)) : GQuery P0 → Option k × Option k
  | .lin s _ _ u v => (Algebra.decodeLabel (σ s) u, Algebra.decodeLabel (σ s) v)
  | .pair u v => (Algebra.decodeLabel (σ .g₁) u, Algebra.decodeLabel (σ .g₂) v)
  | .name v => (if v ∈ issued then Algebra.decodeLabel (σ .gₜ) v else none, none)

private noncomputable def lazyRun_auxObserve (σ : LabelEncoding P0) :
    (q : lazyRun_auxQuery) → lazyRun_auxRange q
  | .initial pp forms c =>
      ((pubView σ pp (formVec forms) c, labelName (σ .gₜ) (kappa pp c)),
        (σ .gₜ (kappa pp c), σ .gₜ (-kappa pp c)))
  | .group issued q => (lazyRun_auxOperands σ issued q, groupAnswer σ issued q)

private noncomputable def lazyRun_auxLift {α : Type} (c : GameM P0 α) : lazyRun_auxM α :=
  StateT.mk fun st => simulateQ (QueryImpl.ofLift unifSpec (OracleComp lazyRun_auxMixed))
    (c.run st)

private noncomputable def lazyRun_auxFinishGroup (qr : GQuery P0) (r : qr.Result) :
    GameM P0 qr.Answer := do
    match trEntry qr r with
    | some e => modify fun st =>
        { st with
          tr := st.tr ++ [e]
          issuedT := match e.issuedGT with
            | some l => insert l st.issuedT
            | none => st.issuedT }
    | none => pure ()
    handOut qr r

private noncomputable def lazyRun_auxGroup : QueryImpl (groupModel P0) lazyRun_auxM :=
  fun qr => do
    let issued := (← get).issuedT
    let ob ← (StateT.lift (liftM (lazyRun_auxModel.query (.group issued qr))) : lazyRun_auxM _)
    lazyRun_auxLift (lazyRun_auxFinishGroup qr ob.2)

private noncomputable def lazyRun_auxHandler : QueryImpl (AdvModel P0) lazyRun_auxM :=
  (((QueryImpl.ofLift unifSpec (OracleComp lazyRun_auxMixed)).liftTarget lazyRun_auxM +
    lazyRun_auxGroup) + (fun i => lazyRun_auxLift (hfLazy i))) +
    (fun q => lazyRun_auxLift (kdfImpl q))

private noncomputable def lazyRun_auxPrefix (pp : PublicParams P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] :
    GameM P0 (Seed P0 × FormMatrix P0 × Coins P0) :=
  letI := SampleableType.ofFintype {c : Coins P0 // ValidCoins pp.qap c}
  do
    let seed ← StateT.lift ($ᵗ (Seed P0))
    let entries ← (formIndexList P0).mapM fun i => do
      let a ← hfLazy (seed, i)
      pure (i, a)
    let forms : FormMatrix P0 := fun i =>
      ((entries.find? fun e => decide (e.1 = i)).map Prod.snd).getD 0
    let c ← StateT.lift ($ᵗ {c : Coins P0 // ValidCoins pp.qap c})
    pure (seed, forms, c.val)

private noncomputable def lazyRun_auxFinishEnc (m : Msg P0)
    (p : Seed P0 × FormMatrix P0 × Coins P0) (ob : PubView P0 × ClassName P0) :
    GameM P0 (EncOut P0) := do
  let pad ← kdfLazy ob.2
  modify fun st => { st with issuedT := st.issuedT ∪ (ob.1.gT.map Prod.snd).toFinset }
  pure ⟨ob.1, ⟨p.1, m ^^^ pad⟩, p.2.1, p.2.2⟩

private noncomputable def lazyRun_auxEnc (pp : PublicParams P0) (m : Msg P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] : lazyRun_auxM (EncOut P0) := do
  let p ← lazyRun_auxLift (lazyRun_auxPrefix pp)
  let ob ← (StateT.lift (liftM (lazyRun_auxModel.query (.initial pp p.2.1 p.2.2))) : lazyRun_auxM _)
  lazyRun_auxLift (lazyRun_auxFinishEnc m p ob.1)

private noncomputable def lazyRun_auxProgram (pp : PublicParams P0) (m : Msg P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (A : Adversary P0) :=
  (do
    let e ← lazyRun_auxEnc pp m
    let o ← simulateQ lazyRun_auxHandler (A.run e.pv e.header)
    pure (e, o)).run OracleState.empty

private noncomputable def lazyRun_auxPosterior {α : Type}
    (c : OracleComp lazyRun_auxMixed α) :
    Finset (LabelEncoding P0) → ProbComp (α × LabelEncoding P0) :=
  OracleComp.construct
    (fun a W => (fun σ => (a, σ)) <$> lazyRun_auxUniform W)
    (fun q _ ih W => by
      classical
      cases q with
      | inl n => exact (liftM (unifSpec.query n) : ProbComp _) >>= fun u => ih u W
      | inr q => exact do
          let σ ← lazyRun_auxUniform W
          let y := lazyRun_auxObserve σ q
          ih y (W.filter fun σ' => lazyRun_auxObserve σ' q = y)) c

noncomputable def lazyRun (ch : AdmissibleChoice P0) (S : Relation P0)
    (m : Msg P0) (A : Adversary P0) : ProbComp (WorldOut P0) := by
  classical
  exact (fun z => ⟨z.2, z.1.1.1, z.1.1.2, z.1.2⟩) <$>
    lazyRun_auxPosterior (lazyRun_auxProgram (ppOf ch S) m A) Finset.univ

private noncomputable def lazy_law_auxEager (σ : LabelEncoding P0) :
    QueryImpl lazyRun_auxMixed ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (fun q => pure (lazyRun_auxObserve σ q) : QueryImpl lazyRun_auxModel ProbComp)

private lemma lazy_law_auxUniformQuery (σ : LabelEncoding P0) (n : ℕ) :
    simulateQ (lazy_law_auxEager σ)
      (liftM (lazyRun_auxMixed.query (.inl n))) =
        (liftM (unifSpec.query n) : ProbComp _) := by
  rw [simulateQ_spec_query]
  rfl

private lemma lazy_law_auxSubQuery (σ : LabelEncoding P0) (q : lazyRun_auxQuery) :
    simulateQ (lazy_law_auxEager σ)
      (liftM (lazyRun_auxModel.query q) : OracleComp lazyRun_auxMixed _) =
        pure (lazyRun_auxObserve σ q) := by
  exact QueryImpl.simulateQ_add_liftM_query_right _ _ q

open scoped ENNReal in
private lemma lazy_law_auxUniform_mass {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]
    (W : Finset H) (hW : W.Nonempty) (σ : H) :
    Pr[= σ | lazyRun_auxUniform W] = if σ ∈ W then ((W.card : ℝ≥0∞))⁻¹ else 0 := by
  classical
  by_cases hσ : σ ∈ W
  · rw [if_pos hσ]
    simp only [lazyRun_auxUniform, dif_pos hW]
    rw [show σ = (⟨σ, hσ⟩ : {σ // σ ∈ W}).val from rfl,
      probOutput_map_injective _ Subtype.val_injective]
    simp
  · rw [if_neg hσ]
    apply probOutput_eq_zero
    simp only [lazyRun_auxUniform, dif_pos hW, support_map, Set.mem_image,
      not_exists, not_and]
    intro x _ hx
    exact hσ (hx ▸ x.prop)

open scoped ENNReal in

private lemma lazy_law_auxDisintegrate {H R B : Type} [Fintype H] [Nonempty H]
    [DecidableEq H] [DecidableEq R] (W : Finset H) (f : H → R)
    (cont : R → H → ProbComp B) :
    evalSPMF (lazyRun_auxUniform W >>= fun σ =>
      lazyRun_auxUniform (W.filter fun σ' => f σ' = f σ) >>= cont (f σ)) =
    evalSPMF (lazyRun_auxUniform W >>= fun σ => cont (f σ) σ) := by
  classical
  by_cases hW : W.Nonempty
  swap
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst he
    simp [lazyRun_auxUniform]
  apply evalSPMF_ext
  intro b
  simp only [probOutput_bind_eq_tsum, tsum_fintype, lazy_law_auxUniform_mass W hW]
  set F : H → Finset H :=
    fun σ => W.filter fun σ' => f σ' = f σ with hF
  have hFne : ∀ σ ∈ W, (F σ).Nonempty := fun σ hσ => ⟨σ, by simp [hF, hσ]⟩
  have hFeq : ∀ σ σ', f σ' = f σ → F σ' = F σ := by
    intro σ σ' h
    simp only [hF, h]
  have inner : ∀ σ ∈ W,
      (∑ σ', Pr[= σ' | lazyRun_auxUniform (F σ)] * Pr[= b | cont (f σ) σ']) =
      ∑ σ', if σ' ∈ F σ then
        ((F σ).card : ℝ≥0∞)⁻¹ * Pr[= b | cont (f σ') σ'] else 0 := by
    intro σ hσ
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [lazy_law_auxUniform_mass (F σ) (hFne σ hσ)]
    split_ifs with h
    · rw [(Finset.mem_filter.mp h).2]
    · simp
  calc
    _ = ∑ σ, ∑ σ', if σ ∈ W then
        (if σ' ∈ F σ then ((W.card : ℝ≥0∞))⁻¹ *
          (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | cont (f σ') σ']) else 0) else 0 := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs with hσ
      · rw [inner σ hσ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ' _ => ?_
        split_ifs with h
        · rw [hFeq σ σ' (Finset.mem_filter.mp h).2]
        · simp
      · simp
    _ = ∑ σ', ∑ σ, if σ ∈ W then
        (if σ' ∈ F σ then ((W.card : ℝ≥0∞))⁻¹ *
          (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | cont (f σ') σ']) else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ σ', if σ' ∈ W then
        ((W.card : ℝ≥0∞))⁻¹ * Pr[= b | cont (f σ') σ'] else 0 := by
      refine Finset.sum_congr rfl fun σ' _ => ?_
      by_cases hσ' : σ' ∈ W
      · rw [if_pos hσ']
        have hset : ∀ σ, (if σ ∈ W then
            (if σ' ∈ F σ then ((W.card : ℝ≥0∞))⁻¹ *
              (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | cont (f σ') σ']) else 0) else 0) =
            if σ ∈ F σ' then ((W.card : ℝ≥0∞))⁻¹ *
              (((F σ').card : ℝ≥0∞)⁻¹ * Pr[= b | cont (f σ') σ']) else 0 := by
          intro σ
          by_cases hσ : σ ∈ W
          · have hiff : σ' ∈ F σ ↔ σ ∈ F σ' := by
              simp only [hF, Finset.mem_filter, hσ, hσ', true_and]
              exact eq_comm
            simp only [if_pos hσ, hiff]
          · have : σ ∉ F σ' := fun h => hσ (Finset.mem_filter.mp h).1
            simp [hσ, this]
        simp only [hset]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        have hc : ((F σ').card : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast (Finset.card_pos.mpr (hFne σ' hσ')).ne'
        rw [← mul_assoc, mul_comm ((F σ').card : ℝ≥0∞), mul_assoc,
          ← mul_assoc _ _ (Pr[= b | _]),
          ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), one_mul]
      · rw [if_neg hσ']
        apply Finset.sum_eq_zero
        intro σ _
        split_ifs with hσ h
        · exact absurd (Finset.mem_filter.mp h).1 hσ'
        · rfl
        · rfl
    _ = _ := by
      refine Finset.sum_congr rfl fun σ' _ => ?_
      split_ifs <;> simp

private lemma lazy_law_auxPosterior {α : Type} (c : OracleComp lazyRun_auxMixed α)
    (W : Finset (LabelEncoding P0)) :
    evalSPMF (lazyRun_auxPosterior c W) =
      evalSPMF (lazyRun_auxUniform W >>= fun σ =>
        (fun a => (a, σ)) <$> simulateQ (lazy_law_auxEager σ) c) := by
  classical
  induction c using OracleComp.inductionOn generalizing W with
  | pure a => simp [lazyRun_auxPosterior, map_eq_bind_pure_comp]
  | query_bind q cont ih =>
      cases q with
      | inl n =>
          simp only [lazyRun_auxPosterior, OracleComp.construct_query_bind]
          simp only [simulateQ_bind, simulateQ_spec_query, lazy_law_auxEager,
            QueryImpl.add_apply_inl, map_bind]
          calc
            _ = evalSPMF ((liftM (unifSpec.query n) : ProbComp _) >>= fun u =>
                lazyRun_auxUniform W >>= fun σ =>
                  (fun a => (a, σ)) <$> simulateQ (lazy_law_auxEager σ) (cont u)) :=
              evalSPMF_bind_congr fun u _ => ih u W
            _ = _ := evalSPMF_bind_bind_swap _ _ _
      | inr q =>
          simp only [lazyRun_auxPosterior, OracleComp.construct_query_bind]
          simp only [simulateQ_bind, simulateQ_spec_query, lazy_law_auxEager,
            QueryImpl.add_apply_inr, pure_bind]
          calc
            _ = evalSPMF (lazyRun_auxUniform W >>= fun σ =>
                lazyRun_auxUniform
                  (W.filter fun σ' => lazyRun_auxObserve σ' q = lazyRun_auxObserve σ q) >>=
                    fun σ' => (fun a => (a, σ')) <$>
                      simulateQ (lazy_law_auxEager σ') (cont (lazyRun_auxObserve σ q))) :=
              evalSPMF_bind_congr fun σ _ => ih _ _
            _ = _ := lazy_law_auxDisintegrate W
              (fun σ => lazyRun_auxObserve σ q)
              (fun y σ => (fun a => (a, σ)) <$>
                simulateQ (lazy_law_auxEager σ) (cont y))

private lemma lazy_law_auxLift {α : Type} (σ : LabelEncoding P0) (c : GameM P0 α)
    (st : OracleState P0) :
    simulateQ (lazy_law_auxEager σ) ((lazyRun_auxLift c).run st) = c.run st := by
  change simulateQ (lazy_law_auxEager σ)
    (simulateQ (QueryImpl.ofLift unifSpec (OracleComp lazyRun_auxMixed)) (c.run st)) = _
  rw [← QueryImpl.simulateQ_compose]
  have h : lazy_law_auxEager σ ∘ₛ
      QueryImpl.ofLift unifSpec (OracleComp lazyRun_auxMixed) = QueryImpl.id' unifSpec := by
    funext n
    exact lazy_law_auxUniformQuery σ n
  rw [h, simulateQ_id']

private lemma lazy_law_auxObserveLift {α : Type} (σ : LabelEncoding P0)
    (q : lazyRun_auxQuery) (f : lazyRun_auxRange q → GameM P0 α)
    (st : OracleState P0) :
    simulateQ (lazy_law_auxEager σ) ((do
      let y ← (StateT.lift (liftM (lazyRun_auxModel.query q)) : lazyRun_auxM _)
      lazyRun_auxLift (f y)).run st) = (f (lazyRun_auxObserve σ q)).run st := by
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind,
    bind_map_left, lazy_law_auxSubQuery]
  change simulateQ (lazy_law_auxEager σ)
    ((lazyRun_auxLift (f (lazyRun_auxObserve σ q))).run st) = _
  exact lazy_law_auxLift σ _ st

private lemma lazy_law_auxGroup_factor (σ : LabelEncoding P0) (q : GQuery P0)
    (st : OracleState P0) :
    (groupImpl σ q).run st =
      (lazyRun_auxFinishGroup q (groupAnswer σ st.issuedT q)).run st := by
  simp only [groupImpl, lazyRun_auxFinishGroup, StateT.run_bind, StateT.run_get, pure_bind]
  cases ht : trEntry q (groupAnswer σ st.issuedT q) with
  | none => simp only [ht]
  | some e =>
      cases hi : e.issuedGT <;> simp only [ht, hi]

private lemma lazy_law_auxHandler (σ : LabelEncoding P0) (q : (AdvModel P0).Domain)
    (st : OracleState P0) :
    simulateQ (lazy_law_auxEager σ) ((lazyRun_auxHandler q).run st) =
      ((gameImpl σ q).run st) := by
  rcases q with ((n | q) | i) | q
  · change simulateQ (lazy_law_auxEager σ)
      ((fun u => (u, st)) <$> (liftM (lazyRun_auxMixed.query (.inl n)))) =
        (fun u => (u, st)) <$> (liftM (unifSpec.query n) : ProbComp _)
    rw [simulateQ_map, lazy_law_auxUniformQuery]
    rfl
  · change simulateQ (lazy_law_auxEager σ) ((lazyRun_auxGroup q).run st) =
      (groupImpl σ q).run st
    rw [lazy_law_auxGroup_factor]
    simpa only [lazyRun_auxGroup, StateT.run_bind, StateT.run_get, pure_bind,
      lazyRun_auxObserve] using
      lazy_law_auxObserveLift σ (.group st.issuedT q)
        (fun ob => lazyRun_auxFinishGroup q ob.2) st
  · exact lazy_law_auxLift σ (hfLazy i) st
  · exact lazy_law_auxLift σ (kdfImpl q) st

private lemma lazy_law_auxEnc_factor (pp : PublicParams P0) (m : Msg P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (σ : LabelEncoding P0) :
    encGame σ pp m = (do
      let p ← lazyRun_auxPrefix pp
      lazyRun_auxFinishEnc m p
        (pubView σ pp (formVec p.2.1) p.2.2, labelName (σ .gₜ) (kappa pp p.2.2))) := by
  simp only [encGame, encAt, lazyRun_auxPrefix, lazyRun_auxFinishEnc, bind_assoc, pure_bind]

private lemma lazy_law_auxEnc (pp : PublicParams P0) (m : Msg P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (σ : LabelEncoding P0)
    (st : OracleState P0) :
    simulateQ (lazy_law_auxEager σ) ((lazyRun_auxEnc pp m).run st) =
      (encGame σ pp m).run st := by
  rw [lazy_law_auxEnc_factor]
  simp only [lazyRun_auxEnc, StateT.run_bind,
    simulateQ_bind, lazy_law_auxLift]
  refine bind_congr (fun z => ?_)
  simpa only [StateT.run_bind, simulateQ_bind, lazy_law_auxLift, lazyRun_auxObserve] using
    lazy_law_auxObserveLift σ (.initial pp z.1.2.1 z.1.2.2)
      (fun ob => lazyRun_auxFinishEnc m z.1 ob.1) z.2

private lemma lazy_law_auxProgram (pp : PublicParams P0) (m : Msg P0)
    [Nonempty {c : Coins P0 // ValidCoins pp.qap c}] (A : Adversary P0)
    (σ : LabelEncoding P0) :
    simulateQ (lazy_law_auxEager σ) (lazyRun_auxProgram pp m A) =
      runWith σ A (encGame σ pp m) OracleState.empty := by
  simp only [lazyRun_auxProgram, runWith, StateT.run_bind, simulateQ_bind, lazy_law_auxEnc]
  congr 1
  funext z
  rw [simulateQ_StateT_compose lazyRun_auxHandler (lazy_law_auxEager σ)
    (gameImpl σ) (lazy_law_auxHandler σ)]
  simp

private lemma lazy_law_auxThree {H E α : Type} [Fintype H] [Nonempty H]
    [SampleableType H] [Fintype E] [Nonempty E] (e : (H × H × H) ≃ E)
    (f : E → ProbComp α) :
    evalSPMF (do
      let x ← $ᵗ H
      let y ← $ᵗ H
      let z ← $ᵗ H
      f (e (x, y, z))) =
      evalSPMF (lazyRun_auxUniform Finset.univ >>= f) := by
  classical
  letI : DecidableEq E := Classical.decEq _
  letI : DecidableEq H := Classical.decEq _
  apply evalSPMF_ext
  intro a
  simp only [probOutput_bind_eq_tsum,
    tsum_fintype, probOutput_uniformSample,
    lazy_law_auxUniform_mass Finset.univ Finset.univ_nonempty,
    Finset.mem_univ, if_true, Finset.card_univ]
  have hc : Fintype.card E = Fintype.card H ^ 3 := by
    rw [← Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod]
    ring
  rw [hc]
  rw [← Fintype.sum_equiv e
    (fun t => _ * Pr[= a | f (e t)])
    (fun σ => _ * Pr[= a | f σ]) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ1 _ => ?_
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ2 _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σT _ => ?_
  rw [Nat.cast_pow, ENNReal.inv_pow, pow_three]
  simp only [mul_assoc]

private lemma lazy_law_auxPrior {α : Type} (f : LabelEncoding P0 → ProbComp α) :
    evalSPMF ((sampleEncoding : ProbComp (LabelEncoding P0)) >>= f) =
      evalSPMF (lazyRun_auxUniform Finset.univ >>= f) := by
  simp only [sampleEncoding, bind_assoc, pure_bind]
  exact lazy_law_auxThree lazyRun_auxEncodingEquiv f

lemma lazy_law (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0) (A : Adversary P0) :
    evalSPMF (lazyRun ch S m A) = evalSPMF (worldRun (ppOf ch S) m A) := by
  classical
  rw [lazyRun, evalSPMF_map, lazy_law_auxPosterior, ← evalSPMF_map]
  simp only [map_bind, Functor.map_map]
  rw [worldRun, lazy_law_auxPrior]
  apply evalSPMF_bind_congr
  intro σ _
  rw [lazy_law_auxProgram]
  simp only [Function.comp_apply, map_eq_bind_pure_comp, Function.comp_def]

def allowance (w : ℕ) : Kind → ℚ
  | .light => ledgerJ w * Constants.theta
  | .field => ledgerJ w * Constants.eps_f
  | .guess => Praxis.choose2 (Constants.L + 3*w) * Constants.eps_f +
      (Constants.L + 3*w : ℕ) * Constants.eps_f
  | .reservoir => (2 * (Constants.L : ℚ) + 4*w + 2*Constants.T) / Constants.N_free
  | .kdf => 4 * (w : ℚ) / 2^126
  | .seed => Constants.statistical_seed

lemma sum_allowance (w : ℕ) : (∑ i : Kind, allowance w i) = ledgerCmp w := by
  simp [Finset.univ, Fintype.elems, allowance, ledgerCmp]
  ring

end Praxis.Proofs.GroupModel.Split

namespace Praxis.Proofs.GroupModel.Split

lemma guess_fiber_aux_card (p : Polynomial k) (hp : p ≠ 0) (pool : Finset k) :
    (Finset.univ.filter fun x : {x : k // x ∈ pool} => p.eval x.val = 0).card ≤
      p.natDegree := by
  classical
  have hc : (Finset.univ.filter fun x : {x : k // x ∈ pool} => p.eval x.val = 0).card ≤
      p.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      simpa only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp,
        Polynomial.IsRoot] using (Finset.mem_filter.mp hx).2
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  exact hc.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

lemma guess_fiber (p : Polynomial k) (hp : p ≠ 0) (pool : Finset k) (hpool : pool.Nonempty) :
    (letI : Nonempty {x : k // x ∈ pool} := hpool.to_subtype
     letI := SampleableType.ofFintype {x : k // x ∈ pool}
     (Pr[fun x : {x : k // x ∈ pool} => p.eval x.val = 0 |
       ($ᵗ {x : k // x ∈ pool})]).toReal) ≤ p.natDegree / (pool.card : ℝ) := by
  classical
  rw [probEvent_uniformSample]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast guess_fiber_aux_card p hp pool)
    (by positivity)

lemma guess_allowance (dcoin dguess used : ℕ)
    (hdegree : dcoin + 3 ≤ Constants.eps_f_numerator)
    (hguess : dguess ≤ 2)
    (hused : used ≤ Constants.L + 3 * Constants.W_budget + 1) :
    (dcoin : ℝ) / ((P0.q : ℝ) - Constants.D) +
      (dguess : ℝ) / ((P0.q : ℝ) - used) ≤ (Constants.eps_f : ℝ) := by
  have hbase : 0 < (P0.q : ℝ) - Constants.D := by
    norm_num [P0, Params.main, Constants.q, Constants.D]
  have hslack : 2 * ((P0.q : ℝ) - Constants.D) ≤
      3 * ((P0.q : ℝ) - (Constants.L + 3 * Constants.W_budget + 1 : ℕ)) := by
    norm_num [P0, Params.main, Constants.q, Constants.D, Constants.L, Constants.W_budget]
  have hu : (used : ℝ) ≤ (Constants.L + 3 * Constants.W_budget + 1 : ℕ) := by
    exact_mod_cast hused
  have hpool : 0 < (P0.q : ℝ) - used := by linarith
  have hg : (dguess : ℝ) ≤ 2 := by exact_mod_cast hguess
  have hg_bound : (dguess : ℝ) / ((P0.q : ℝ) - used) ≤
      3 / ((P0.q : ℝ) - Constants.D) := by
    apply (div_le_div_iff₀ hpool hbase).mpr
    calc
      (dguess : ℝ) * ((P0.q : ℝ) - Constants.D) ≤
          2 * ((P0.q : ℝ) - Constants.D) := mul_le_mul_of_nonneg_right hg hbase.le
      _ ≤ 3 * ((P0.q : ℝ) - used) := by linarith
  have hd : (dcoin : ℝ) + 3 ≤ Constants.eps_f_numerator := by exact_mod_cast hdegree
  have heps : (Constants.eps_f : ℝ) =
      (Constants.eps_f_numerator : ℝ) / ((P0.q : ℝ) - Constants.D) := by
    norm_num [Constants.eps_f, Constants.eps_f_numerator, P0, Params.main,
      Constants.q, Constants.D]
  calc
    _ ≤ (dcoin : ℝ) / ((P0.q : ℝ) - Constants.D) +
        3 / ((P0.q : ℝ) - Constants.D) := add_le_add le_rfl hg_bound
    _ = ((dcoin : ℝ) + 3) / ((P0.q : ℝ) - Constants.D) := (add_div _ _ _).symm
    _ ≤ (Constants.eps_f_numerator : ℝ) / ((P0.q : ℝ) - Constants.D) :=
      div_le_div_of_nonneg_right hd hbase.le
    _ = _ := heps.symm

end Praxis.Proofs.GroupModel.Split
