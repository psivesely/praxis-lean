import Praxis.Proofs.Query.Marked
import Praxis.Proofs.KeyOracle
import Praxis.Semantics.Algorithms
import Praxis.Proofs.NamesReservoir
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Extractor
import Praxis.Games
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.QAP
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting

namespace Praxis.Proofs.Names

open OracleComp OracleSpec

open scoped ENNReal

variable {P : Params}

theorem idealKdf_guessName_iff (cx : IdealCtx P) (st : IdealState P)
    (hm : st.mark = none) (nm : ClassName P) :
    (idealKdf cx st nm).mark = some .guessName ↔
      nm = cx.target ∧ ∀ kl ∈ cx.keyLabels, st.dT kl.1 = none := by
  classical
  unfold idealKdf
  by_cases hn : nm = cx.target
  · simp only [hn, if_true, true_and]
    cases hf : cx.keyLabels.find? (fun kl => match st.dT kl.1 with
        | some E => decide (¬ cx.isKey (kl.2 • E))
        | none => false) with
    | some kl =>
      simp only [Option.some.injEq, reduceCtorEq, false_iff]
      intro ha
      have hp := List.find?_some hf
      rw [ha kl (List.mem_of_find?_eq_some hf)] at hp
      simp at hp
    | none =>
      simp only [List.any_eq_true, Option.isSome_iff_exists]
      split_ifs with ha
      · simp only [Option.some.injEq, reduceCtorEq, false_iff]
        intro hb
        obtain ⟨kl, hkl, E, hE⟩ := ha
        rw [hb kl hkl] at hE
        contradiction
      · simp only [true_iff]
        intro kl hkl
        cases he : st.dT kl.1 with
        | none => rfl
        | some E => exact False.elim (ha ⟨kl, hkl, E, he⟩)
  · simp [hn, hm]

theorem idealOp_not_guessName (cx : IdealCtx P) (st : IdealState P)
    (hm : st.mark ≠ some .guessName) (op : TrOp P) :
    (idealOp cx st op).mark ≠ some .guessName := by
  classical
  cases op with
  | lin s a b u v res =>
    cases s <;>
      simp only [idealOp, ideal1, ideal2, idealT, recordT] <;>
      split <;> (try split) <;> simp_all
  | pair u v res =>
    simp only [idealOp, idealT]
    split <;> (try split) <;> simp_all
  | name u res =>
    simp only [idealOp]
    split
    · exact hm
    · simp only [idealT]
      split <;> (try split) <;> simp_all

theorem idealInit_not_guessName (cx : IdealCtx P) (pv : PubView P) :
    (idealInit cx pv).mark ≠ some .guessName := by
  classical
  have h1 (es : List (Option (G1Idx P) × Label P)) (st : IdealState P)
      (hm : st.mark ≠ some .guessName) :
      (es.foldl (fun st e => match st.mark with
        | some _ => st
        | none => ideal1 cx .init st e.2 (Pi.single e.1 1)) st).mark ≠
        some .guessName := by
    induction es generalizing st with
    | nil => exact hm
    | cons e es ih =>
      apply ih
      cases hs : st.mark with
      | some k => simpa only [hs] using hm
      | none =>
        simp only [hs, ideal1]
        split <;> (try split) <;> simp_all
  have h2 (es : List (Option (G2Idx P) × Label P)) (st : IdealState P)
      (hm : st.mark ≠ some .guessName) :
      (es.foldl (fun st e => match st.mark with
        | some _ => st
        | none => ideal2 cx .init st e.2 (Pi.single e.1 1)) st).mark ≠
        some .guessName := by
    induction es generalizing st with
    | nil => exact hm
    | cons e es ih =>
      apply ih
      cases hs : st.mark with
      | some k => simpa only [hs] using hm
      | none =>
        simp only [hs, ideal2]
        split <;> (try split) <;> simp_all
  have ht (es : List (Option Unit × Label P)) (st : IdealState P)
      (hm : st.mark ≠ some .guessName) :
      (es.foldl (fun st e => match st.mark with
        | some _ => st
        | none => idealT cx true st e.2 (gtInit e.1)) st).mark ≠
        some .guessName := by
    induction es generalizing st with
    | nil => exact hm
    | cons e es ih =>
      apply ih
      cases hs : st.mark with
      | some k => simpa only [hs] using hm
      | none =>
        simp only [hs, idealT]
        split <;> (try split) <;> simp_all
  exact ht _ _ (h2 _ _ (h1 _ _ (by simp)))

theorem worldFull_event [Fact (Nat.Prime P.q)] [Nonempty (ZMod P.q ↪ Label P)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (m : Msg P) (A : Adversary P) (ext : ExtractorLaw P) (p : WorldOut P → Prop) :
    Pr[fun f => p f.w | worldFull pp m A ext] = Pr[p | worldRun pp m A] := by
  classical
  unfold worldFull
  rw [probEvent_bind_eq_tsum]
  have hk (w : WorldOut P) :
      Pr[fun f : FullOut P => p f.w | (do
        let ωp ← sampleAssigns pp 1
        let ω0 ← sampleAssigns pp 3
        let ω1 ← sampleAssigns pp 3
        let x ← ext pp.S w.out.pv w.st.tr
        pure (⟨w, ωp 0, ω0, ω1, x⟩ : FullOut P))] = if p w then 1 else 0 := by
    simp only [probEvent_bind_eq_tsum, probEvent_pure]
    by_cases hp : p w <;> simp [hp, tsum_probOutput_eq_sub]
  simp_rw [hk]
  simpa only [mul_ite, mul_one, mul_zero] using
    (probEvent_eq_tsum_ite (worldRun pp m A) p).symm

theorem idealT_dT_none_imp (cx : IdealCtx P) (initial : Bool) (st : IdealState P)
    (res l : Label P) (F : ExprT P) :
    (idealT cx initial st res F).dT l = none → st.dT l = none := by
  classical
  cases hr : st.dT res with
  | none =>
    simp only [idealT, hr, Function.update_apply]
    by_cases hl : l = res <;> simp [hl]
  | some E =>
    simp only [idealT, hr]
    split <;> exact id

theorem recordT_dT_none_imp (st : IdealState P) (u v l : Label P) :
    (recordT st u v).dT l = none → st.dT l = none := by
  classical
  simp only [recordT]
  split <;> simp_all

theorem idealOp_dT_none_imp (cx : IdealCtx P) (st : IdealState P)
    (op : TrOp P) (l : Label P) :
    (idealOp cx st op).dT l = none → st.dT l = none := by
  classical
  cases op with
  | lin s a b u v res =>
    cases s
    · simp only [idealOp, ideal1]
      split <;> (try split) <;> exact id
    · simp only [idealOp, ideal2]
      split <;> (try split) <;> exact id
    · intro h
      exact recordT_dT_none_imp st u v l
        (idealT_dT_none_imp cx false (recordT st u v) res l _ h)
  | pair u v res => exact idealT_dT_none_imp cx false st res l _
  | name u res =>
    simp only [idealOp]
    split
    · exact id
    · exact idealT_dT_none_imp cx false { st with named := Function.update st.named u true }
        (otherLabel u res) l _

theorem idealKdf_dT (cx : IdealCtx P) (st : IdealState P) (nm : ClassName P) :
    (idealKdf cx st nm).dT = st.dT := by
  classical
  unfold idealKdf
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem idealEvent_fold_dT_none_imp (cx : IdealCtx P) (es : List (MonEvent P))
    (st : IdealState P) (l : Label P) :
    (es.foldl (idealEvent cx) st).dT l = none → st.dT l = none := by
  classical
  induction es generalizing st with
  | nil => exact id
  | cons e es ih =>
    intro h
    have h' := ih (idealEvent cx st e) h
    cases hs : st.mark with
    | some k => simpa only [idealEvent, hs] using h'
    | none =>
      cases e with
      | op op => exact idealOp_dT_none_imp cx st op l (by simpa [idealEvent, hs] using h')
      | kdf nm => simpa only [idealEvent, hs, idealKdf_dT] using h'

theorem rho_interpolant [Fact (Nat.Prime P.q)] (pts : RowPoints P) :
    pts.interp (fun k => if k = rhoIndex then 1 else 0) =
      Lagrange.basis Finset.univ pts.point rhoIndex := by
  classical
  simp [RowPoints.interp, Lagrange.interpolate_apply]

theorem rho_interpolant_ne_zero [Fact (Nat.Prime P.q)] (pts : RowPoints P)
    (hd : Function.Injective pts.point) (x : Fq P) (hx : ∀ i, x ≠ pts.point i) :
    (pts.interp (fun k => if k = rhoIndex then 1 else 0)).eval x ≠ 0 := by
  classical
  rw [rho_interpolant]
  simp only [Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr
    (hd.ne (Ne.symm (Finset.mem_erase.mp hi).1)))) (sub_ne_zero.mpr (hx i))

set_option maxRecDepth 2000 in

theorem kappa_ne_zero (ch : AdmissibleChoice P0) (S : Relation P0)
    (c : Coins P0) (hc : ValidCoins (ppOf ch S).qap c) :
    kappa (ppOf ch S) c ≠ 0 := by
  classical
  have hpi : coin c .pi ≠ 0 := hc.2.1 .pi rfl
  have hbE : coin c .bE ≠ 0 := hc.2.1 .bE rfl
  have heps : coin c .eps ≠ -1 := by simpa [coin] using hc.2.2.2 (0 : Fin P0.K1)
  have h1 : 1 + coin c .eps ≠ 0 := by
    intro h
    apply heps
    linear_combination h
  have hg : gammaKey c ≠ 0 := by
    simpa [gammaKey, piAt, legScaleAt, thetaAt, LegKind.base, bOf] using
      mul_ne_zero (mul_ne_zero hpi h1) hbE
  have hL := rho_interpolant_ne_zero ch.1 ch.2.distinct (coin c .tau) (fun i => hc.1 i)
  unfold kappa
  apply mul_ne_zero hg
  dsimp only [ppOf, setup, domainMap, RowPoints.toQAP]
  exact hL

theorem kappa_ne_neg (ch : AdmissibleChoice P0) (S : Relation P0)
    (c : Coins P0) (hc : ValidCoins (ppOf ch S).qap c) :
    kappa (ppOf ch S) c ≠ -kappa (ppOf ch S) c := by
  have h2 : (2 : Fq P0) ≠ 0 := by decide
  intro h
  have hz : (2 : Fq P0) * kappa (ppOf ch S) c = 0 := by linear_combination h
  exact (mul_ne_zero h2 (kappa_ne_zero ch S c hc)) hz

theorem monEvents_append_kdf (tr : List (TrOp P)) (kl : List (ℕ × ClassName P))
    (nm : ClassName P) :
    monEvents tr (kl ++ [(tr.length, nm)]) = monEvents tr kl ++ [.kdf nm] := by
  have hp :
      (List.range tr.length).flatMap (fun k =>
        ((kl ++ [(tr.length, nm)]).filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          (tr[k]?).toList.map MonEvent.op) =
      (List.range tr.length).flatMap (fun k =>
        (kl.filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          (tr[k]?).toList.map MonEvent.op) := by
    apply List.flatMap_congr
    intro k hk
    have hk' := List.mem_range.mp hk
    simp [List.filter_append, show tr.length ≠ k by omega]
  unfold monEvents
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [hp]
  simp [List.filter_append, List.append_assoc]

theorem monEvents_append_op (tr : List (TrOp P)) (kl : List (ℕ × ClassName P))
    (op : TrOp P) (hkl : ∀ e ∈ kl, e.1 ≤ tr.length) :
    monEvents (tr ++ [op]) kl = monEvents tr kl ++ [.op op] := by
  have hp :
      (List.range tr.length).flatMap (fun k =>
        (kl.filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          ((tr ++ [op])[k]?).toList.map MonEvent.op) =
      (List.range tr.length).flatMap (fun k =>
        (kl.filter fun e => e.1 == k).map (fun e => MonEvent.kdf e.2) ++
          (tr[k]?).toList.map MonEvent.op) := by
    apply List.flatMap_congr
    intro k hk
    rw [List.getElem?_append_left (List.mem_range.mp hk)]
  have hf : (kl.filter fun e => e.1 == tr.length + 1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    have hh := hkl e he
    simp [show e.1 ≠ tr.length + 1 by omega]
  unfold monEvents
  simp only [List.length_append, List.length_singleton, List.range_succ,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hp, hf]
  simp [List.append_assoc]

theorem idealT_result (cx : IdealCtx P) (initial : Bool) (st : IdealState P)
    (res : Label P) (F : ExprT P) : (idealT cx initial st res F).dT res ≠ none := by
  classical
  cases hr : st.dT res with
  | none => simp [idealT, hr]
  | some E => simp only [idealT, hr]; split <;> simp [hr]

theorem idealOp_issuedGT (cx : IdealCtx P) (st : IdealState P)
    (op : TrOp P) (l : Label P) (h : op.issuedGT = some l) :
    (idealOp cx st op).dT l ≠ none := by
  cases op with
  | lin s a b u v res =>
    cases s <;> simp only [TrOp.issuedGT, reduceCtorEq, Option.some.injEq] at h
    subst l
    exact idealT_result cx false (recordT st u v) res _
  | pair u v res =>
    simp only [TrOp.issuedGT, Option.some.injEq] at h
    subst l
    exact idealT_result cx false st res _
  | name u nm => simp [TrOp.issuedGT] at h

theorem idealEvent_prev_mark_none (cx : IdealCtx P) (st : IdealState P) (e : MonEvent P)
    (h : (idealEvent cx st e).mark = none) : st.mark = none := by
  cases hs : st.mark with
  | none => rfl
  | some k => simp [idealEvent, hs] at h

noncomputable def initTFold (cx : IdealCtx P) (es : List (Option Unit × Label P)) (st : IdealState P) :
    IdealState P := es.foldl (fun st e => match st.mark with
      | some _ => st
      | none => idealT cx true st e.2 (gtInit e.1)) st

theorem initTFold_of_mark (cx : IdealCtx P) (es : List (Option Unit × Label P)) (st : IdealState P)
    (h : st.mark ≠ none) : initTFold cx es st = st := by
  cases hs : st.mark with
  | none => exact False.elim (h hs)
  | some k =>
    induction es with
    | nil => rfl
    | cons e es ih => simpa [initTFold, List.foldl_cons, hs] using ih

theorem initTFold_dT_none_imp (cx : IdealCtx P) (es : List (Option Unit × Label P))
    (st : IdealState P) (l : Label P) :
    (initTFold cx es st).dT l = none → st.dT l = none := by
  induction es generalizing st with
  | nil => exact id
  | cons e es ih =>
    intro h
    cases hs : st.mark with
    | some k =>
      rw [initTFold_of_mark cx (e :: es) st (by simp [hs])] at h
      exact h
    | none =>
      have hh := ih (idealT cx true st e.2 (gtInit e.1)) (by simpa [initTFold, hs] using h)
      exact idealT_dT_none_imp cx true st e.2 l _ hh

theorem initTFold_mem (cx : IdealCtx P) (es : List (Option Unit × Label P))
    (st : IdealState P) (hm : (initTFold cx es st).mark = none)
    (e : Option Unit × Label P) (he : e ∈ es) :
    (initTFold cx es st).dT e.2 ≠ none := by
  induction es generalizing st with
  | nil => simp at he
  | cons f es ih =>
    have hs : st.mark = none := by
      by_contra hn
      rw [initTFold_of_mark cx (f :: es) st hn] at hm
      exact hn hm
    rcases List.mem_cons.mp he with he | he
    · subst e
      have hd := idealT_result cx true st f.2 (gtInit f.1)
      intro hz
      apply hd
      apply initTFold_dT_none_imp cx es _ f.2
      simpa [initTFold, hs] using hz
    · have hh := ih (idealT cx true st f.2 (gtInit f.1)) (by simpa [initTFold, hs] using hm) he
      simpa [initTFold, hs] using hh

theorem idealInit_gt_has (cx : IdealCtx P) (pv : PubView P)
    (hm : (idealInit cx pv).mark = none) (e : Option Unit × Label P) (he : e ∈ pv.gT) :
    (idealInit cx pv).dT e.2 ≠ none :=
  initTFold_mem cx pv.gT _ hm e he

def observerBudget (Q QH : ℕ) : ℕ := 3*Q + 2*QH + 2

theorem observerBudget_reserve (Q QH : ℕ) (hQ : Q < Constants.T) (hH : QH ≤ Constants.T) :
    observerBudget Q QH + Constants.N_free ≤ Fintype.card (Label P0) := by
  simp only [Label, Fintype.card_bitVec]
  norm_num [observerBudget, Params.main, Constants.label_bits, Constants.N_free, Constants.T] at *
  omega

theorem observerBudget_ledger (Q QH : ℕ) (hQ : Q < Constants.T) (hH : QH ≤ Constants.T) :
    (((observerBudget Q QH : ℕ) : ℝ≥0∞)^2 * (Constants.N_free : ℝ≥0∞)⁻¹^2).toReal ≤
      (ledgerName : ℝ) := by
  have hb : observerBudget Q QH ≤ 5*Constants.T + 2 := by unfold observerBudget; omega
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast]
  calc
    _ ≤ ((5*Constants.T+2 : ℕ) : ℝ)^2 * (Constants.N_free : ℝ)⁻¹^2 := by
      gcongr
    _ ≤ _ := by norm_num [ledgerName, Constants.T, Constants.N_free]

end Praxis.Proofs.Names
