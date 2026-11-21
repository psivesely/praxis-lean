import Praxis.Proofs.GroupModel.Split.Lazy.CouplingCount
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.Coupling
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingInitial
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Published
import Praxis.Reduction
import Praxis.Encryption.GroupModel

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option maxHeartbeats 500000

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

variable (pp : PublicParams P0)

lemma bind_point {α β : Type} (oa : ProbComp α) (f : α → ProbComp β) (a : α) (b : β) :
    Pr[= a | oa] * Pr[= b | f a] ≤ Pr[= b | oa >>= f] := by
  rw [probOutput_bind_eq_tsum]
  exact ENNReal.le_tsum a

lemma map_point {α β : Type} (oa : ProbComp α) (f : α → β) (a : α) :
    Pr[= a | oa] ≤ Pr[= f a | f <$> oa] := by
  rw [probOutput_map]
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_mono
  intro b _ hb
  exact congrArg f hb

lemma cons_insert (st : State pp) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp)
    (hc : (insertResult pp st s l P).first = none) :
    cons pp (insertResult pp st s l P) [] c x =
      (cons pp st [] c x).filter (fun σ => σ s (valueAt pp [] c x P) = l) := by
  cases hd : st.dict s l with
  | none =>
    rw [insertResult_of_none pp st s P l hd]
    exact cons_record pp st [] c x s l P st.guesses hd
  | some Q =>
    have hPQ := insertResult_eq_of_no_collision pp st s l P Q hd hc
    subst Q
    rw [insertResult_of_same pp st s P l hd]
    symm
    apply Finset.filter_eq_self.mpr
    intro σ hσ
    exact (mem_cons_iff pp st [] c x σ).mp hσ |>.1 s l P hd

lemma cons_insert_mem (st : State pp) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (P : Poly pp) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp st [] c x)
    (hc : (insertResult pp st s (σ s (valueAt pp [] c x P)) P).first = none) :
    σ ∈ cons pp (insertResult pp st s (σ s (valueAt pp [] c x P)) P) [] c x := by
  rw [cons_insert pp st c x s _ P hc, Finset.mem_filter]
  exact ⟨hσ, rfl⟩

lemma insert_count (st : State pp) (c : CoinDomain pp) (x : ℕ → k)
    (s : GroupModel.Sorted.PSort) (P : Poly pp) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp st [] c x)
    (hc : (insertResult pp st s (σ s (valueAt pp [] c x P)) P).first = none) :
    ((cons pp (insertResult pp st s (σ s (valueAt pp [] c x P)) P) [] c x).card : ℝ≥0∞) =
      (cons pp st [] c x).card *
        Pr[= (σ s (valueAt pp [] c x P),
          insertResult pp st s (σ s (valueAt pp [] c x P)) P) |
          (referenceInsert pp s P).run st] := by
  let v := valueAt pp [] c x P
  let l := σ s v
  have hσd := (mem_cons_iff pp st [] c x σ).mp hσ
  cases hfind : labelOf pp st s P with
  | some l' =>
    have hd := labelOf_some pp st s P l' hfind
    have hl : l' = l := (hσd.1 s l' P hd).symm
    subst l'
    have hs : insertResult pp st s l P = st := insertResult_of_same pp st s P l hd
    change ((cons pp (insertResult pp st s l P) [] c x).card : ℝ≥0∞) =
      (cons pp st [] c x).card * Pr[= (l, insertResult pp st s l P) | (referenceInsert pp s P).run st]
    simp only [hs, referenceInsert, StateT.run_bind, StateT.run_get, pure_bind, hfind,
      StateT.run_pure, probOutput_pure_self, mul_one]
  | none =>
    have hv : v ∉ valuesOf pp st [] c x s := by
      intro hv
      simp only [valuesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨l', Q, hQ, hv⟩ := hv
      have hl : l' = l := by simpa [l, ← hv] using (hσd.1 s l' Q hQ).symm
      subst l'
      have hPQ := insertResult_eq_of_no_collision pp st s l P Q hQ hc
      subst Q
      exact labelOf_none pp st s P hfind l hQ
    have hl := label_available pp st [] c x s v hv σ hσ
    have hd := not_mem_assigned pp st s l hl
    have hs := insertResult_of_none pp st s P l hd
    have hcard := card_cons_eq pp st [] c x s v hv l hl
    have hcons := cons_insert pp st c x s l P hc
    have hprob : Pr[= (l, insertResult pp st s l P) | (referenceInsert pp s P).run st] =
        ((available pp st s).card : ℝ≥0∞)⁻¹ := by
      simp only [referenceInsert, StateT.run_bind, StateT.run_get, pure_bind, hfind,
        StateT.run_lift, StateT.run_set, StateT.run_pure, StateT.run_map, bind_assoc, pure_bind, bind_pure_comp, bind_map_left, map_pure, Functor.map_map]
      change Pr[= (l, insertResult pp st s l P) |
        (fun a => (a, {st with dict := record pp st.dict s a P})) <$>
          uniform (available pp st s)] = _
      rw [hs, probOutput_map_injective _ (by intro a b h; exact congrArg Prod.fst h) l]
      exact (uniform_mass _ ⟨l, hl⟩ l).trans (if_pos hl)
    change ((cons pp (insertResult pp st s l P) [] c x).card : ℝ≥0∞) = _
    rw [hprob, hcons]
    have hcast : ((cons pp st [] c x).card : ℝ≥0∞) =
        (available pp st s).card *
          ((cons pp st [] c x).filter fun τ => τ s v = l).card := by
      exact_mod_cast hcard
    rw [hcast]
    have hA : ((available pp st s).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨l, hl⟩).ne'
    rw [mul_comm (Nat.cast _) (Nat.cast _), mul_assoc,
      ENNReal.mul_inv_cancel hA (ENNReal.natCast_ne_top _), mul_one]

lemma fold_first (es : List (GroupModel.Sorted.PSort × Poly pp)) (st : State pp)
    (labelFor : GroupModel.Sorted.PSort → Poly pp → Label P0)
    (hc : (es.foldl (fun st e => insertResult pp st e.1 (labelFor e.1 e.2) e.2) st).first = none) :
    st.first = none := by
  induction es generalizing st with
  | nil => exact hc
  | cons e es ih =>
    exact (insertResult_props pp st e.1 (labelFor e.1 e.2) e.2).2.2.2.2 (ih _ hc)

lemma labels_count (es : List (GroupModel.Sorted.PSort × Poly pp))
    (st : State pp) (c : CoinDomain pp) (x : ℕ → k) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp st [] c x)
    (hc : (es.foldl (fun st e =>
      insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2) st).first = none) :
    ((cons pp (es.foldl (fun st e =>
      insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2) st) [] c x).card : ℝ≥0∞) ≤
      (cons pp st [] c x).card *
        Pr[= (es.map (fun e => σ e.1 (valueAt pp [] c x e.2)),
          es.foldl (fun st e =>
            insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2) st) |
          (es.mapM fun e => referenceInsert pp e.1 e.2).run st] := by
  induction es generalizing st with
  | nil => simp
  | cons e es ih =>
    let l := σ e.1 (valueAt pp [] c x e.2)
    let st' := insertResult pp st e.1 l e.2
    have hfirst : st'.first = none := fold_first pp es st'
      (fun s P => σ s (valueAt pp [] c x P)) hc
    have hσ' := cons_insert_mem pp st c x e.1 e.2 σ hσ hfirst
    have hi := ih st' hσ' hc
    have hct := insert_count pp st c x e.1 e.2 σ hσ hfirst
    let ls := es.map (fun e => σ e.1 (valueAt pp [] c x e.2))
    let fin := es.foldl (fun st e =>
      insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2) st'
    have hprob : Pr[= (l, st') | (referenceInsert pp e.1 e.2).run st] *
        Pr[= (ls, fin) | (es.mapM fun e => referenceInsert pp e.1 e.2).run st'] ≤
        Pr[= (l :: ls, fin) |
          ((e :: es).mapM fun e => referenceInsert pp e.1 e.2).run st] := by
      simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, bind_pure_comp]
      rw [probOutput_bind_eq_tsum]
      apply le_trans _ (ENNReal.le_tsum (a := (l, st')))
      apply mul_le_mul_right
      simpa only [StateT.run_map] using map_point
        ((es.mapM fun e => referenceInsert pp e.1 e.2).run st')
        (fun b : List (Label P0) × State pp => (l :: b.1, b.2)) (ls, fin)
    change ((cons pp fin [] c x).card : ℝ≥0∞) ≤ (cons pp st [] c x).card * _
    calc
      _ ≤ (cons pp st' [] c x).card *
          Pr[= (ls, fin) | (es.mapM fun e => referenceInsert pp e.1 e.2).run st'] := hi
      _ = (cons pp st [] c x).card *
          (Pr[= (l, st') | (referenceInsert pp e.1 e.2).run st] *
          Pr[= (ls, fin) | (es.mapM fun e => referenceInsert pp e.1 e.2).run st']) := by
        rw [hct]; ring
      _ ≤ _ := mul_le_mul_right hprob _

lemma mapM_key {α β : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (is : List α) (f : α → M β) :
    (is.mapM fun i => do let a ← f i; pure (i, a)) =
      (fun ls => is.zip ls) <$> is.mapM f := by
  induction is with
  | nil => simp
  | cons i is ih =>
    rw [List.mapM_cons, List.mapM_cons, ih]
    simp only [map_bind, bind_map_left, bind_pure_comp, Functor.map_map, List.zip_cons_cons]

lemma table_count {α : Type} (is : List α) (s : GroupModel.Sorted.PSort)
    (P : α → Poly pp) (st : State pp) (c : CoinDomain pp) (x : ℕ → k)
    (σ : LabelEncoding P0) (hσ : σ ∈ cons pp st [] c x)
    (hc : (is.foldl (fun st i => insertResult pp st s (σ s (valueAt pp [] c x (P i)))
      (P i)) st).first = none) :
    ((cons pp (is.foldl (fun st i => insertResult pp st s
      (σ s (valueAt pp [] c x (P i))) (P i)) st) [] c x).card : ℝ≥0∞) ≤
      (cons pp st [] c x).card *
        Pr[= (is.map (fun i => (i, σ s (valueAt pp [] c x (P i)))),
          is.foldl (fun st i => insertResult pp st s (σ s (valueAt pp [] c x (P i)))
            (P i)) st) |
          (is.mapM fun i => do let l ← referenceInsert pp s (P i); pure (i, l)).run st] := by
  have h := labels_count pp (is.map fun i => (s, P i)) st c x σ hσ
    (by simpa only [List.foldl_map] using hc)
  simp only [List.foldl_map, List.map_map, List.mapM_map, Function.comp_def] at h
  apply h.trans
  apply mul_le_mul_right
  rw [mapM_key, StateT.run_map]
  have hz : ∀ (is : List α),
      is.zip (is.map (fun i => σ s (valueAt pp [] c x (P i)))) =
        is.map (fun i => (i, σ s (valueAt pp [] c x (P i)))) := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons, List.zip_cons_cons, ih]
  simpa only [hz] using map_point
    ((is.mapM fun i => referenceInsert pp s (P i)).run st)
    (fun z => (is.zip z.1, z.2))
    (is.map (fun i => σ s (valueAt pp [] c x (P i))),
      is.foldl (fun st i => insertResult pp st s (σ s (valueAt pp [] c x (P i))) (P i)) st)

lemma fold_mem (es : List (GroupModel.Sorted.PSort × Poly pp)) (st : State pp)
    (c : CoinDomain pp) (x : ℕ → k) (σ : LabelEncoding P0)
    (hσ : σ ∈ cons pp st [] c x)
    (hc : (es.foldl (fun st e =>
      insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2) st).first = none) :
    σ ∈ cons pp (es.foldl (fun st e =>
      insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2) st) [] c x := by
  induction es generalizing st with
  | nil => exact hσ
  | cons e es ih =>
    apply ih
    · apply cons_insert_mem pp st c x e.1 e.2 σ hσ
      exact fold_first pp es _ (fun s P => σ s (valueAt pp [] c x P)) hc
    · exact hc

lemma fold_guesses (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp) :
    (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).guesses = st.guesses := by
  induction es generalizing st with
  | nil => rfl
  | cons e es ih => exact (ih _).trans (insertResult_props pp st e.1 e.2.1 e.2.2).1

lemma fold_excluded (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp) :
    (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).excluded = st.excluded := by
  induction es generalizing st with
  | nil => rfl
  | cons e es ih => exact (ih _).trans (insertResult_props pp st e.1 e.2.1 e.2.2).2.1

lemma fold_vars (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp)
    (h0 : ∀ s l P, st.dict s l = some P → P.vars = ∅)
    (h : ∀ e ∈ es, e.2.2.vars = ∅) :
    ∀ s l P, (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).dict s l = some P →
      P.vars = ∅ := by
  induction es generalizing st with
  | nil => exact h0
  | cons e es ih =>
    apply ih
    · intro s l P hP
      rcases (insertResult_props pp st e.1 e.2.1 e.2.2).2.2.2.1 s l P hP with hP | ⟨_, rfl⟩
      · exact h0 s l P hP
      · exact h e (by simp)
    · exact fun e' he => h e' (by simp [he])

lemma initialise_vars (A : FormMatrix P0) (pv : PubView P0) :
    ∀ s l P, (initialise pp A pv).dict s l = some P → P.vars = ∅ := by
  apply fold_vars
  · simp [empty]
  · simp only [initialEntries, List.mem_append, List.mem_map]
    rintro _ ((⟨e, _, rfl⟩ | ⟨e, _, rfl⟩) | ⟨e, _, rfl⟩) <;>
      simp [base1, base2, baseT]

lemma initialise_excluded (A : FormMatrix P0) (pv : PubView P0) :
    (initialise pp A pv).excluded = fun _ => ∅ :=
  fold_excluded pp (initialEntries pp A pv) (empty pp)

lemma initialise_guesses (A : FormMatrix P0) (pv : PubView P0) :
    (initialise pp A pv).guesses = ∅ :=
  fold_guesses pp (initialEntries pp A pv) (empty pp)

lemma initialise_not_excluded (A : FormMatrix P0) (pv : PubView P0)
    (s : GroupModel.Sorted.PSort) (l : Label P0) : l ∉ (initialise pp A pv).excluded s := by
  rw [initialise_excluded pp A pv]
  exact Finset.notMem_empty l

attribute [local irreducible] initialise

lemma initialise_cons (A : FormMatrix P0) (c : CoinDomain pp) (x : ℕ → k)
    (σ : LabelEncoding P0) :
    σ ∈ cons pp (initialise pp A (pubView σ pp (formVec A) c.val)) [] c x := by
  rw [mem_cons_iff]
  refine ⟨?_, ?_⟩
  · intro s l P hP
    have hv := initialise_vars pp A (pubView σ pp (formVec A) c.val) s l P hP
    have he : valueAt pp [] c x P = evaluate pp σ c P :=
      valueAt_eq_evaluate pp [] c x σ P
        (fun v hvv => False.elim (Finset.notMem_empty v (hv ▸ hvv)))
    exact (congrArg (σ s) he).trans ((initialise_sound pp σ c A).1 s l P hP)
  · intro s l hl v
    exact False.elim (initialise_not_excluded pp A (pubView σ pp (formVec A) c.val) s l hl)

@[simp] lemma valueAt_base1 (c : CoinDomain pp) (x : ℕ → k) (E : Expr1 P0) :
    valueAt pp [] c x (base1 pp E) = val1 pp (Assign.ofCoins c.val) E := by
  simp [valueAt, base1, atCoin]

@[simp] lemma valueAt_base2 (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (E : Expr2 P0) : valueAt pp [] c x (base2 pp A E) =
      val2 pp (formVec A) (Assign.ofCoins c.val) E := by
  simp [valueAt, base2, atCoin]

@[simp] lemma valueAt_baseT (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (E : ExprT P0) : valueAt pp [] c x (baseT pp A E) =
      valT pp (formVec A) (Assign.ofCoins c.val) E := by
  simp [valueAt, baseT, atCoin]

lemma real_table1 (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (σ : LabelEncoding P0) :
    (keys1 P0).map (fun i => (i, σ .g₁ (valueAt pp [] c x (base1 pp (Pi.single i 1))))) =
      (pubView σ pp (formVec A) c.val).g1 := by
  simp [valueAt_base1, Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic.val1_single, keys1, pubView, e1At, Assign.ofCoins]

lemma real_table2 (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (σ : LabelEncoding P0) :
    (keys2 P0).map (fun i => (i, σ .g₂ (valueAt pp [] c x (base2 pp A (Pi.single i 1))))) =
      (pubView σ pp (formVec A) c.val).g2 := by
  simp [valueAt_base2, Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic.val2_single, e2At_real, keys2, pubView]

lemma real_tableT (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (σ : LabelEncoding P0) :
    ([none, some ()] : List (Option Unit)).map
      (fun i => (i, σ .gₜ (valueAt pp [] c x (baseT pp A (gtInit i))))) =
      (pubView σ pp (formVec A) c.val).gT := by
  simp [valueAt_baseT, valT_gtInit, pubView, Assign.ofCoins]

def initialPolys (A : FormMatrix P0) : List (GroupModel.Sorted.PSort × Poly pp) :=
  (keys1 P0).map (fun i => (.g₁, base1 pp (Pi.single i 1))) ++
  (keys2 P0).map (fun i => (.g₂, base2 pp A (Pi.single i 1))) ++
  ([none, some ()] : List (Option Unit)).map (fun i => (.gₜ, baseT pp A (gtInit i)))

lemma initial_entries (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (σ : LabelEncoding P0) :
    initialEntries pp A (pubView σ pp (formVec A) c.val) =
      (initialPolys pp A).map (fun e => (e.1, σ e.1 (valueAt pp [] c x e.2), e.2)) := by
  rw [initialEntries, ← real_table1 pp c x A σ, ← real_table2 pp c x A σ,
    ← real_tableT pp c x A σ]
  simp only [initialPolys, List.map_append, List.map_map]
  rfl

lemma initialise_fold (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (σ : LabelEncoding P0) :
    initialise pp A (pubView σ pp (formVec A) c.val) =
      (initialPolys pp A).foldl (fun st e =>
        insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2) (empty pp) := by
  rw [initialise, initial_entries pp c x A σ, List.foldl_map]

section InitialCount

attribute [local irreducible] keys1 keys2 g1Order g2Order List.mapM referenceInsert List.foldl insertResult

lemma tables_count {α β γ δ : Type} (is1 : List α) (is2 : List β) (is3 : List γ)
    (P1 : α → Poly pp) (P2 : β → Poly pp) (P3 : γ → Poly pp)
    (build : List (α × Label P0) → List (β × Label P0) → List (γ × Label P0) → δ)
    (c : CoinDomain pp) (x : ℕ → k) (σ : LabelEncoding P0)
    (hc : (((is1.map fun i => (GroupModel.Sorted.PSort.g₁, P1 i)) ++ (is2.map fun i => (GroupModel.Sorted.PSort.g₂, P2 i)) ++
        (is3.map fun i => (GroupModel.Sorted.PSort.gₜ, P3 i))).foldl
      (fun st e => insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2)
        (empty pp)).first = none) :
    let f : State pp → GroupModel.Sorted.PSort × Poly pp → State pp :=
      fun st e => insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2
    let fin := (((is1.map fun i => (GroupModel.Sorted.PSort.g₁, P1 i)) ++ (is2.map fun i => (GroupModel.Sorted.PSort.g₂, P2 i)) ++
        (is3.map fun i => (GroupModel.Sorted.PSort.gₜ, P3 i))).foldl f (empty pp))
    ((cons pp fin [] c x).card : ℝ≥0∞) ≤ Fintype.card (LabelEncoding P0) *
      Pr[= (build (is1.map fun i => (i, σ .g₁ (valueAt pp [] c x (P1 i))))
          (is2.map fun i => (i, σ .g₂ (valueAt pp [] c x (P2 i))))
          (is3.map fun i => (i, σ .gₜ (valueAt pp [] c x (P3 i)))), fin) |
        (do
          let a ← is1.mapM fun i => do let l ← referenceInsert pp .g₁ (P1 i); pure (i,l)
          let b ← is2.mapM fun i => do let l ← referenceInsert pp .g₂ (P2 i); pure (i,l)
          let d ← is3.mapM fun i => do let l ← referenceInsert pp .gₜ (P3 i); pure (i,l)
          pure (build a b d)).run (empty pp)] := by
  dsimp only
  let f : State pp → GroupModel.Sorted.PSort × Poly pp → State pp :=
    fun st e => insertResult pp st e.1 (σ e.1 (valueAt pp [] c x e.2)) e.2
  let es1 := is1.map fun i => (GroupModel.Sorted.PSort.g₁, P1 i)
  let es2 := is2.map fun i => (GroupModel.Sorted.PSort.g₂, P2 i)
  let es3 := is3.map fun i => (GroupModel.Sorted.PSort.gₜ, P3 i)
  let st1 := es1.foldl f (empty pp)
  let st2 := es2.foldl f st1
  let st3 := es3.foldl f st2
  let a := is1.map fun i => (i, σ .g₁ (valueAt pp [] c x (P1 i)))
  let b := is2.map fun i => (i, σ .g₂ (valueAt pp [] c x (P2 i)))
  let d := is3.map fun i => (i, σ .gₜ (valueAt pp [] c x (P3 i)))
  have hc3 : st3.first = none := by simpa only [List.foldl_append] using hc
  have hc2 : st2.first = none := fold_first pp es3 st2 (fun s P => σ s (valueAt pp [] c x P)) hc3
  have hc1 : st1.first = none := fold_first pp es2 st1 (fun s P => σ s (valueAt pp [] c x P)) hc2
  have hσ0 : σ ∈ cons pp (empty pp) [] c x := by simp [mem_cons_iff, empty]
  have hσ1 : σ ∈ cons pp st1 [] c x := fold_mem pp es1 _ c x σ hσ0 hc1
  have hσ2 : σ ∈ cons pp st2 [] c x := fold_mem pp es2 _ c x σ hσ1 hc2
  let p1 := is1.mapM fun i => do let l ← referenceInsert pp .g₁ (P1 i); pure (i,l)
  let p2 := is2.mapM fun i => do let l ← referenceInsert pp .g₂ (P2 i); pure (i,l)
  let p3 := is3.mapM fun i => do let l ← referenceInsert pp .gₜ (P3 i); pure (i,l)
  have h1 : ((cons pp st1 [] c x).card : ℝ≥0∞) ≤
      (cons pp (empty pp) [] c x).card * Pr[= (a, st1) | p1.run (empty pp)] := by
    simpa only [st1, es1, f, List.foldl_map] using
      table_count pp is1 .g₁ P1 (empty pp) c x σ hσ0
        (by simpa only [st1, es1, f, List.foldl_map] using hc1)
  have h2 : ((cons pp st2 [] c x).card : ℝ≥0∞) ≤
      (cons pp st1 [] c x).card * Pr[= (b, st2) | p2.run st1] := by
    simpa only [st2, es2, f, List.foldl_map] using
      table_count pp is2 .g₂ P2 st1 c x σ hσ1
        (by simpa only [st2, es2, f, List.foldl_map] using hc2)
  have h3 : ((cons pp st3 [] c x).card : ℝ≥0∞) ≤
      (cons pp st2 [] c x).card * Pr[= (d, st3) | p3.run st2] := by
    simpa only [st3, es3, f, List.foldl_map] using
      table_count pp is3 .gₜ P3 st2 c x σ hσ2
        (by simpa only [st3, es3, f, List.foldl_map] using hc3)
  have h0 : cons pp (empty pp) [] c x = Finset.univ := by
    ext τ; simp [mem_cons_iff, empty]
  have hp : Pr[= (a, st1) | p1.run (empty pp)] *
      (Pr[= (b, st2) | p2.run st1] * Pr[= (d, st3) | p3.run st2]) ≤
      Pr[= (build a b d, st3) | (do
        let a ← p1; let b ← p2; let d ← p3; pure (build a b d)).run (empty pp)] := by
    simp only [StateT.run_bind, StateT.run_pure]
    apply le_trans _ (bind_point _ _ (a, st1) (build a b d, st3))
    apply mul_le_mul_right
    apply le_trans _ (bind_point _ _ (b, st2) (build a b d, st3))
    apply mul_le_mul_right
    simp only [bind_pure_comp]
    exact map_point (p3.run st2) (fun z => (build a b z.1, z.2)) (d, st3)
  change ((cons pp ((es1 ++ es2 ++ es3).foldl f (empty pp)) [] c x).card : ℝ≥0∞) ≤ _
  simp only [List.foldl_append]
  calc
    _ ≤ (cons pp st2 [] c x).card * Pr[= (d, st3) | p3.run st2] := h3
    _ ≤ ((cons pp (empty pp) [] c x).card * Pr[= (a, st1) | p1.run (empty pp)]) *
        Pr[= (b, st2) | p2.run st1] * Pr[= (d, st3) | p3.run st2] :=
      mul_le_mul_left (le_trans h2 (mul_le_mul_left h1 _)) _
    _ = Fintype.card (LabelEncoding P0) *
        (Pr[= (a, st1) | p1.run (empty pp)] *
          (Pr[= (b, st2) | p2.run st1] * Pr[= (d, st3) | p3.run st2])) := by
      rw [h0, Finset.card_univ]; ring
    _ ≤ _ := mul_le_mul_right hp _

lemma initial_count (c : CoinDomain pp) (x : ℕ → k) (A : FormMatrix P0)
    (σ : LabelEncoding P0)
    (hc : (initialise pp A (pubView σ pp (formVec A) c.val)).first = none) :
    ((cons pp (initialise pp A (pubView σ pp (formVec A) c.val)) [] c x).card : ℝ≥0∞) ≤
      Fintype.card (LabelEncoding P0) *
        Pr[= (pubView σ pp (formVec A) c.val,
          initialise pp A (pubView σ pp (formVec A) c.val)) |
          (referenceInitial pp A).run (empty pp)] := by
  have hi := tables_count pp (keys1 P0) (keys2 P0) ([none, some ()] : List (Option Unit))
    (fun i => base1 pp (Pi.single i 1)) (fun i => base2 pp A (Pi.single i 1))
    (fun i => baseT pp A (gtInit i)) (@PubView.mk P0) c x σ
    (by simpa only [initialise_fold pp c x A σ, initialPolys] using hc)
  dsimp only at hi
  rw [initialise_fold pp c x A σ]
  simpa only [initialPolys, real_table1 pp c x A σ, real_table2 pp c x A σ,
    real_tableT pp c x A σ, referenceInitial] using hi

end InitialCount

lemma fold_dict (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp)
    (s : GroupModel.Sorted.PSort) (l : Label P0) (P : Poly pp) (hP : st.dict s l = some P) :
    (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).dict s l = some P := by
  induction es generalizing st with
  | nil => exact hP
  | cons e es ih => exact ih _ ((insertResult_props pp st e.1 e.2.1 e.2.2).2.2.1 s l P hP)

lemma fold_entry (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp)
    (hc : (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).first = none) :
    ∀ e ∈ es, (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).dict e.1 e.2.1 =
      some e.2.2 := by
  induction es generalizing st with
  | nil => simp
  | cons e es ih =>
    have hc' : (insertResult pp st e.1 e.2.1 e.2.2).first = none := by
      have hback : ∀ (es : List (GroupModel.Sorted.PSort × Label P0 × Poly pp)) (st : State pp),
          (es.foldl (fun st e => insertResult pp st e.1 e.2.1 e.2.2) st).first = none →
          st.first = none := by
        intro es
        induction es with
        | nil => exact fun _ h => h
        | cons e es ih =>
          intro st h
          exact (insertResult_props pp st e.1 e.2.1 e.2.2).2.2.2.2 (ih _ h)
      exact hback es _ hc
    intro e' he'
    rcases List.mem_cons.mp he' with heq | he'
    · subst e'
      apply fold_dict pp es (insertResult pp st e.1 e.2.1 e.2.2) e.1 e.2.1 e.2.2
      cases hd : st.dict e.1 e.2.1 with
      | none => simp [insertResult, hd, record_same]
      | some P =>
        have h := insertResult_eq_of_no_collision pp st e.1 e.2.1 e.2.2 P hd hc'
        have hd' : st.dict e.1 e.2.1 = some e.2.2 := by simpa only [h] using hd
        rw [insertResult_of_same pp st e.1 e.2.2 e.2.1 hd']
        exact hd'
    · exact ih _ hc e' he'

lemma initial_inv (A : FormMatrix P0) (pv : PubView P0) (st : OracleState P0)
    (hc : (initialise pp A pv).first = none) :
    Inv pp (⟨{st with issuedT := (pv.gT.map Prod.snd).toFinset},
      initialise pp A pv, [], []⟩ : GenState pp) := by
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · simp [OrdInv]
  · intro l hl
    simp only [List.mem_toFinset, List.mem_map] at hl
    obtain ⟨e, he, rfl⟩ := hl
    have hd := fold_entry pp (initialEntries pp A pv) (empty pp) (by simpa only [initialise] using hc)
      (.gₜ, e.2, baseT pp A (gtInit e.1)) (by
        simp only [initialEntries, List.mem_append, List.mem_map]
        exact Or.inr ⟨e, he, rfl⟩)
    change ((initialise pp A pv).dict .gₜ e.2).isSome
    exact Option.isSome_iff_exists.mpr ⟨_, (by simpa only [initialise] using hd)⟩
  · intro s l P hP v hv
    have h := initialise_vars pp A pv s l P hP
    rw [h] at hv
    exact False.elim (Finset.notMem_empty _ hv)
  · have hg : (initialise pp A pv).guesses = ∅ := initialise_guesses pp A pv
    simp [OrdGuess, hg]

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init
