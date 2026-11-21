import Praxis.Proofs.Basic
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec Praxis.Algebra

variable {q : ℕ} {P : Params}

@[simp] theorem run_pure {α : Type} (x : α) :
    runUnits (pure x : UnitComp q α) = pure x := rfl

@[simp] theorem run_bind {α β : Type} (c : UnitComp q α) (f : α → UnitComp q β) :
    runUnits (c >>= f) = runUnits c >>= fun x => runUnits (f x) :=
  simulateQ_bind _ _ _

@[simp] theorem run_map {α β : Type} (f : α → β) (c : UnitComp q α) :
    runUnits (f <$> c) = f <$> runUnits c := by
  exact simulateQ_map _ c f

@[simp] theorem run_fstep (s : FieldStep q) : runUnits (fstep s) = pure (fieldStepAnswer s) := by
  unfold runUnits fstep
  rw [simulateQ_spec_query]
  rfl

@[simp] theorem run_fadd (a b : ZMod q) : runUnits (fadd a b) = pure (a + b) := run_fstep _

@[simp] theorem run_fsub (a b : ZMod q) : runUnits (fsub a b) = pure (a - b) := run_fstep _

@[simp] theorem run_fmul (a b : ZMod q) : runUnits (fmul a b) = pure (a * b) := run_fstep _

@[simp] theorem run_fneg (a : ZMod q) : runUnits (fneg a) = pure (-a) := run_fstep _

@[simp] theorem run_finv (a : ZMod q) : runUnits (finv a) = pure a⁻¹ := run_fstep _

@[simp] theorem run_feq (a b : ZMod q) : runUnits (feq a b) = pure (decide (a = b)) := run_fstep _

@[simp] theorem run_fwrite (a : ZMod q) : runUnits (fwrite a) = pure a := run_fstep _

@[simp] theorem run_charge (c : Charge) : runUnits (charge c : UnitComp q Unit) = pure () := by
  unfold runUnits charge
  rw [simulateQ_spec_query]
  rfl

@[simp] theorem run_lookup {α : Type} (t : Label P → Option α) (l : Label P) :
    runUnits (lookupC t l) = pure (t l) := by simp [lookupC]

@[simp] theorem run_insert {α : Type} (t : Label P → Option α) (l : Label P) (a : α) :
    runUnits (insertC t l a) = pure (keepEarliest t l a) := by simp [insertC]

theorem run_mapM {α β : Type} (xs : List α) (f : α → UnitComp q β) (g : α → β)
    (h : ∀ x ∈ xs, runUnits (f x) = pure (g x)) :
    runUnits (xs.mapM f) = pure (xs.map g) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.mapM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem run_foldlM {α β : Type} (xs : List α) (f : β → α → UnitComp q β) (g : β → α → β)
    (h : ∀ x ∈ xs, ∀ s, runUnits (f s x) = pure (g s x)) (s : β) :
    runUnits (xs.foldlM f s) = pure (xs.foldl g s) := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp [List.foldlM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem find_pairs {ι β : Type} [DecidableEq ι] (xs : List ι) (g : ι → β) (i : ι)
    (hi : i ∈ xs) : (xs.map (fun j => (j, g j))).find? (fun e => decide (e.1 = i)) = some (i, g i) := by
  induction xs with
  | nil => simp at hi
  | cons j js ih =>
    by_cases hj : j = i
    · subst j; simp
    · simp only [List.mem_cons] at hi
      simp [hj, ih (hi.resolve_left (Ne.symm hj))]

theorem run_funOfM {ι β : Type} [DecidableEq ι] (xs : List ι) (d : β)
    (f : ι → UnitComp q β) (g : ι → β) (h : ∀ i ∈ xs, runUnits (f i) = pure (g i)) :
    runUnits (funOfM xs d f) =
      pure (fun i => (((xs.map fun j => (j, g j)).find? fun e => decide (e.1 = i)).map Prod.snd).getD d) := by
  unfold funOfM
  rw [run_bind, run_mapM xs _ (fun j => (j, g j)) (by intros; simp [h _ ‹_›])]
  simp

theorem run_funOfM_full {ι β : Type} [DecidableEq ι] (xs : List ι) (d : β)
    (f : ι → UnitComp q β) (g : ι → β) (h : ∀ i, runUnits (f i) = pure (g i))
    (hc : ∀ i, i ∈ xs) : runUnits (funOfM xs d f) = pure g := by
  rw [run_funOfM xs d f g (fun i _ => h i)]
  congr 1
  funext i
  simp [find_pairs xs g i (hc i)]

@[simp] theorem mem_legList (l : Leg P) : l ∈ legList P := by
  rcases l with ⟨X, k⟩
  cases X <;> simp [legList]

@[simp] theorem mem_cellList (c : Cell P) : c ∈ cellList P := by
  rcases c with ⟨k, l⟩
  simp [cellList]

@[simp] theorem mem_g2Keys (e : Cell P × Fin 3 × Sector) : e ∈ g2Keys P := by
  rcases e with ⟨c, l, s⟩
  cases s <;> simp [g2Keys]

@[simp] theorem mem_gtKeys (e : Fin 3 × Sector) : e ∈ gtKeys := by
  rcases e with ⟨l, s⟩
  cases s <;> simp [gtKeys]

@[simp] theorem sum_finRange {n : ℕ} {β : Type*} [AddCommMonoid β] (f : Fin n → β) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  exact (Fin.sum_univ_def f).symm

theorem fold_add {β : Type*} [AddCommMonoid β] (xs : List β) (a : β) :
    xs.foldl (fun s x => s + x) a = a + xs.sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

@[simp] theorem run_sum (xs : List (ZMod q)) : runUnits (sumC xs) = pure xs.sum := by
  cases xs with
  | nil => simp [sumC]
  | cons x xs =>
    rw [sumC, run_foldlM xs _ (fun a b => a + b) (by intros; simp)]
    congr 1
    simpa using fold_add xs x

@[simp] theorem run_sumMul (xs : List (ZMod q × ZMod q)) :
    runUnits (sumMulC xs) = pure ((xs.map fun e => e.1 * e.2).sum) := by
  cases xs with
  | nil => simp [sumMulC]
  | cons x xs =>
    simp only [sumMulC, run_bind, run_fmul, pure_bind]
    rw [run_foldlM xs _ (fun a e => a + e.1 * e.2) (by intros; simp)]
    congr 1
    simpa [← List.foldl_map] using fold_add (xs.map fun e => e.1 * e.2) (x.1 * x.2)

theorem run_vecOfM {n : ℕ} (f : Fin n → UnitComp q (ZMod q)) (g : Fin n → ZMod q)
    (h : ∀ i, runUnits (f i) = pure (g i)) : runUnits (vecOfM f) = pure g := by
  unfold vecOfM
  rw [run_bind, run_mapM _ f g (fun i _ => h i)]
  simp only [pure_bind, run_pure]
  congr 1
  funext i
  simp [List.getD_eq_getElem?_getD]

@[simp] theorem run_linV (a b : Fq P) (A B : Vec (Fq P) P.N) :
    runUnits (linV a b A B) = pure (a • A + b • B) := by
  apply run_vecOfM
  intro i; simp

@[simp] theorem run_addV (A B : Vec (Fq P) P.N) : runUnits (addV A B) = pure (A + B) := by
  apply run_vecOfM; intro i; simp

@[simp] theorem run_subV (A B : Vec (Fq P) P.N) : runUnits (subV A B) = pure (A - B) := by
  apply run_vecOfM; intro i; simp

@[simp] theorem run_negV (A : Vec (Fq P) P.N) : runUnits (negV A) = pure (-A) := by
  apply run_vecOfM; intro i; simp

@[simp] theorem run_smulV (a : Fq P) (A : Vec (Fq P) P.N) : runUnits (smulV a A) = pure (a • A) := by
  apply run_vecOfM; intro i; simp

@[simp] theorem run_linG1 (a b : Fq P) (A B : Fin P.K1 → Vec (Fq P) P.N) :
    runUnits (linG1 a b A B) = pure (a • A + b • B) := by
  apply run_funOfM_full <;> simp

@[simp] theorem run_linG2 (a b : Fq P) (A B : Cell P → Fin 3 → Sector → Fq P) :
    runUnits (linG2 a b A B) = pure (a • A + b • B) := by
  unfold linG2
  rw [run_bind, run_funOfM_full _ _ _ (fun e => a * A e.1 e.2.1 e.2.2 + b * B e.1 e.2.1 e.2.2)
    (by intro e; simp) (by simp)]
  rfl

theorem run_mapGT (f : Vec (Fq P) P.N → UnitComp P.q (Vec (Fq P) P.N))
    (g : Vec (Fq P) P.N → Vec (Fq P) P.N) (h : ∀ v, runUnits (f v) = pure (g v))
    (F : Fin 3 → Sector → Vec (Fq P) P.N) :
    runUnits (mapGT f F) = pure (fun l s => g (F l s)) := by
  unfold mapGT
  rw [run_bind, run_funOfM_full _ _ _ (fun e => g (F e.1 e.2)) (by simp [h]) (by simp)]
  rfl

theorem run_mapGT2 (f : Vec (Fq P) P.N → Vec (Fq P) P.N → UnitComp P.q (Vec (Fq P) P.N))
    (g : Vec (Fq P) P.N → Vec (Fq P) P.N → Vec (Fq P) P.N)
    (h : ∀ v w, runUnits (f v w) = pure (g v w)) (F G : Fin 3 → Sector → Vec (Fq P) P.N) :
    runUnits (mapGT2 f F G) = pure (fun l s => g (F l s) (G l s)) := by
  unfold mapGT2
  rw [run_bind, run_funOfM_full _ _ _ (fun e => g (F e.1 e.2) (G e.1 e.2)) (by simp [h]) (by simp)]
  rfl

theorem sum_legList {M : Type*} [AddCommMonoid M] (f : Leg P → M) :
    ((legList P).map f).sum = ∑ leg, f leg := by
  rw [Fintype.sum_prod_type, show (Finset.univ : Finset LegKind) = {.E, .O, .V} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [legList, List.map_append, List.sum_append, List.map_map, Function.comp_def]

@[simp] theorem run_pair (A : Fin P.K1 → Vec (Fq P) P.N)
    (B : Cell P → Fin 3 → Sector → Fq P) :
    runUnits (pairC A B) = pure (fun l s => ∑ k : Fin P.K1, (∑ leg : Leg P, B (k, leg) l s) • A k) := by
  unfold pairC
  rw [run_bind, run_funOfM_full _ _ _
    (fun e i => ∑ k : Fin P.K1, (∑ leg : Leg P, B (k, leg) e.1 e.2) * A k i) ?_ (by simp)]
  · simp only [pure_bind, run_pure]
    congr 1
    funext l s i
    simp
  · intro e
    rw [run_bind, run_funOfM_full _ _ _ (fun k => ∑ leg : Leg P, B (k, leg) e.1 e.2)
      (by intro k; simp [sum_legList]) (by simp)]
    simp only [pure_bind]
    apply run_vecOfM
    intro i
    simp [List.map_map]

@[simp] theorem run_all {ι : Type} (xs : List ι) (f : ι → UnitComp q Bool) (g : ι → Bool)
    (h : ∀ i ∈ xs, runUnits (f i) = pure (g i)) :
    runUnits (allC xs f) = pure (xs.all g) := by
  induction xs with
  | nil => simp [allC]
  | cons i is ih =>
    simp only [allC, run_bind, h i (by simp), pure_bind, List.all_cons]
    cases g i <;> simp [ih (fun j hj => h j (by simp [hj]))]

theorem sparse_sum (a x : Vec (Fq P) P.N) :
    ((sparseForm a).map (fun e => e.2 * x e.1)).sum = dot a x := by
  unfold sparseForm dot
  rw [List.map_filterMap]
  have h : (fun i => Option.map (fun e : Fin (P.N + 1) × Fq P => e.2 * x e.1)
      (if a i = 0 then none else some (i, a i))) =
      (fun i => if a i = 0 then none else some (a i * x i)) := by
    funext i; split <;> rfl
  rw [h]
  have hs (xs : List (Fin (P.N + 1))) :
      (xs.filterMap fun i => if a i = 0 then none else some (a i * x i)).sum =
      (xs.map fun i => a i * x i).sum := by
    induction xs with
    | nil => simp
    | cons i is ih => by_cases hi : a i = 0 <;> simp [hi, ih]
  rw [hs, sum_finRange]

@[simp] theorem run_dot (a x : Vec (Fq P) P.N) : runUnits (dotC (sparseForm a) x) = pure (dot a x) := by
  simp [dotC, List.map_map, Function.comp_def, sparse_sum]

variable [Fact (Nat.Prime P.q)]

@[simp] theorem run_sat (S : Relation P) (x : Vec (Fq P) P.N) :
    runUnits (satC (sparseOf S) x) = pure (decide (Sat S x)) := by
  unfold satC
  have hb : runUnits (allC (List.finRange P.N) (fun i => do
      let z ← feq (x i.succ) 0
      if z then pure true else feq (x i.succ) 1)) =
      pure (decide (∀ i : Fin P.N, x i.succ = 0 ∨ x i.succ = 1)) := by
    rw [run_all _ _ (fun i => decide (x i.succ = 0 ∨ x i.succ = 1)) (by
      intro i _; by_cases h : x i.succ = 0 <;> simp [h])]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, decide_eq_true_eq, List.mem_finRange, forall_const]
  by_cases h0 : x 0 = 1
  · simp only [run_bind, run_feq, pure_bind, h0, decide_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hb, run_map, map_pure, run_pure]
    by_cases hbool : ∀ i : Fin P.N, x i.succ = 0 ∨ x i.succ = 1
    · rw [show decide (∀ i : Fin P.N, x i.succ = 0 ∨ x i.succ = 1) = true from
        by simpa only [decide_eq_true_eq] using hbool]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [run_all _ _ (fun t => decide ((∑ f, dot ((S t).left f) x * dot ((S t).right f) x) =
        x 0 * dot (S t).linear x)) ?_]
      · congr 1
        apply Bool.eq_iff_iff.mpr
        simp [List.all_eq_true, Sat, h0, hbool]
      · intro t _
        simp only [sparseOf]
        rw [run_bind, run_mapM _ _ (fun f => dot ((S t).left f) x * dot ((S t).right f) x)
          (by intros; simp)]
        simp [h0]
    · simp [run_bind, run_map, hb, hbool, Sat, h0]
  · simp [run_bind, run_map, h0, Sat]

end Praxis.Proofs.Injectivity
