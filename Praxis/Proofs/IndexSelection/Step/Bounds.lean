import Praxis.Proofs.IndexSelection.Bounds
import Praxis.Constants
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.IndexSelection

open OracleComp OracleSpec

open Praxis.Algebra (Vec)

private theorem ub_bind {q : ℕ} {α β : Type} {c : UnitComp q α}
    {f : α → UnitComp q β} {n m : ℕ} (hc : WithinUnits c n)
    (hf : ∀ x, WithinUnits (f x) m) : WithinUnits (c >>= f) (n + m) :=
  isQueryBoundP_bind hc (fun x _ => hf x)

private theorem ub_pure {q : ℕ} {α : Type} (x : α) (k : ℕ) :
    WithinUnits (pure x : UnitComp q α) k := by simp [WithinUnits]

private theorem ub_map {q : ℕ} {α β : Type} (f : α → β) {c : UnitComp q α} {k : ℕ}
    (h : WithinUnits c k) : WithinUnits (f <$> c) k :=
  (isQueryBoundP_map_iff c f k).mpr h

private theorem ub_mapM {q : ℕ} {α β : Type} (xs : List α)
    (f : α → UnitComp q β) (k : ℕ) (h : ∀ x, WithinUnits (f x) k) :
    WithinUnits (xs.mapM f) (xs.length * k) := by
  induction xs with
  | nil => simpa using ub_pure (q := q) ([] : List β) 0
  | cons x xs ih =>
    simp only [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      ub_bind (h x) (fun y => ub_map (List.cons y) ih)

private theorem ub_foldlM {q : ℕ} {α β : Type} (xs : List α)
    (f : β → α → UnitComp q β) (k : ℕ) (h : ∀ b x, WithinUnits (f b x) k)
    (init : β) : WithinUnits (xs.foldlM f init) (xs.length * k) := by
  induction xs generalizing init with
  | nil => simpa using ub_pure (q := q) init 0
  | cons x xs ih =>
    simp only [List.foldlM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using ub_bind (h init x) (fun b => ih b)

private theorem ub_query {q : ℕ} (s : FieldStep q) : WithinUnits (fstep s) 1 := by
  simp [WithinUnits, fstep, isUnit]

private theorem ub_charge {q : ℕ} (c : Charge) : WithinUnits (charge (q := q) c) 1 := by
  simp [WithinUnits, charge, isUnit]

private theorem ub_vecOfM {P : Params} (f : Fin (P.N + 1) → UnitComp P.q (Fq P))
    (k : ℕ) (h : ∀ i, WithinUnits (f i) k) :
    WithinUnits (vecOfM f) ((P.N + 1) * k) := by
  unfold vecOfM
  simp only [LawfulMonad.bind_pure_comp]
  apply ub_map
  simpa using ub_mapM (List.finRange (P.N + 1)) f k h

private theorem ub_funOfM {q : ℕ} {α β : Type} [DecidableEq α] (xs : List α)
    (d : β) (f : α → UnitComp q β) (k : ℕ) (h : ∀ i, WithinUnits (f i) k) :
    WithinUnits (funOfM xs d f) (xs.length * k) := by
  unfold funOfM
  simp only [LawfulMonad.bind_pure_comp]
  apply ub_map
  apply ub_mapM
  intro i
  exact ub_map (Prod.mk i) (h i)

private theorem ub_linV {P : Params} (a b : Fq P) (A B : Vec (Fq P) P.N) :
    WithinUnits (linV a b A B) ((P.N + 1) * 3) := by
  apply ub_vecOfM
  intro i
  change WithinUnits (do let x ← fstep (.mul a (A i)); let y ← fstep (.mul b (B i)); fstep (.add x y)) 3
  exact ub_bind (ub_query (.mul a (A i))) (fun x =>
      ub_bind (ub_query (.mul b (B i))) (fun y => ub_query (.add x y)))

private theorem ub_subV {P : Params} (A B : Vec (Fq P) P.N) :
    WithinUnits (subV A B) (P.N + 1) := by
  simpa [subV, fsub] using ub_vecOfM (fun i => fstep (.sub (A i) (B i))) 1
    (fun _ => ub_query _)

private theorem ub_negV {P : Params} (A : Vec (Fq P) P.N) :
    WithinUnits (negV A) (P.N + 1) := by
  simpa [negV, fneg] using ub_vecOfM (fun i => fstep (.neg (A i))) 1
    (fun _ => ub_query _)

private theorem ub_lookup {P : Params} {α : Type} (t : Label P → Option α) (l : Label P) :
    WithinUnits (lookupC t l) 1 := by
  unfold lookupC
  simp only [LawfulMonad.bind_pure_comp]
  exact ub_map _ (ub_charge (q := P.q) .tableStep)

private theorem ub_insert {P : Params} {α : Type} (t : Label P → Option α) (l : Label P) (a : α) :
    WithinUnits (insertC t l a) 1 := by
  unfold insertC
  simp only [LawfulMonad.bind_pure_comp]
  exact ub_map _ (ub_charge (q := P.q) .tableStep)

private theorem ub_sumC {q : ℕ} (xs : List (ZMod q)) (h : 0 < xs.length) :
    WithinUnits (sumC xs) (xs.length - 1) := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
    simpa [sumC] using ub_foldlM xs fadd 1 (fun _ _ => ub_query _) x

private theorem ub_sumMulC {q : ℕ} (xs : List (ZMod q × ZMod q)) (h : 0 < xs.length) :
    WithinUnits (sumMulC xs) (2 * xs.length - 1) := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
    have hf : ∀ (a : ZMod q) (e : ZMod q × ZMod q), WithinUnits (do let t ← fmul e.1 e.2; fadd a t) 2 := by
      intro a e
      exact ub_bind (ub_query (.mul e.1 e.2)) (fun t => ub_query (.add a t))
    have hb := ub_bind (ub_query (.mul x.1 x.2))
      (fun a => ub_foldlM xs (fun acc e => do let t ← fmul e.1 e.2; fadd acc t) 2 hf a)
    convert hb using 1 <;> simp [sumMulC, fmul] <;> omega

private theorem ub_linG1 {P : Params} (a b : Fq P)
    (A B : Fin P.K1 → Vec (Fq P) P.N) :
    WithinUnits (linG1 a b A B) (P.K1 * ((P.N + 1) * 3)) := by
  simpa [linG1] using ub_funOfM (List.finRange P.K1) 0
    (fun k => linV a b (A k) (B k)) ((P.N + 1) * 3) (fun _ => ub_linV _ _ _ _)

private theorem ub_linG2 {P : Params} (a b : Fq P)
    (A B : Cell P → Fin 3 → Sector → Fq P) :
    WithinUnits (linG2 a b A B) ((g2Keys P).length * 3) := by
  unfold linG2
  have h : ∀ e : Cell P × Fin 3 × Sector, WithinUnits (do
      let x ← fmul a (A e.1 e.2.1 e.2.2)
      let y ← fmul b (B e.1 e.2.1 e.2.2)
      fadd x y) 3 := by
    intro e
    change WithinUnits (do
      let x ← fstep (.mul a (A e.1 e.2.1 e.2.2))
      let y ← fstep (.mul b (B e.1 e.2.1 e.2.2))
      fstep (.add x y)) 3
    exact ub_bind (ub_query (.mul a (A e.1 e.2.1 e.2.2)))
      (fun x => ub_bind (ub_query (.mul b (B e.1 e.2.1 e.2.2)))
        (fun y => ub_query (.add x y)))
  simp only [LawfulMonad.bind_pure_comp]
  exact ub_map _ (ub_funOfM (g2Keys P) 0 _ 3 h)

private theorem ub_mapGT {P : Params}
    (f : Vec (Fq P) P.N → UnitComp P.q (Vec (Fq P) P.N))
    (F : Fin 3 → Sector → Vec (Fq P) P.N) (k : ℕ)
    (h : ∀ x, WithinUnits (f x) k) : WithinUnits (mapGT f F) (6 * k) := by
  unfold mapGT
  have hh := ub_funOfM gtKeys 0 (fun e => f (F e.1 e.2)) k (fun e => h _)
  have hk : gtKeys.length = 6 := by decide +kernel
  simp only [LawfulMonad.bind_pure_comp]
  apply ub_map
  simpa [hk] using hh

private theorem ub_mapGT2 {P : Params}
    (f : Vec (Fq P) P.N → Vec (Fq P) P.N → UnitComp P.q (Vec (Fq P) P.N))
    (F G : Fin 3 → Sector → Vec (Fq P) P.N) (k : ℕ)
    (h : ∀ x y, WithinUnits (f x y) k) : WithinUnits (mapGT2 f F G) (6 * k) := by
  unfold mapGT2
  have hh := ub_funOfM gtKeys 0 (fun e => f (F e.1 e.2) (G e.1 e.2)) k (fun e => h _ _)
  have hk : gtKeys.length = 6 := by decide +kernel
  simp only [LawfulMonad.bind_pure_comp]
  apply ub_map
  simpa [hk] using hh

private theorem ub_pairC {P : Params} (α : Fin P.K1 → Vec (Fq P) P.N)
    (β : Cell P → Fin 3 → Sector → Fq P) (hk : 0 < P.K1) (hl : 0 < (legList P).length) :
    WithinUnits (pairC α β)
      (6 * (P.K1 * ((legList P).length - 1) + (P.N + 1) * (2 * P.K1 - 1))) := by
  unfold pairC
  have he : ∀ e : Fin 3 × Sector, WithinUnits (do
      let cb ← funOfM (List.finRange P.K1) 0 fun k1 =>
        sumC ((legList P).map fun leg => β (k1, leg) e.1 e.2)
      vecOfM fun i => sumMulC ((List.finRange P.K1).map fun k1 => (cb k1, α k1 i)))
      (P.K1 * ((legList P).length - 1) + (P.N + 1) * (2 * P.K1 - 1)) := by
    intro e
    apply ub_bind
    · simpa using ub_funOfM (List.finRange P.K1) 0
        (fun k1 => sumC ((legList P).map fun leg => β (k1, leg) e.1 e.2))
        ((legList P).length - 1) (fun k1 => by
          simpa using ub_sumC ((legList P).map fun leg => β (k1, leg) e.1 e.2) (by simpa))
    · intro cb
      apply ub_vecOfM
      intro i
      simpa using ub_sumMulC ((List.finRange P.K1).map fun k1 => (cb k1, α k1 i)) (by simpa)
  have hh := ub_funOfM gtKeys 0 _ _ he
  have hg : gtKeys.length = 6 := by decide +kernel
  simp only [LawfulMonad.bind_pure_comp]
  apply ub_map
  simpa [hg] using hh

private theorem ub_testExpr (P : Params) (hP : P = P0) (S : Relation P) (hS : InShape P S)
    (F : Fin 3 → Sector → Vec (Fq P) P.N) :
    WithinUnits (testExprC (sparseOf S) F)
      (2 * (Constants.running_time_extractor_per_sector_test +
        Constants.running_time_extractor_per_sector_test_per_S * size S)) := by
  unfold testExprC
  have h := jset_test P hP S hS
  refine (ub_bind (h (fun l => F l .plain))
    (m := Constants.running_time_extractor_per_sector_test +
      Constants.running_time_extractor_per_sector_test_per_S * size S) ?_).mono (by omega)
  intro x
  cases x with
  | none => exact h (fun l => F l .alpha)
  | some x => exact ub_pure _ _

private theorem ub_gtStep (P : Params) (hP : P = P0) (S : Relation P) (hS : InShape P S)
    (st : ExState P) (F : Fin 3 → Sector → Vec (Fq P) P.N) (res : Label P) :
    WithinUnits (gtStepC (sparseOf S) st F res)
      (2 + 6 * (P.N + 1) + 4 * (Constants.running_time_extractor_per_sector_test +
        Constants.running_time_extractor_per_sector_test_per_S * size S)) := by
  let B := Constants.running_time_extractor_per_sector_test +
    Constants.running_time_extractor_per_sector_test_per_S * size S
  have htest : ∀ G, WithinUnits (testExprC (sparseOf S) G) (2 * B) :=
    fun G => ub_testExpr P hP S hS G
  have hsub : ∀ E, WithinUnits (mapGT2 subV F E) (6 * (P.N + 1)) :=
    fun E => ub_mapGT2 subV F E (P.N + 1) ub_subV
  unfold gtStepC
  refine (ub_bind (ub_lookup st.dT res) (m := 1 + (2 * B + (6 * (P.N + 1) + 2 * B))) ?_).mono (by omega)
  intro old
  refine ub_bind (ub_insert st.dT res F) ?_
  intro dT
  refine ub_bind (htest F) ?_
  intro x
  cases x with
  | some x => exact ub_pure _ _
  | none =>
    cases old with
    | none => exact ub_pure _ _
    | some E =>
      refine ub_bind (hsub E) ?_
      intro D
      simpa only [LawfulMonad.bind_pure_comp] using ub_map (fun r => { st with dT := dT, found := r }) (htest D)

theorem step_bound (P : Params) (hP : P = P0) (S : Relation P) (hS : InShape P S)
    (st : ExState P) (op : TrOp P) :
    WithinUnits (exStepC (sparseOf S) st op)
      (Constants.running_time_extractor_per_operation + 1 +
        2 * 2 * (Constants.running_time_extractor_per_sector_test +
          Constants.running_time_extractor_per_sector_test_per_S * size S)) := by
  let B := Constants.running_time_extractor_per_sector_test +
    Constants.running_time_extractor_per_sector_test_per_S * size S
  let C := Constants.running_time_extractor_per_operation + 1
  have hk : 0 < P.K1 := by rw [hP]; decide +kernel
  have hl : 0 < (legList P).length := by rw [hP]; decide +kernel
  have hg : (g2Keys P).length = 6 * (P.K1 * (legList P).length) := by
    simp [g2Keys, cellList, List.length_flatMap]
    omega
  have hlegs : (legList P).length = 36 := by rw [hP]; decide +kernel
  have hn : P.N = 391693 := by rw [hP]; rfl
  have hk' : P.K1 = 192 := by rw [hP]; rfl
  have hc : C = 902503300 := rfl
  have hgt : ∀ st F res, WithinUnits (gtStepC (sparseOf S) st F res)
      (2 + 6 * (P.N + 1) + 4 * B) := ub_gtStep P hP S hS
  change WithinUnits (exStepC (sparseOf S) st op) (C + 4 * B)
  cases hf : st.found with
  | some x => simp [exStepC, hf, WithinUnits]
  | none =>
    cases op with
    | lin sort a b u v res =>
      cases sort with
      | g₁ =>
        simp only [exStepC, hf]
        refine (ub_bind (ub_lookup st.d1 u) (m := 1 + (P.K1 * ((P.N + 1) * 3) + 1)) ?_).mono ?_
        · intro A
          refine ub_bind (ub_lookup st.d1 v) ?_
          intro D
          refine ub_bind (ub_linG1 a b (A.getD 0) (D.getD 0)) ?_
          intro R
          simpa only [LawfulMonad.bind_pure_comp] using ub_map (fun d1 => { st with d1 := d1, found := none }) (ub_insert st.d1 res R)
        · rw [hn, hk', hc]
          omega
      | g₂ =>
        simp only [exStepC, hf]
        refine (ub_bind (ub_lookup st.d2 u) (m := 1 + ((g2Keys P).length * 3 + 1)) ?_).mono ?_
        · intro A
          refine ub_bind (ub_lookup st.d2 v) ?_
          intro D
          refine ub_bind (ub_linG2 a b (A.getD 0) (D.getD 0)) ?_
          intro R
          simpa only [LawfulMonad.bind_pure_comp] using ub_map (fun d2 => { st with d2 := d2, found := none }) (ub_insert st.d2 res R)
        · rw [hg, hlegs, hk', hc]
          omega
      | gₜ =>
        simp only [exStepC, hf]
        refine (ub_bind (ub_lookup st.dT u)
          (m := 1 + (6 * ((P.N + 1) * 3) + (2 + 6 * (P.N + 1) + 4 * B))) ?_).mono ?_
        · intro A
          refine ub_bind (ub_lookup st.dT v) ?_
          intro D
          refine ub_bind (ub_mapGT2 (linV a b) (A.getD 0) (D.getD 0)
            ((P.N + 1) * 3) (ub_linV a b)) ?_
          exact fun F => hgt st F res
        · rw [hn, hc]
          omega
    | pair u v res =>
      simp only [exStepC, hf]
      refine (ub_bind (ub_lookup st.d1 u)
        (m := 1 + (6 * (P.K1 * ((legList P).length - 1) + (P.N + 1) * (2 * P.K1 - 1)) +
          (2 + 6 * (P.N + 1) + 4 * B))) ?_).mono ?_
      · intro A
        refine ub_bind (ub_lookup st.d2 v) ?_
        intro D
        refine ub_bind (ub_pairC (A.getD 0) (D.getD 0) hk hl) ?_
        exact fun F => hgt st F res
      · rw [hn, hk', hlegs, hc]
        omega
    | name v res =>
      simp only [exStepC, hf]
      by_cases hv : st.named v
      · simp [hv, WithinUnits, charge, isUnit, hc]
      · simp only [hv, Bool.false_eq_true, if_false]
        refine (ub_bind (ub_charge (q := P.q) .tableStep)
          (m := 1 + (1 + (6 * (P.N + 1) + (2 + 6 * (P.N + 1) + 4 * B)))) ?_).mono ?_
        · intro _
          refine ub_bind (ub_charge (q := P.q) .tableStep) ?_
          intro _
          refine ub_bind (ub_lookup st.dT v) ?_
          intro A
          refine ub_bind (ub_mapGT negV (A.getD 0) (P.N + 1) ub_negV) ?_
          exact fun F => hgt _ F _
        · rw [hn, hc]
          omega

end Praxis.Proofs.IndexSelection
