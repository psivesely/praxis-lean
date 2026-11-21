import Praxis.ExtractorCounted
import Praxis.Extractor
import Praxis.Grid
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.IndexSelection

open OracleComp OracleSpec

set_option maxHeartbeats 10000

theorem sum_flatMap_map {α β : Type} (xs : List α) (f : α → List β) (w : β → ℕ) :
    ((xs.flatMap f).map w).sum = (xs.map fun x => ((f x).map w).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem mapM_units {q : ℕ} {α β : Type} (xs : List α) (f : α → UnitComp q β)
    (cost : α → ℕ) (hf : ∀ x ∈ xs, WithinUnits (f x) (cost x)) :
    WithinUnits (xs.mapM f) (xs.map cost).sum := by
  induction xs with
  | nil => simp [WithinUnits]
  | cons x xs ih =>
    simp only [List.mapM_cons, List.map_cons, List.sum_cons]
    apply isQueryBoundP_bind (hf x (by simp))
    intro a ha
    simpa only [Nat.add_zero] using
      isQueryBoundP_bind (ih (fun y hy => hf y (by simp [hy])))
        (fun b _ => isQueryBoundP_pure isUnit (a :: b) 0)

theorem foldlM_units {q : ℕ} {α β : Type} (xs : List α) (f : β → α → UnitComp q β)
    (cost : α → ℕ) (init : β)
    (hf : ∀ x ∈ xs, ∀ s, WithinUnits (f s x) (cost x)) :
    WithinUnits (xs.foldlM f init) (xs.map cost).sum := by
  induction xs generalizing init with
  | nil => simp [WithinUnits]
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.map_cons, List.sum_cons]
    exact isQueryBoundP_bind (hf x (by simp) init)
      (fun s _ => ih s (fun y hy => hf y (by simp [hy])))

theorem funOfM_units {q : ℕ} {α β : Type} [DecidableEq α] (xs : List α) (d : β)
    (f : α → UnitComp q β) (k : ℕ) (hf : ∀ x ∈ xs, WithinUnits (f x) k) :
    WithinUnits (funOfM xs d f) (xs.length * k) := by
  unfold funOfM
  have h := mapM_units xs (fun i => do let b ← f i; pure (i, b)) (fun _ => k) (by
    intro x hx
    simpa [WithinUnits] using isQueryBoundP_bind (hf x hx) (fun b _ => isQueryBoundP_pure isUnit (x, b) 0))
  simpa [WithinUnits] using isQueryBoundP_bind h (fun l _ => isQueryBoundP_pure isUnit (fun i => ((l.find? fun e => decide (e.1 = i)).map Prod.snd).getD d) 0)

theorem vecOfM_units {q n : ℕ} (f : Fin n → UnitComp q (ZMod q)) (k : ℕ)
    (hf : ∀ i, WithinUnits (f i) k) : WithinUnits (vecOfM f) (n * k) := by
  unfold vecOfM
  have h := mapM_units (List.finRange n) f (fun _ => k) (by simp [hf])
  simpa [WithinUnits] using isQueryBoundP_bind h (fun l _ => isQueryBoundP_pure isUnit (fun i : Fin n => l.getD i.val 0) 0)

theorem sampleF_units {q : ℕ} : WithinUnits (sampleF : UnitComp q (ZMod q)) 1 := by
  simp [WithinUnits, sampleF, sampleFin, isUnit]

theorem fadd_units {q : ℕ} (x y : ZMod q) : WithinUnits (fadd x y) 1 := by
  simp [WithinUnits, fadd, fstep, isUnit]

theorem fwrite_units {q : ℕ} (x : ZMod q) : WithinUnits (fwrite x) 1 := by
  simp [WithinUnits, fwrite, fstep, isUnit]

theorem sumC_units {q : ℕ} (xs : List (ZMod q)) :
    WithinUnits (sumC xs) (max 1 (xs.length - 1)) := by
  cases xs with
  | nil => simpa [sumC] using (fwrite_units (q := q) 0)
  | cons x xs =>
    have h := foldlM_units xs (fun a b => fadd a b) (fun _ => 1) x
      (by intro y hy s; exact fadd_units s y)
    apply h.mono
    simp

theorem insertC_units {P : Params} {α : Type} (t : Label P → Option α)
    (l : Label P) (a : α) : WithinUnits (insertC t l a) 1 := by
  simp [WithinUnits, insertC, charge, isUnit]

def initCost {P : Params} : Option (G2Idx P) → ℕ
  | some (.totR1 _ _) => 3 * P.K1 * P.N
  | _ => 0

theorem initG2C_units {P : Params} (sk : Sketches P) (hN : 0 < P.N)
    (hc : ∀ leg : Leg P, ((cellList P).filter fun c => decide (c.2 = leg)).length ≤ P.K1)
    (i : Option (G2Idx P)) : WithinUnits (initG2C sk i) (initCost i) := by
  cases i with
  | none => simp [initG2C, initCost, WithinUnits]
  | some i =>
    cases i with
    | totR1 σ leg =>
      simp only [initG2C, initCost]
      have hs : ∀ e ∈ (((cellList P).filter fun c => decide (c.2 = leg)).flatMap fun c =>
          (List.finRange 3).map fun l => (c, l)),
          WithinUnits (sumC ((List.finRange (P.N + 1)).map fun j => sk e.1 e.2 σ j)) P.N := by
        intro e he
        have h := sumC_units ((List.finRange (P.N + 1)).map fun j => sk e.1 e.2 σ j)
        simpa [List.length_map, Nat.max_eq_right (by omega : 1 ≤ P.N)] using h
      have ht := funOfM_units (((cellList P).filter fun c => decide (c.2 = leg)).flatMap fun c =>
        (List.finRange 3).map fun l => (c, l)) 0 _ P.N hs
      have hu := OracleComp.isQueryBoundP_bind ht (fun t _ =>
        OracleComp.isQueryBoundP_pure isUnit (fun c l σ' => if σ' = σ ∧ c.2 = leg then t (c, l) else 0) 0)
      apply hu.mono
      simp only [Nat.add_zero, List.length_flatMap, List.length_map, List.length_finRange,
        List.map_const', List.sum_replicate, nsmul_eq_mul]
      nlinarith [hc leg]
    | _ => simp [initG2C, initCost, WithinUnits]

theorem initStateC_units {P : Params} (pub : PubView P) (sk : Sketches P)
    (hN : 0 < P.N)
    (hc : ∀ leg : Leg P, ((cellList P).filter fun c => decide (c.2 = leg)).length ≤ P.K1) :
    WithinUnits (initStateC pub sk)
      (pub.g1.length + (pub.g2.map fun e => initCost e.1 + 1).sum + pub.gT.length) := by
  unfold initStateC
  have h1 := foldlM_units pub.g1 (fun t e => insertC t e.2 (initG1 e.1)) (fun _ => 1)
    (fun _ => none) (by intro e he t; exact insertC_units t e.2 (initG1 e.1))
  have h2 (t : Label P → Option (Cell P → Fin 3 → Sector → Fq P)) :=
    foldlM_units pub.g2 (fun t e => do
      let D ← initG2C sk e.1
      insertC t e.2 D) (fun e => initCost e.1 + 1) t (by
        intro e he t
        exact OracleComp.isQueryBoundP_bind (initG2C_units sk hN hc e.1)
          (fun D _ => insertC_units t e.2 D))
  have h3 (t : Label P → Option (Fin 3 → Sector → Algebra.Vec (Fq P) P.N)) :=
    foldlM_units pub.gT (fun t e => insertC t e.2 0) (fun _ => 1) t
      (by intro e he t; exact insertC_units t e.2 0)
  have h := OracleComp.isQueryBoundP_bind h1 (fun d1 _ =>
    OracleComp.isQueryBoundP_bind (h2 (fun _ => none)) (fun d2 _ =>
      OracleComp.isQueryBoundP_bind (h3 (fun _ => none)) (fun dT _ =>
        OracleComp.isQueryBoundP_pure isUnit
          ({ d1 := d1, d2 := d2, dT := dT, named := fun _ => false, found := none } : ExState P) 0)))
  simpa [WithinUnits, Nat.add_assoc] using h

end Praxis.Proofs.IndexSelection
