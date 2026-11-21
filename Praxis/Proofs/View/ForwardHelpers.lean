import Praxis.Proofs.View.Converse
import Praxis.Enc
import Praxis.Grid
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open scoped BigOperators

section Lists

lemma sum_legKind {M : Type*} [AddCommMonoid M] (f : LegKind → M) :
    ∑ k, f k = f .E + f .O + f .V := by
  change ({.E, .O, .V} : Finset LegKind).sum f = _
  simp [add_assoc]

lemma sum_sector {M : Type*} [AddCommMonoid M] (f : Sector → M) :
    ∑ σ, f σ = f .plain + f .alpha := by
  change ({.plain, .alpha} : Finset Sector).sum f = _
  simp

variable {M α β : Type*} [AddCommMonoid M]

lemma list_sum_flatMap (l : List α) (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

lemma list_sum_filterMap (l : List α) (g : α → Option β) (f : β → M) :
    ((l.filterMap g).map f).sum = (l.map fun a => (g a).elim 0 f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : g a <;> simp [h, ih]

lemma legList_sum {P : Params} (f : Leg P → M) :
    ((legList P).map f).sum = ∑ l, f l := by
  simp only [legList, list_sum_flatMap, List.map_map, Function.comp_def, ← Fin.sum_univ_def, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Fintype.sum_prod_type, sum_legKind]
  ac_rfl

lemma cellList_sum {P : Params} (f : Cell P → M) :
    ((cellList P).map f).sum = ∑ c, f c := by
  simp only [cellList, list_sum_flatMap, List.map_map, Function.comp_def, legList_sum, ← Fin.sum_univ_def,
    Fintype.sum_prod_type]

lemma remList_sum {P : Params} (f : RemExp P → M) :
    (((List.finRange (P.U * P.E1p)).filterMap fun s =>
      if h : P.U ∣ s.val then none else some (⟨s, h⟩ : RemExp P)).map f).sum = ∑ s, f s := by
  classical
  rw [list_sum_filterMap, ← Fin.sum_univ_def]
  have hh : (∑ s : Fin (P.U * P.E1p),
      (if h : P.U ∣ s.val then none else some (⟨s, h⟩ : RemExp P)).elim 0 f) =
      ∑ s ∈ Finset.univ.filter (fun s : Fin (P.U * P.E1p) => ¬ P.U ∣ s.val),
        (if h : P.U ∣ s.val then none else some (⟨s, h⟩ : RemExp P)).elim 0 f := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : P.U ∣ s.val <;> simp [hs]
  rw [hh]
  rw [Finset.sum_subtype (p := fun s : Fin (P.U * P.E1p) => ¬ P.U ∣ s.val)
    _ (by simp)]
  apply Finset.sum_congr rfl
  intro s _
  simp [s.property]

lemma keys1_sum {P : Params} (f : Option (G1Idx P) → M) :
    ((keys1 P).map f).sum = f none +
      (∑ k1, ∑ i, f (some (.L1 k1 i))) +
      (∑ k1, ∑ i, f (some (.L2 k1 i))) +
      (∑ k1, f (some (.totL1 k1))) + (∑ k1, f (some (.totL2 k1))) +
      (∑ s, f (some (.QP s))) + (∑ s, f (some (.RP s))) + (∑ i, f (some (.GY i))) := by
  simp only [keys1, g1Order, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, list_sum_flatMap,
    ← Fin.sum_univ_def]
  have hh := remList_sum (P := P) (fun s => f (some (.RP s)))
  rw [list_sum_filterMap, ← Fin.sum_univ_def] at hh ⊢
  have he : (fun s : Fin (P.U * P.E1p) =>
      (if h : P.U ∣ s.val then none else some (G1Idx.RP ⟨s, h⟩)).elim 0 (fun a => f (some a))) =
      (fun s => (if h : P.U ∣ s.val then none else some (⟨s, h⟩ : RemExp P)).elim 0
        (fun s => f (some (.RP s)))) := by
    funext s
    split <;> rfl
  rw [he, hh]
  ac_rfl

lemma g2OrderSector_sum {P : Params} (σ : Sector) (f : G2Idx P → M) :
    ((g2OrderSector P σ).map f).sum =
      (∑ l, ∑ j, f (.ZeroCoordinate σ l j)) + (∑ l, ∑ j, f (.R2 σ l j)) +
      (∑ l, f (.totR1 σ l)) + (∑ l, f (.totR2 σ l)) +
      (∑ cl, ∑ j, f (.QB σ cl j)) + (∑ cl, ∑ j, f (.RB σ cl j)) +
      (∑ l, f (.SC σ l)) + (∑ g, ∑ e, f (.GB σ g e)) + (∑ s, ∑ e, f (.GM σ s e)) := by
  simp only [g2OrderSector, List.map_append, List.sum_append, list_sum_flatMap,
    List.map_map, Function.comp_def, ← Fin.sum_univ_def, legList_sum, cellList_sum]
  rfl

lemma keys2_sum {P : Params} (f : Option (G2Idx P) → M) :
    ((keys2 P).map f).sum = f none + ∑ σ,
      ((∑ l, ∑ j, f (some (.ZeroCoordinate σ l j))) + (∑ l, ∑ j, f (some (.R2 σ l j))) +
      (∑ l, f (some (.totR1 σ l))) + (∑ l, f (some (.totR2 σ l))) +
      (∑ cl, ∑ j, f (some (.QB σ cl j))) + (∑ cl, ∑ j, f (some (.RB σ cl j))) +
      (∑ l, f (some (.SC σ l))) + (∑ g, ∑ e, f (some (.GB σ g e))) +
      (∑ s, ∑ e, f (some (.GM σ s e)))) := by
  simp only [keys2, g2Order, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, g2OrderSector_sum, sum_sector]

end Lists

section Linearity

variable {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
  (v : Fin P.n → Vec (Fq P) P.N) (ω : Assign P)

lemma valT_zero : valT pp v ω (0 : ExprT P) = 0 := by
  simp [valT]

end Linearity

section Totals

variable {P : Params}

def expand1C (f : Option (G1Idx P) → Fq P) : Option (G1Idx P) → Fq P
  | some (.L1 k i) => f (some (.L1 k i)) + f (some (.totL1 k))
  | some (.L2 k i) => f (some (.L2 k i)) + f (some (.totL2 k))
  | some (.totL1 _) | some (.totL2 _) => 0
  | a => f a

def expand1 (D : ExprT P) : ExprT P := (fun ab => expand1C (fun a => D.1 (a, ab.2)) ab.1, D.2)

def expand2C (f : Option (G2Idx P) → Fq P) : Option (G2Idx P) → Fq P
  | some (.ZeroCoordinate σ l j) => f (some (.ZeroCoordinate σ l j)) + f (some (.totR1 σ l))
  | some (.R2 σ l j) => f (some (.R2 σ l j)) + f (some (.totR2 σ l))
  | some (.totR1 _ _) | some (.totR2 _ _) => 0
  | b => f b

def expand2 (D : ExprT P) : ExprT P := (fun ab => expand2C (fun b => D.1 (ab.1, b)) ab.2, D.2)

def expandTot (D : ExprT P) : ExprT P := expand2 (expand1 D)

lemma list_sum_comm {α β M : Type*} [AddCommMonoid M] (l : List α) (k : List β) (f : α → β → M) :
    (l.map fun a => (k.map (f a)).sum).sum = (k.map fun b => (l.map fun a => f a b).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.sum_map_add, ih]

lemma sum_expand1 (f x : Option (G1Idx P) → Fq P)
    (h1 : ∀ k, x (some (.totL1 k)) = ∑ i, x (some (.L1 k i)))
    (h2 : ∀ k, x (some (.totL2 k)) = ∑ i, x (some (.L2 k i))) :
    ((keys1 P).map fun a => expand1C f a * x a).sum =
      ((keys1 P).map fun a => f a * x a).sum := by
  simp only [keys1_sum, expand1C, zero_mul, Finset.sum_const_zero, add_zero,
    add_mul, Finset.sum_add_distrib, h1, h2, Finset.mul_sum]
  ring

lemma sum_expand2 (f x : Option (G2Idx P) → Fq P)
    (h1 : ∀ σ l, x (some (.totR1 σ l)) = ∑ j, x (some (.ZeroCoordinate σ l j)))
    (h2 : ∀ σ l, x (some (.totR2 σ l)) = ∑ j, x (some (.R2 σ l j))) :
    ((keys2 P).map fun b => expand2C f b * x b).sum =
      ((keys2 P).map fun b => f b * x b).sum := by
  simp only [keys2_sum, expand2C, zero_mul, Finset.sum_const_zero, add_zero,
    add_mul, Finset.sum_add_distrib, h1, h2, Finset.mul_sum]
  ring

variable [Fact (Nat.Prime P.q)] (pp : PublicParams P)
  (v : Fin P.n → Vec (Fq P) P.N) (ω : Assign P)

lemma valT_expand1 (D : ExprT P) : valT pp v ω (expand1 D) = valT pp v ω D := by
  unfold valT expand1
  dsimp only
  rw [list_sum_comm, list_sum_comm (keys1 P)]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  simp only [← mul_assoc, List.sum_map_mul_right]
  congr 1
  apply sum_expand1 <;> intro k <;> simp [e1At, g1Exp]

set_option maxHeartbeats 1000000 in
lemma valT_expand2 (D : ExprT P) : valT pp v ω (expand2 D) = valT pp v ω D := by
  unfold valT expand2
  dsimp only
  apply congrArg (fun x => x + D.2 * gtExp pp ω.coins)
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  have hm (f : Option (G2Idx P) → Fq P) :
      ((keys2 P).map fun b => f b * (e1At pp ω a * e2At pp v ω b)).sum =
        e1At pp ω a * ((keys2 P).map fun b => f b * e2At pp v ω b).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro b _
    ring
  rw [hm, hm]
  congr 1
  apply sum_expand2
  · intro σ l
    simp [e2At, Finset.mul_sum]
  · intro σ l
    simp [e2At, g2Exp, r2Exp, Finset.mul_sum]

lemma valT_expandTot (D : ExprT P) : valT pp v ω (expandTot D) = valT pp v ω D := by
  rw [expandTot, valT_expand2, valT_expand1]

end Totals

end Praxis.Proofs.View
