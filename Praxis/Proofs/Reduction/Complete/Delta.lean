import Praxis.Proofs.Basic
import Praxis.Enc
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Reduction

private theorem sum_map_sub {α R : Type*} [AddCommGroup R]
    (l : List α) (f g : α → R) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; abel

private theorem sum_map_flat {α β R : Type*} [AddCommMonoid R]
    (l : List α) (g : α → List β) (f : β → R) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

private theorem sum_map_swap {α β R : Type*} [AddCommMonoid R]
    (xs : List α) (ys : List β) (f : α → β → R) :
    (xs.map fun x => (ys.map fun y => f x y).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]

private theorem sum_map_fin_swap {α β R : Type*} [AddCommMonoid R] [Fintype β]
    (xs : List α) (f : α → β → R) :
    (xs.map fun x => ∑ y, f x y).sum = ∑ y, (xs.map fun x => f x y).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private theorem sum_map_factor {α R : Type*} [CommSemiring R]
    (xs : List α) (f : α → R) (x : R) :
    (xs.map fun a => f a * x).sum = (xs.map f).sum * x := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih, add_mul]

theorem keys2_sum_restricted {P : Params} [Fact (Nat.Prime P.q)]
    (f : Option (G2Idx P) → Fq P)
    (h : ∀ b, (match b with
      | some (.ZeroCoordinate _ _ _) => False
      | some (.totR1 _ _) => False
      | _ => True) → f b = 0) :
    ((keys2 P).map f).sum =
      ((legList P).map fun l => ∑ j, f (some (.ZeroCoordinate .plain l j))).sum +
      ((legList P).map fun l => f (some (.totR1 .plain l))).sum +
      ((legList P).map fun l => ∑ j, f (some (.ZeroCoordinate .alpha l j))).sum +
      ((legList P).map fun l => f (some (.totR1 .alpha l))).sum := by
  classical
  simp only [keys2, g2Order, g2OrderSector, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, sum_map_flat, List.map_map]
  simp [Function.comp_def, Fin.sum_univ_def, h none trivial,
    h (some (.R2 _ _ _)) trivial, h (some (.totR2 _ _)) trivial,
    h (some (.QB _ _ _)) trivial, h (some (.RB _ _ _)) trivial,
    h (some (.SC _ _)) trivial, h (some (.GB _ _ _)) trivial,
    h (some (.GM _ _ _)) trivial, add_assoc]

theorem e2At_sub_search {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (c : Coins P) (r r' : Algebra.Vec (Fq P) P.N) (b : Option (G2Idx P)) :
    e2At pp v ⟨c, r'⟩ b - e2At pp v ⟨c, r⟩ b =
      match b with
      | some (.ZeroCoordinate σ l j) => sectorScale c σ * legScale c l * (r' j - r j)
      | some (.totR1 σ l) => sectorScale c σ * legScale c l * ∑ j, (r' j - r j)
      | _ => 0 := by
  classical
  cases b with
  | none => simp [e2At]
  | some b =>
    cases b with
    | ZeroCoordinate σ l j => simp only [e2At, r1ExpAt]; ring
    | totR1 σ l =>
      simp only [e2At, r1ExpAt, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    | R2 σ l j => simp [e2At]
    | totR2 σ l => simp [e2At]
    | QB σ c j => simp [e2At]
    | RB σ c j => simp [e2At]
    | SC σ l => simp [e2At]
    | GB σ g e => simp [e2At]
    | GM σ s e => simp [e2At]

theorem valT_sub_search {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (c : Coins P) (r r' : Algebra.Vec (Fq P) P.N) (D : ExprT P) :
    valT pp v ⟨c, r'⟩ D - valT pp v ⟨c, r⟩ D =
      ((keys1 P).map fun a => ((keys2 P).map fun b =>
        D.1 (a, b) * (e1At pp ⟨c, r⟩ a *
          (e2At pp v ⟨c, r'⟩ b - e2At pp v ⟨c, r⟩ b))).sum).sum := by
  classical
  have he1 (a : Option (G1Idx P)) : e1At pp ⟨c, r'⟩ a = e1At pp ⟨c, r⟩ a := by
    cases a <;> rfl
  simp only [valT, add_sub_add_right_eq_sub, ← sum_map_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  rw [he1 a]
  ring

theorem valT_sub_expanded {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (c : Coins P) (r r' : Algebra.Vec (Fq P) P.N) (D : ExprT P) :
    valT pp v ⟨c, r'⟩ D - valT pp v ⟨c, r⟩ D =
      ((keys1 P).map fun a =>
        (((legList P).map fun l => ∑ j,
          e1At pp ⟨c, r⟩ a *
            (D.1 (a, some (.ZeroCoordinate .plain l j)) + D.1 (a, some (.totR1 .plain l))) *
            (sectorScale c .plain * legScale c l) * (r' j - r j)).sum +
         ((legList P).map fun l => ∑ j,
          e1At pp ⟨c, r⟩ a *
            (D.1 (a, some (.ZeroCoordinate .alpha l j)) + D.1 (a, some (.totR1 .alpha l))) *
            (sectorScale c .alpha * legScale c l) * (r' j - r j)).sum)).sum := by
  classical
  rw [valT_sub_search]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  rw [keys2_sum_restricted _ (by
    intro b hb
    rw [e2At_sub_search]
    cases b with
    | none => simp
    | some b => cases b <;> simp_all)]
  simp only [e2At_sub_search]
  have sector (σ : Sector) :
      ((legList P).map fun l => ∑ j,
        D.1 (a, some (.ZeroCoordinate σ l j)) *
          (e1At pp ⟨c, r⟩ a * (sectorScale c σ * legScale c l * (r' j - r j)))).sum +
      ((legList P).map fun l =>
        D.1 (a, some (.totR1 σ l)) *
          (e1At pp ⟨c, r⟩ a * (sectorScale c σ * legScale c l * ∑ j, (r' j - r j)))).sum =
      ((legList P).map fun l => ∑ j,
        e1At pp ⟨c, r⟩ a * (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l))) *
          (sectorScale c σ * legScale c l) * (r' j - r j)).sum := by
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro l _
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← sector .plain, ← sector .alpha]
  ring

theorem valT_sub_gradient {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (c : Coins P) (r r' : Algebra.Vec (Fq P) P.N) (D : ExprT P) :
    valT pp v ⟨c, r'⟩ D - valT pp v ⟨c, r⟩ D =
      ∑ j, (rGrad pp ⟨c, r⟩ D .plain j + rGrad pp ⟨c, r⟩ D .alpha j) *
        (r' j - r j) := by
  classical
  have sector (σ : Sector) :
      ((keys1 P).map fun a => ((legList P).map fun l => ∑ j,
        e1At pp ⟨c, r⟩ a * (D.1 (a, some (.ZeroCoordinate σ l j)) + D.1 (a, some (.totR1 σ l))) *
          (sectorScale c σ * legScale c l) * (r' j - r j)).sum).sum =
      ∑ j, rGrad pp ⟨c, r⟩ D σ j * (r' j - r j) := by
    rw [sum_map_swap]
    simp_rw [sum_map_fin_swap]
    apply Finset.sum_congr rfl
    intro j _
    simp only [rGrad, sum_map_factor]
    apply congrArg (fun z : Fq P => z * (r' j - r j))
    apply congrArg List.sum
    apply List.map_congr_left
    intro l _
    ring
  rw [valT_sub_expanded]
  simp only [List.sum_map_add, sector .plain, sector .alpha, add_mul, Finset.sum_add_distrib]

end Praxis.Proofs.Reduction
