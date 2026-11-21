import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Probability.FiniteLaw
import Praxis.Algebra.DifferenceLattice.Saturation
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

namespace Praxis.Algebra.Prefix

open Finset Module

open Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Prefix.Definitions

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairing (w : ι → ℤ) : (ι → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ i, x i * w i
  map_add' := by intro x y; simp [add_mul, sum_add_distrib]
  map_smul' := by intro a x; simp [mul_assoc, mul_sum]

omit [Fintype ι] [DecidableEq ι] in

theorem range_le_ker_iff {d : ℕ} (B : Matrix ι (Fin d) ℤ)
    (f : (ι → ℤ) →ₗ[ℤ] ℤ) :
    B.mulVecLin.range ≤ f.ker ↔ ∀ j, f (B.col j) = 0 := by
  rw [Matrix.range_mulVecLin, Submodule.span_le]
  simp [Set.range_subset_iff]

theorem saturation_le_ker_iff (M : Submodule ℤ (ι → ℤ))
    (f : (ι → ℤ) →ₗ[ℤ] ℤ) :
    Algebra.Lattice.saturation M ≤ f.ker ↔ M ≤ f.ker := by
  constructor
  · intro h
    exact (Algebra.Lattice.le_saturation M).trans h
  · intro h x hx
    obtain ⟨a, ha, hx⟩ := hx
    have hz := h hx
    change f (a • x) = 0 at hz
    rw [map_smul] at hz
    exact (mul_eq_zero.mp hz).resolve_left ha

theorem basis_matrix_range {d : ℕ} (L : IntLat ι d) :
    L.matrix.mulVecLin.range = L.carrier := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have h := (∑ j, a j • L.basis j).property
    convert h using 1
    ext i
    simp [IntLat.matrix, Matrix.mulVec, dotProduct,
      mul_comm]
  · intro hx
    refine ⟨L.basis.equivFun ⟨x, hx⟩, ?_⟩
    ext i
    exact Algebra.Lattice.basis_eval L.carrier L.basis ⟨x, hx⟩ i

theorem primitive_image_eq_iff {d : ℕ} (G : ι → ℕ)
    (B : Matrix ι (Fin d) ℤ) (L : IntLat ι d)
    (hL : L.carrier = Algebra.Lattice.saturation B.mulVecLin.range)
    (r s : Grid G) :
    imageZ G L.matrix r = imageZ G L.matrix s ↔ imageZ G B r = imageZ G B s := by
  let f := pairing (fun i => (r i : ℤ) - (s i : ℤ))
  have he (A : Matrix ι (Fin d) ℤ) :
      imageZ G A r = imageZ G A s ↔ A.mulVecLin.range ≤ f.ker := by
    rw [range_le_ker_iff]
    constructor
    · intro h j
      have hj := congrFun h j
      change ∑ i, A i j * ((r i : ℤ) - (s i : ℤ)) = 0
      rw [show (∑ i, A i j * ((r i : ℤ) - (s i : ℤ))) =
        (∑ i, A i j * (r i : ℤ)) - ∑ i, A i j * (s i : ℤ) by
          simp [mul_sub, sum_sub_distrib]]
      exact sub_eq_zero.mpr hj
    · intro h
      ext j
      have hj := h j
      change ∑ i, A i j * ((r i : ℤ) - (s i : ℤ)) = 0 at hj
      change (∑ i, A i j * (r i : ℤ)) = ∑ i, A i j * (s i : ℤ)
      simpa [mul_sub, sum_sub_distrib, sub_eq_zero] using hj
  rw [he, basis_matrix_range, hL, saturation_le_ker_iff, ← he]

theorem mass_le_of_fibres {Ω T Q : Type*} [Fintype Ω] [Nonempty Ω]
    [Nonempty T] (f : Ω → T) (g : Ω → Q)
    (h : ∀ x y, f x = f y → g x = g y) :
    Algebra.FiniteProbability.atomMass f ≤ Algebra.FiniteProbability.atomMass g := by
  classical
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  by_cases ht : ∃ x, f x = t
  · obtain ⟨x, rfl⟩ := ht
    exact (Algebra.FiniteProbability.pointProb_mono f g (f x) (g x)
      (fun y hy => h y x hy)).trans (Algebra.FiniteProbability.pointProb_le_mass g (g x))
  · have hn : ∀ x, f x ≠ t := by simpa using ht
    have hz : Algebra.FiniteProbability.pointProb f t = 0 := by
      simp [Algebra.FiniteProbability.pointProb_eq_sum, hn]
    rw [hz]
    exact Algebra.FiniteProbability.atomMass_nonneg g

theorem primitive_mass_eq {d : ℕ} (G : ι → ℕ) (hG : ∀ i, 0 < G i)
    (B : Matrix ι (Fin d) ℤ) (L : IntLat ι d)
    (hL : L.carrier = Algebra.Lattice.saturation B.mulVecLin.range) :
    L.mZ G = mass G (imageZ G B) := by
  let : Nonempty (Grid G) := ⟨fun i => ⟨0, hG i⟩⟩
  apply le_antisymm
  · exact mass_le_of_fibres _ _ (fun r s h =>
      (primitive_image_eq_iff G B L hL r s).mp h)
  · exact mass_le_of_fibres _ _ (fun r s h =>
      (primitive_image_eq_iff G B L hL r s).mpr h)

theorem pointProb_precomp_equiv {Ω Δ T : Type*} [Fintype Ω] [Fintype Δ]
    (e : Ω ≃ Δ) (f : Δ → T) (t : T) :
    Algebra.FiniteProbability.pointProb (f ∘ e) t = Algebra.FiniteProbability.pointProb f t := by
  classical
  rw [Algebra.FiniteProbability.pointProb_eq_sum, Algebra.FiniteProbability.pointProb_eq_sum,
    Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun x => if f x = t then (1 : ℝ) else 0)

theorem mass_precomp_equiv {Ω Δ T : Type*} [Fintype Ω] [Fintype Δ]
    (e : Ω ≃ Δ) (f : Δ → T) :
    Algebra.FiniteProbability.atomMass (f ∘ e) = Algebra.FiniteProbability.atomMass f := by
  unfold Algebra.FiniteProbability.atomMass
  congr 1
  funext t
  exact pointProb_precomp_equiv e f t

theorem mass_add_independent {X Y T : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] [AddGroup T] (f : Y → T) (a : X → T) :
    Algebra.FiniteProbability.atomMass (fun xy : X × Y => f xy.2 + a xy.1) ≤
      Algebra.FiniteProbability.atomMass f := by
  classical
  apply Algebra.FiniteProbability.atomMass_le
  intro t
  rw [Algebra.FiniteProbability.pointProb_prod]
  have hb (x : X) : Algebra.FiniteProbability.atomMass (fun y => f y + a x) ≤
      Algebra.FiniteProbability.atomMass f :=
    mass_le_of_fibres _ _ (fun _ _ h => add_right_cancel h)
  calc
    (∑ x : X, Algebra.FiniteProbability.pointProb (fun y => f y + a x) t) /
        (Fintype.card X : ℝ) ≤
        (∑ _x : X, Algebra.FiniteProbability.atomMass f) / (Fintype.card X : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun x _ =>
        (Algebra.FiniteProbability.pointProb_le_mass _ t).trans (hb x))
    _ = Algebra.FiniteProbability.atomMass f := by
      simp [Fintype.card_ne_zero]

theorem image_mass_mono {d k : ℕ} (G : Fin (k+1) → ℕ)
    (hG : ∀ i, 0 < G i) (B : Matrix (Fin (k+1)) (Fin d) ℤ) :
    mass G (imageZ G B) ≤
      mass (fun i : Fin k => G i.castSucc)
        (imageZ (fun i : Fin k => G i.castSucc) (B.submatrix Fin.castSucc id)) := by
  let e := Fin.snocEquiv (fun i => Fin (G i))
  let f := imageZ (fun i : Fin k => G i.castSucc) (B.submatrix Fin.castSucc id)
  let a := fun x : Fin (G (Fin.last k)) => fun j : Fin d =>
    B (Fin.last k) j * (x : ℤ)
  let : Nonempty (Fin (G (Fin.last k))) := ⟨⟨0, hG _⟩⟩
  let : Nonempty (Grid (fun i : Fin k => G i.castSucc)) :=
    ⟨fun i => ⟨0, hG _⟩⟩
  have he : imageZ G B ∘ e = fun xy => f xy.2 + a xy.1 := by
    funext xy j
    change (∑ i, B i j * ((e xy i : ℕ) : ℤ)) = _
    rw [Fin.sum_univ_castSucc]
    simp [e, Fin.snocEquiv, f, a, imageZ, Matrix.submatrix]
  change Algebra.FiniteProbability.atomMass _ ≤ Algebra.FiniteProbability.atomMass f
  rw [← mass_precomp_equiv e (imageZ G B), he]
  exact mass_add_independent f a

theorem step_coord_castSucc {d n k : ℕ} (P : PivotFirstStep d n k) (i : Fin k) :
    P.next.coord i.castSucc = P.old.coord i := by
  simp [PivotFirstPrefix.coord, P.same_order]

theorem step_matrix_init {d n k : ℕ} (P : PivotFirstStep d n k) :
    P.next.matrix.submatrix Fin.castSucc id = P.old.matrix := by
  ext i j
  change P.next.original.matrix (P.next.coord i.castSucc) j =
    P.old.original.matrix (P.old.coord i) j
  rw [P.same_original, step_coord_castSucc]

theorem step_grids_init {d n k : ℕ} (P : PivotFirstStep d n k) :
    (fun i : Fin k => P.next.grids P.grids i.castSucc) = P.old.grids P.grids := by
  funext i
  change P.grids (P.next.coord i.castSucc) = P.grids (P.old.coord i)
  rw [step_coord_castSucc]

theorem prefix_mass_mono {d n k : ℕ} (P : PivotFirstStep d n k) :
    PrefixMassMono P := by
  unfold PrefixMassMono
  rw [primitive_mass_eq (P.next.grids P.grids)
      (fun i => P.grids_pos (P.next.coord i)) P.next.matrix
      P.next.primitive P.next.primitive_eq,
    primitive_mass_eq (P.old.grids P.grids)
      (fun i => P.grids_pos (P.old.coord i)) P.old.matrix
      P.old.primitive P.old.primitive_eq]
  have h := image_mass_mono (P.next.grids P.grids)
    (fun i => P.grids_pos (P.next.coord i)) P.next.matrix
  rwa [step_matrix_init, step_grids_init] at h

end Praxis.Algebra.Prefix
