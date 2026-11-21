import Praxis.Algebra.Trans.AlgModel

open scoped BigOperators

namespace Praxis.Algebra.Trans

variable {R : Type*} [CommRing R]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem det_mul_column_expansion {r : ℕ}
    (A : Matrix (Fin r) ι R) (B : Matrix ι (Fin r) R) :
    Matrix.det (A * B) = ∑ f : Fin r → ι,
      Matrix.det (A.submatrix id f) * ∏ j, B (f j) j := by
  classical
  calc
    Matrix.det (A * B) = ∑ f : Fin r → ι, ∑ p : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign p : ℤ) : R) * ∏ j, A (p j) (f j) * B (f j) j := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
        Finset.sum_mul, Finset.prod_mul_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring

omit [Fintype ι] [DecidableEq ι] in
private theorem det_submatrix_zero_of_not_injective {r : ℕ}
    (A : Matrix (Fin r) ι R) (f : Fin r → ι) (hf : ¬ Function.Injective f) :
    Matrix.det (A.submatrix id f) = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])

private theorem sum_row_orderings [LinearOrder ι] {r : ℕ}
    (I : Finset ι) (hI : I.card = r) (F : (Fin r → ι) → R) :
    (∑ f ∈ (Finset.univ.filter (fun f : Fin r → ι => Function.Injective f)).filter
      (fun f => Finset.univ.image f = I), F f) =
    ∑ p : Equiv.Perm (Fin r), F (fun j => I.orderEmbOfFin hI (p j)) := by
  classical
  symm
  apply Finset.sum_bij (fun p _ => fun j => I.orderEmbOfFin hI (p j))
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact (I.orderEmbOfFin hI).injective.comp p.injective
    · change Finset.univ.image ((I.orderEmbOfFin hI) ∘ p) = I
      rw [← Finset.image_image, Finset.image_univ_of_surjective p.surjective]
      apply Finset.coe_injective
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Finset.range_orderEmbOfFin]
  · intro p _ q _ hpq
    apply Equiv.ext
    intro j
    exact (I.orderEmbOfFin hI).injective (congrFun hpq j)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hmem (j : Fin r) : f j ∈ I := by
      rw [← hf.2]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    let q : Fin r → Fin r := fun j => (I.orderIsoOfFin hI).symm ⟨f j, hmem j⟩
    have hq : Function.Injective q := by
      intro j k hjk
      apply hf.1
      have hh := congrArg (fun x => ((I.orderIsoOfFin hI) x : ι)) hjk
      simpa [q] using hh
    let p : Equiv.Perm (Fin r) := Equiv.ofBijective q
      (Finite.injective_iff_bijective.mp hq)
    refine ⟨p, Finset.mem_univ _, ?_⟩
    funext j
    change ((I.orderIsoOfFin hI) ((I.orderIsoOfFin hI).symm ⟨f j, hmem j⟩) : ι) = f j
    simp
  · intro p _
    rfl

theorem det_mul_subsets [LinearOrder ι] {r : ℕ}
    (A : Matrix (Fin r) ι R) (B : Matrix ι (Fin r) R) :
    Matrix.det (A * B) =
      ∑ I ∈ Finset.univ.powersetCard r,
        if hI : I.card = r then
          Matrix.det (A.submatrix id (I.orderEmbOfFin hI)) *
            Matrix.det (B.submatrix (I.orderEmbOfFin hI) id)
        else 0 := by
  classical
  let F : (Fin r → ι) → R := fun f =>
    Matrix.det (A.submatrix id f) * ∏ j, B (f j) j
  rw [det_mul_column_expansion]
  change (∑ f, F f) = _
  have hfilter : (∑ f, F f) = ∑ f with Function.Injective f, F f := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hn : ¬ Function.Injective f := by simpa using hf
    simp [F, det_submatrix_zero_of_not_injective A f hn]
  rw [hfilter]
  have hmaps (f : Fin r → ι)
      (hf : f ∈ Finset.univ.filter (fun f : Fin r → ι => Function.Injective f)) :
      Finset.univ.image f ∈ Finset.univ.powersetCard r := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hf).2]
    simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  apply Finset.sum_congr rfl
  intro I hI
  have hc : I.card = r := (Finset.mem_powersetCard.mp hI).2
  rw [dif_pos hc, sum_row_orderings I hc F]
  let e := I.orderEmbOfFin hc
  have hdet (p : Equiv.Perm (Fin r)) :
      Matrix.det (A.submatrix id (fun j => e (p j))) =
        ((Equiv.Perm.sign p : ℤ) : R) * Matrix.det (A.submatrix id e) := by
    exact Matrix.det_permute' p (A.submatrix id e)
  change (∑ p : Equiv.Perm (Fin r),
    Matrix.det (A.submatrix id (fun j => e (p j))) * ∏ j, B (e (p j)) j) = _
  simp_rw [hdet]
  rw [Matrix.det_apply' (B.submatrix (I.orderEmbOfFin hc) id), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Matrix.submatrix_apply, id_eq]
  ring

theorem weightedGram_det [LinearOrder ι] {r : ℕ}
    (B : Matrix ι (Fin r) R) (sigma : ι → R) :
    Matrix.det (weightedGram B sigma) =
      ∑ I ∈ Finset.univ.powersetCard r,
        rowMinor B I ^ 2 * ∏ i ∈ I, sigma i ^ 2 := by
  classical
  unfold weightedGram
  rw [det_mul_subsets]
  apply Finset.sum_congr rfl
  intro I hI
  have hc : I.card = r := (Finset.mem_powersetCard.mp hI).2
  rw [dif_pos hc, rowMinor, dif_pos hc]
  let e := I.orderEmbOfFin hc
  have hmatrix :
      (B.transpose * Matrix.diagonal (fun i => sigma i ^ 2)).submatrix id e =
        (B.submatrix e id).transpose * Matrix.diagonal (fun j => sigma (e j) ^ 2) := by
    ext i j
    simp
  have hprod : (∏ j, sigma (e j) ^ 2) = ∏ i ∈ I, sigma i ^ 2 := by
    calc
      _ = ∏ i ∈ Finset.univ.image e, sigma i ^ 2 := by
        rw [Finset.prod_image]
        exact fun _ _ _ _ h => e.injective h
      _ = _ := by
        have he : Finset.univ.image e = I := by
          apply Finset.coe_injective
          simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
            e, Finset.range_orderEmbOfFin]
        rw [he]
  change Matrix.det ((B.transpose * Matrix.diagonal (fun i => sigma i ^ 2)).submatrix id e) *
    Matrix.det (B.submatrix e id) = Matrix.det (B.submatrix e id) ^ 2 * _
  rw [hmatrix, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hprod]
  ring

theorem cauchyBinet3 [LinearOrder ι] {r : ℕ}
    (B : Matrix ι (Fin r) R) (sigma : ι → R) : CauchyBinet3 B sigma := by
  intro _
  exact weightedGram_det B sigma

end Praxis.Algebra.Trans
