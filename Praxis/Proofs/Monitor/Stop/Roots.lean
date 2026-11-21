import Praxis.Proofs.Monitor.Stop.Coins
import Praxis.Proofs.Monitor.Stop.Sampling
import Praxis.Proofs.Monitor.Stop.LeftPoly
import Praxis.Algebra.BilinearModel.Bilinear.SmallRoots
import Praxis.Enc
import Praxis.Params
import Praxis.Search
import Praxis.Setting

namespace Praxis.Proofs.Monitor

open OracleComp OracleSpec

open Classical

variable {P : Params} [Fact (Nat.Prime P.q)]

noncomputable def gridSet (pp : PublicParams P) : MonVar P → Finset (Fq P)
  | .inl _ => Finset.univ
  | .inr (.inl _) => Finset.univ
  | .inr (.inr s) => scalarSet pp.qap s

def sampleCoords {pp : PublicParams P} (z : AssignSample pp) : MonVar P → Fq P :=
  assignmentCoords (sampleToAssign z)

theorem sampleCoords_mem {pp : PublicParams P} (z : AssignSample pp) :
    sampleCoords z ∈ Fintype.piFinset (gridSet pp) := by
  rw [Fintype.mem_piFinset]
  intro i
  rcases i with i | i | s
  · simp [gridSet]
  · simp [gridSet]
  · exact (validCoins_iff_scalarSet _ _).1 z.1.2 s

def sampleCoordsSearch {pp : PublicParams P} (z : AssignSample pp) :
    (MonVar P → Fq P) × SearchSample P :=
  (sampleCoords z, z.1.1.2.1)

theorem sampleCoordsSearch_injective (pp : PublicParams P) :
    Function.Injective (sampleCoordsSearch (pp := pp)) := by
  intro z z' h
  have h1 : sampleCoords z = sampleCoords z' := congrArg Prod.fst h
  have h2 : z.1.1.2.1 = z'.1.1.2.1 := congrArg Prod.snd h
  obtain ⟨⟨⟨y, r, s⟩, hz⟩, rr⟩ := z
  obtain ⟨⟨⟨y', r', s'⟩, hz'⟩, rr'⟩ := z'
  simp only at h2
  subst h2
  have hy : y = y' := funext fun i => congrFun h1 (.inl i)
  have hrr : rr = rr' := funext fun i => congrFun h1 (.inr (.inl i))
  have hs : s = s' := funext fun a => congrFun h1 (.inr (.inr a))
  subst hy
  subst hrr
  subst hs
  rfl

theorem sampleCoordsSearch_surjective (pp : PublicParams P) (x : MonVar P → Fq P)
    (hx : x ∈ Fintype.piFinset (gridSet pp)) (r : SearchSample P) :
    ∃ z : AssignSample pp, sampleCoordsSearch z = (x, r) := by
  rw [Fintype.mem_piFinset] at hx
  refine ⟨(⟨((fun i => x (.inl i)), r, fun s => x (.inr (.inr s))),
    (validCoins_iff_scalarSet _ _).2 (fun s => hx (.inr (.inr s)))⟩,
    fun i => x (.inr (.inl i))), ?_⟩
  unfold sampleCoordsSearch sampleCoords sampleToAssign assignmentCoords
  refine Prod.ext ?_ rfl
  funext i
  rcases i with i | i | s <;> rfl

theorem card_sample_filter (pp : PublicParams P) (E : (MonVar P → Fq P) → Prop) :
    (Finset.univ.filter (fun z : AssignSample pp => E (sampleCoords z))).card =
      ((Fintype.piFinset (gridSet pp)).filter E).card * Fintype.card (SearchSample P) := by
  rw [← Finset.card_univ (α := SearchSample P), ← Finset.card_product]
  refine Finset.card_bij (fun z _ => sampleCoordsSearch z) ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨sampleCoords_mem z, hz.2⟩, Finset.mem_univ _⟩
  · intro z _ z' _ h
    exact sampleCoordsSearch_injective pp h
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter] at hp
    obtain ⟨z, hz⟩ := sampleCoordsSearch_surjective pp p.1 hp.1.1 p.2
    refine ⟨z, ?_, hz⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : sampleCoords z = p.1 := congrArg Prod.fst hz
    rw [this]
    exact hp.1.2

theorem card_sample (pp : PublicParams P) :
    Fintype.card (AssignSample pp) =
      (Fintype.piFinset (gridSet pp)).card * Fintype.card (SearchSample P) := by
  have h := card_sample_filter pp (fun _ => True)
  simpa using h

theorem root_count_bound (pp : PublicParams P) (m : ℕ) (hm : 0 < m)
    (hmin : ∀ s, m ≤ (scalarSet pp.qap s).card) (p : MonPoly P) (hp : p ≠ 0) :
    (((Fintype.piFinset (gridSet pp)).filter
        (fun x => MvPolynomial.eval x p = 0)).card : ℚ≥0) /
      ((Fintype.piFinset (gridSet pp)).card : ℚ≥0) ≤ (p.totalDegree : ℚ≥0) / m := by
  let n := Fintype.card (MonVar P)
  let e : MonVar P ≃ Fin n := Fintype.equivFin (MonVar P)
  let p' : MvPolynomial (Fin n) (Fq P) := MvPolynomial.rename e p
  have hp' : p' ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.rename_injective e e.injective) (by simpa [p'] using h)
  have hdeg : p'.totalDegree ≤ p.totalDegree := MvPolynomial.totalDegree_rename_le e p
  let S' : Fin n → Finset (Fq P) := fun i => gridSet pp (e.symm i)
  have hmq : m ≤ P.q := by
    have h1 := hmin .tau
    have h2 : (scalarSet pp.qap .tau).card ≤ Fintype.card (Fq P) :=
      Finset.card_le_univ _
    rw [ZMod.card] at h2
    exact h1.trans h2
  have hS' : ∀ i, m ≤ (S' i).card := by
    intro i
    simp only [S']
    rcases e.symm i with j | j | s
    · simpa only [gridSet, Finset.card_univ, ZMod.card] using hmq
    · simpa only [gridSet, Finset.card_univ, ZMod.card] using hmq
    · exact hmin s
  have hmain := Algebra.Bilinear.product_root_count p' hp' S' m hm hS'
  have hnum : ((Fintype.piFinset S').filter (fun x => MvPolynomial.eval x p' = 0)).card =
      ((Fintype.piFinset (gridSet pp)).filter (fun y => MvPolynomial.eval y p = 0)).card := by
    apply Finset.card_nbij' (fun x => fun a => x (e a)) (fun y => fun i => y (e.symm i))
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
      rw [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun a => ?_, ?_⟩
      · simpa [S'] using hx.1 (e a)
      · have := hx.2
        simpa [p', MvPolynomial.eval_rename, Function.comp_def] using this
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hy
      rw [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => by simpa [S'] using hy.1 (e.symm i), ?_⟩
      have := hy.2
      simpa [p', MvPolynomial.eval_rename, Function.comp_def] using this
    · intro x _
      funext i
      simp
    · intro y _
      funext a
      simp
  have hden : ∏ i, ((S' i).card : ℚ≥0) = ((Fintype.piFinset (gridSet pp)).card : ℚ≥0) := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
    exact Equiv.prod_comp e.symm (fun j => ((gridSet pp j).card : ℚ≥0))
  rw [hnum, hden] at hmain
  refine hmain.trans ?_
  have : (p'.totalDegree : ℚ≥0) ≤ p.totalDegree := by exact_mod_cast hdeg
  gcongr

theorem assign_root_prob (pp : PublicParams P) [SampleableType (AssignSample pp)]
    [Nonempty (ValidCoin pp)] (m : ℕ) (hm : 0 < m) (hmin : ∀ s, m ≤ (scalarSet pp.qap s).card)
    (p : MonPoly P) (hp : p ≠ 0) :
    Pr[fun z : AssignSample pp => MvPolynomial.eval (sampleCoords z) p = 0 |
      $ᵗ (AssignSample pp)] ≤ (p.totalDegree : ENNReal) / m := by
  have hne : (Fintype.piFinset (gridSet pp)).Nonempty := by
    rw [Fintype.piFinset_nonempty]
    intro j
    rcases j with j | j | s
    · exact ⟨0, by simp [gridSet]⟩
    · exact ⟨0, by simp [gridSet]⟩
    · exact Finset.card_pos.1 (lt_of_lt_of_le hm (hmin s))
  have hB : 0 < (Fintype.piFinset (gridSet pp)).card := Finset.card_pos.2 hne
  have hk : 0 < Fintype.card (SearchSample P) := by
    obtain ⟨c⟩ := (inferInstance : Nonempty (ValidCoin pp))
    exact Fintype.card_pos_iff.2 ⟨c.1.2.1⟩
  have h := root_count_bound pp m hm hmin p hp
  set A := ((Fintype.piFinset (gridSet pp)).filter
    (fun x => MvPolynomial.eval x p = 0)).card with hA
  set B := (Fintype.piFinset (gridSet pp)).card with hBdef
  set k := Fintype.card (SearchSample P) with hkdef
  have hn : A * m ≤ p.totalDegree * B := by
    have := (div_le_div_iff₀ (show (0 : ℚ≥0) < (B : ℚ≥0) by exact_mod_cast hB)
      (show (0 : ℚ≥0) < (m : ℚ≥0) by exact_mod_cast hm)).mp h
    exact_mod_cast this
  have hf : (Finset.univ.filter
      (fun z : AssignSample pp => MvPolynomial.eval (sampleCoords z) p = 0)).card = A * k := by
    convert card_sample_filter pp (fun x => MvPolynomial.eval x p = 0)
  rw [probEvent_uniformSample, hf, card_sample pp]
  have hBk : 0 < B * k := Nat.mul_pos hB hk
  have hn' : A * k * m ≤ p.totalDegree * (B * k) := by
    calc A * k * m = A * m * k := by ring
      _ ≤ p.totalDegree * B * k := Nat.mul_le_mul_right _ hn
      _ = p.totalDegree * (B * k) := by ring
  have hmE : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hsE : ((B * k : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast hBk.ne'
  have hnE : ((A * k : ℕ) : ENNReal) * m ≤ (p.totalDegree : ENNReal) * ((B * k : ℕ) : ENNReal) := by
    exact_mod_cast hn'
  apply (ENNReal.div_le_iff hsE (ENNReal.natCast_ne_top _)).mpr
  have hc : (p.totalDegree : ENNReal) / m * ((B * k : ℕ) : ENNReal) =
      ((p.totalDegree : ENNReal) * ((B * k : ℕ) : ENNReal)) / m := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ring
  rw [hc]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hmE) (Or.inl (ENNReal.natCast_ne_top m))).mpr hnE

end Praxis.Proofs.Monitor
