import Praxis.Proofs.Basic
import Praxis.Enc
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.GroupModel

open Classical

variable {P : Params} [Fact (Nat.Prime P.q)]

private theorem singleton_sum {I F : Type} [DecidableEq I] [Semiring F]
    (xs : List I) (hnd : xs.Nodup) (a : I) (ha : a ∈ xs) (v : I → F) :
    (xs.map fun b => (Pi.single a (1 : F) : I → F) b * v b).sum = v a := by
  rw [← List.sum_toFinset _ hnd]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [Pi.single_apply, hba, Ne.symm hba]
  · intro hn
    exact (hn (List.mem_toFinset.mpr ha)).elim

theorem val1_single (pp : PublicParams P) (ω : Assign P) (a : Option (G1Idx P))
    (hnd : (keys1 P).Nodup) (ha : a ∈ keys1 P) :
    val1 pp ω (Pi.single a 1) = e1At pp ω a := by
  exact singleton_sum (keys1 P) hnd a ha (e1At pp ω)

theorem val2_single (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (a : Option (G2Idx P))
    (hnd : (keys2 P).Nodup) (ha : a ∈ keys2 P) :
    val2 pp v ω (Pi.single a 1) = e2At pp v ω a := by
  exact singleton_sum (keys2 P) hnd a ha (e2At pp v ω)

theorem e2At_ofCoins (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (c : Coins P) (a : G2Idx P) :
    e2At pp v (Assign.ofCoins c) (some a) = g2Exp pp v c a := by
  cases a <;> simp [e2At, g2Exp, Assign.ofCoins, r1ExpAt, r1Exp, H1]

theorem valT_init (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (a : Option Unit) :
    valT pp v ω (gtInit a) = if a = none then 1 else gtExp pp ω.coins := by
  cases a with
  | none => simp [valT, gtInit, keys1, keys2, e1At, e2At, Pi.single_apply, Function.comp_def]
  | some x =>
    cases x
    simp [valT, gtInit, keys1, keys2, Pi.single_apply, Function.comp_def]

theorem g1_initial_witness (pp : PublicParams P) (a b : Option (G1Idx P))
    (hnd : (keys1 P).Nodup) (ha : a ∈ keys1 P) (hb : b ∈ keys1 P)
    (hne : ¬ FormalEq1 pp (Pi.single a 1) (Pi.single b 1))
    (r : Algebra.Vec (Fq P) P.N) :
    ∃ c : Coins P, ValidCoins pp.qap c ∧ e1At pp ⟨c, r⟩ a ≠ e1At pp ⟨c, r⟩ b := by
  classical
  simp only [FormalEq1, not_forall, _root_.not_imp] at hne
  obtain ⟨ω, hv, hne⟩ := hne
  rw [val1_single pp ω a hnd ha, val1_single pp ω b hnd hb] at hne
  exact ⟨ω.coins, hv, hne⟩

theorem gt_initial_witness (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (a b : Option Unit) (hne : ¬ FormalEqT pp v (gtInit a) (gtInit b))
    (r : Algebra.Vec (Fq P) P.N) :
    ∃ c : Coins P, ValidCoins pp.qap c ∧
      valT pp v ⟨c, r⟩ (gtInit a) ≠ valT pp v ⟨c, r⟩ (gtInit b) := by
  classical
  simp only [FormalEqT, not_forall, _root_.not_imp] at hne
  obtain ⟨ω, hv, hne⟩ := hne
  refine ⟨ω.coins, hv, ?_⟩
  simpa only [valT_init] using hne

end Praxis.Proofs.GroupModel
