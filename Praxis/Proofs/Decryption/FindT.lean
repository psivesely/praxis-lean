import Praxis.Proofs.Decryption.Range
import Praxis.Dec
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Setting

set_option maxRecDepth 4096

namespace Praxis.Proofs.Decryption

private theorem mem_search (b : ℕ) (z : ℤ) :
    z ∈ (List.range (2 * b + 1)).map (fun (k : ℕ) => (k : ℤ) - b) ↔
      -(b : ℤ) ≤ z ∧ z ≤ b := by
  constructor
  · intro hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    have hk' := List.mem_range.mp hk
    constructor <;> omega
  · intro hz
    apply List.mem_map.mpr
    refine ⟨(z + b).toNat, ?_, ?_⟩
    · apply List.mem_range.mpr
      have hn : 0 ≤ z + (b : ℤ) := by omega
      have he := Int.toNat_of_nonneg hn
      omega
    · have hn : 0 ≤ z + (b : ℤ) := by omega
      have he := Int.toNat_of_nonneg hn
      omega

private theorem findT_general (P : Params) [Fact (Nat.Prime P.q)]
    {G : Type*} [AddCommGroup G] [Module (Fq P) G] [DecidableEq G] (H' Ψ : G)
    (hΨ : Ψ ≠ 0) (t : ℤ) (ht : |t| ≤ (P.tBound : ℤ)) (h : H' = (t : Fq P) • Ψ)
    (hq : 2 * P.tBound + 1 < P.q) : findT (P := P) H' Ψ = some t := by
  have hq' : (2 * (P.tBound : ℤ) + 1) < (P.q : ℤ) := by exact_mod_cast hq
  have ht' := abs_le.mp ht
  let L := (List.range (2 * P.tBound + 1)).map fun (k : ℕ) => (k : ℤ) - P.tBound
  have hm : t ∈ L := (mem_search P.tBound t).mpr ht'
  have hex : (L.find? fun (z : ℤ) => decide (H' = (z : Fq P) • Ψ)).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨t, hm, by simpa using h⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hex
  have ham : a ∈ L := List.mem_of_find?_eq_some ha
  have hap : H' = (a : Fq P) • Ψ := by
    simpa using List.find?_some ha
  have hab : (a : Fq P) = (t : Fq P) := by
    apply (smul_left_injective (Fq P) hΨ)
    exact hap.symm.trans h
  have hd : (P.q : ℤ) ∣ t - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a t P.q).mp hab
  have habounds := (mem_search P.tBound a).mp ham
  have hdiff : |t - a| < (P.q : ℤ) := by
    rw [abs_lt]
    omega
  have hdiff' : (t - a).natAbs < (P.q : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    rw [Int.abs_eq_natAbs] at hdiff
    exact_mod_cast hdiff
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hdiff'
  have : a = t := by omega
  subst a
  unfold findT
  dsimp only [L] at ha
  change (((List.range (2 * P.tBound + 1)).flatMap (fun (k : ℕ) => [(k : ℤ)])).map
    (fun k => k - (P.tBound : ℤ))).find? (fun (z : ℤ) => decide (H' = (z : Fq P) • Ψ)) = some t
  rw [← List.map_eq_flatMap, List.map_map]
  exact ha

theorem findT_spec {G : Type*} [AddCommGroup G] [Module (Fq P0) G] [DecidableEq G] (H' Ψ : G)
    (hΨ : Ψ ≠ 0) (t : ℤ) (ht : |t| ≤ (P0.tBound : ℤ)) (h : H' = ((t : ℤ) : Fq P0) • Ψ) :
    findT (P := P0) H' Ψ = some t := by
  exact findT_general P0 H' Ψ hΨ t ht h (by decide)

end Praxis.Proofs.Decryption
