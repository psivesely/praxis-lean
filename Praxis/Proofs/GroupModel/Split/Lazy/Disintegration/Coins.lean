import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Relation
import Praxis.Search

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration

open Classical

namespace CoinLaw

open Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable {ch : AdmissibleChoice P0} {S : Relation P0}

private def coinSearchEquiv (pp : PublicParams P0) (s : SearchSample P0) :
    CoinDomain pp ≃ SearchSample P0 × {c : CoinDomain pp // c.val.2.1 = s} where
  toFun c := (c.val.2.1, ⟨⟨(c.val.1, s, c.val.2.2), c.property⟩, rfl⟩)
  invFun z := ⟨(z.2.val.val.1, z.1, z.2.val.val.2.2), z.2.val.property⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv z := by
    rcases z with ⟨r, ⟨⟨⟨y, t, v⟩, hv⟩, ht⟩⟩
    dsimp at ht
    subst t
    rfl

lemma coinLaw_search (s : SearchSample P0) :
    (∑' c : CoinDomain (ppOf ch S),
      if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] else 0) = Pr[= s | searchLaw] := by
  let pp := ppOf ch S
  let C := CoinDomain pp
  let R := {c : C // c.val.2.1 = s}
  let e := coinSearchEquiv pp s
  letI : Nonempty R := by
    obtain ⟨c⟩ := (inferInstance : Nonempty C)
    exact ⟨⟨⟨(c.val.1, s, c.val.2.2), c.property⟩, rfl⟩⟩
  letI := SampleableType.ofFintype C
  letI := SampleableType.ofFintype R
  letI := SampleableType.ofFintype (SearchSample P0)
  letI := SampleableType.ofFintype (SearchSample P0 × R)
  have he : evalSPMF (e <$> (coinLaw pp)) = evalSPMF ($ᵗ (SearchSample P0 × R)) := by
    apply evalSPMF_ext
    exact probOutput_map_bijective_uniform_cross C e e.bijective
  have hfst := evalSPMF_map_fst_uniformSample_prod (α := SearchSample P0) (β := R)
  have hmap : evalSPMF ((fun c : C => c.val.2.1) <$> coinLaw pp) = evalSPMF searchLaw := by
    calc
      _ = evalSPMF (Prod.fst <$> (e <$> coinLaw pp)) := by simp only [Functor.map_map]; rfl
      _ = evalSPMF (Prod.fst <$> ($ᵗ (SearchSample P0 × R))) :=
        evalSPMF_map_eq_of_evalSPMF_eq he _
      _ = evalSPMF searchLaw := hfst
  have hm := congrArg (fun d => d s) hmap
  change Pr[= s | (fun c : C => c.val.2.1) <$> coinLaw pp] = Pr[= s | searchLaw] at hm
  rw [probOutput_map_eq_tsum_ite] at hm
  simpa only [eq_comm] using hm

lemma coinLaw_resample (s : SearchSample P0) (c' : CoinDomain (ppOf ch S)) :
    (∑' c : CoinDomain (ppOf ch S), if c.val.2.1 = s then
        Pr[= c | coinLaw (ppOf ch S)] * Pr[= c' | resample (ppOf ch S) c] else 0) =
      Pr[= s | searchLaw] * Pr[= c' | coinLaw (ppOf ch S)] := by
  classical
  letI : DecidableEq (CoinDomain (ppOf ch S)) := Classical.decEq _
  let c₀ : CoinDomain (ppOf ch S) := ⟨(c'.val.1, s, c'.val.2.2), c'.property⟩
  have hinj (c : CoinDomain (ppOf ch S)) : Function.Injective
      (fun r => (⟨(c.val.1, r, c.val.2.2), c.property⟩ : CoinDomain (ppOf ch S))) := by
    intro r t h
    exact congrArg (fun d => d.val.2.1) h
  have hmass : Pr[= c₀ | coinLaw (ppOf ch S)] = Pr[= c' | coinLaw (ppOf ch S)] := by
    simp only [coinLaw, probOutput_uniformSample]
  have hkernel : Pr[= c' | resample (ppOf ch S) c₀] = Pr[= c'.val.2.1 | searchLaw] := by
    exact probOutput_map_injective searchLaw (hinj c₀) c'.val.2.1
  have hterm (c : CoinDomain (ppOf ch S)) :
      (if c.val.2.1 = s then Pr[= c | coinLaw (ppOf ch S)] *
        Pr[= c' | resample (ppOf ch S) c] else 0) =
      if c = c₀ then Pr[= c' | coinLaw (ppOf ch S)] * Pr[= c'.val.2.1 | searchLaw] else 0 := by
    by_cases hc : c = c₀
    · subst c
      simp only [c₀, if_pos rfl, hmass, hkernel]
    · rw [if_neg hc]
      by_cases hs : c.val.2.1 = s
      · rw [if_pos hs]
        have hz : Pr[= c' | resample (ppOf ch S) c] = 0 := by
          rw [probOutput_eq_zero_iff, resample, support_map]
          rintro ⟨r, _, he⟩
          apply hc
          apply Subtype.ext
          have hy := congrArg (fun d : CoinDomain (ppOf ch S) => d.val.1) he
          have hv := congrArg (fun d : CoinDomain (ppOf ch S) => d.val.2.2) he
          exact Prod.ext hy (Prod.ext hs hv)
        rw [hz, mul_zero]
      · rw [if_neg hs]
  simp_rw [hterm]
  rw [tsum_eq_single c₀ (fun c hc => if_neg hc), if_pos rfl]
  have hs : Pr[= c'.val.2.1 | searchLaw] = Pr[= s | searchLaw] := by
    simp only [searchLaw, probOutput_uniformSample]
  rw [hs, mul_comm]

end CoinLaw

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration
