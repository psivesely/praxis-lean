import Praxis.Proofs.Basic
import VCVio.OracleComp.Constructions.SampleableType
import Praxis.Forms
import Praxis.Games
import Praxis.Params

namespace Praxis.Proofs.Reduction

open OracleComp

variable {P : Params}

theorem formIndexList_complete (i : FormIndex P) : i ∈ formIndexList P := by
  rcases i with ⟨ρ, j⟩
  simp only [formIndexList, List.mem_flatMap, List.mem_finRange, true_and]
  refine ⟨ρ, ?_⟩
  cases j with
  | none => simp
  | some j => simp

theorem reconstruct_forms (B : FormMatrix P) :
    (fun i => ((((formIndexList P).map fun j => (j, B j)).find?
      fun e => decide (e.1 = i)).map Prod.snd).getD 0) = B := by
  classical
  funext i
  generalize h : ((formIndexList P).map fun j => (j, B j)).find?
      (fun e => decide (e.1 = i)) = r
  cases r with
  | none =>
    have hn := List.find?_eq_none.mp h
    have hm : (i, B i) ∈ (formIndexList P).map (fun j => (j, B j)) :=
      List.mem_map.mpr ⟨i, formIndexList_complete i, rfl⟩
    simpa using hn (i, B i) hm
  | some x =>
    have hx := List.find?_some h
    have hm := List.mem_of_find?_eq_some h
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
    simp only [decide_eq_true_eq] at hx
    subst j
    rfl

theorem formIndexList_nodup : (formIndexList P).Nodup := by
  have hc : (none :: (List.finRange P.cols).map some).Nodup := by
    simp only [List.nodup_cons, List.mem_map, reduceCtorEq, exists_const, not_false_eq_true,
      true_and, List.nodup_map_iff (Option.some_injective _)]
    exact ⟨by simp, List.nodup_finRange _⟩
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    exact hc.map (fun a b h => congrArg Prod.snd h)
  · apply (List.nodup_finRange P.rows).imp
    intro a b hab x ha hb
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, _, h⟩ := List.mem_map.mp hb
    exact hab (congrArg Prod.fst h).symm

theorem chalOf_formsOfChallenge [Fact (1 < P.q)] (hd : P.d ≠ 0)
    (chal : MSISChallenge P hd) (star : Fin P.rows → Rq P) :
    chalOf hd (formsOfChallenge P hd chal star) = chal := by
  funext ρ j
  simp [chalOf, formsOfChallenge]

theorem formsOfChallenge_chalOf [Fact (1 < P.q)] (hd : P.d ≠ 0)
    (forms : FormMatrix P) :
    formsOfChallenge P hd (chalOf hd forms) (fun ρ => forms (ρ, none)) = forms := by
  funext i
  rcases i with ⟨ρ, j⟩
  cases j with
  | none => rfl
  | some j =>
    funext k
    simp [formsOfChallenge, chalOf]

noncomputable def formEquiv [Fact (1 < P.q)] (hd : P.d ≠ 0) :
    (MSISChallenge P hd × (Fin P.rows → Rq P)) ≃ FormMatrix P where
  toFun x := formsOfChallenge P hd x.1 x.2
  invFun f := (chalOf hd f, fun ρ => f (ρ, none))
  left_inv x := by
    rcases x with ⟨chal, star⟩
    simp [chalOf_formsOfChallenge, formsOfChallenge]
  right_inv := formsOfChallenge_chalOf hd

theorem uniform_forms [Fact (1 < P.q)] [NeZero P.q] (hd : P.d ≠ 0) :
    letI : Nonempty (MSISChallenge P hd) := ⟨0⟩
    letI := SampleableType.ofFintype (MSISChallenge P hd)
    𝒮[do let chal ← $ᵗ (MSISChallenge P hd)
         let star ← $ᵗ (Fin P.rows → Rq P)
         pure (chal, formsOfChallenge P hd chal star)] =
    𝒮[do let forms ← $ᵗ (FormMatrix P)
         pure (chalOf hd forms, forms)] := by
  classical
  letI : Nonempty (MSISChallenge P hd) := ⟨0⟩
  letI := SampleableType.ofFintype (MSISChallenge P hd)
  let e := formEquiv (P := P) hd
  have hp : 𝒮[do let chal ← $ᵗ (MSISChallenge P hd)
                   let star ← $ᵗ (Fin P.rows → Rq P)
                   pure (chal, star)] =
      𝒮[$ᵗ (MSISChallenge P hd × (Fin P.rows → Rq P))] := by
    change 𝒮[do let chal ← $ᵗ (MSISChallenge P hd)
                let star ← $ᵗ (Fin P.rows → Rq P)
                pure (chal, star)] =
      𝒮[(fun a b => (a, b)) <$> ($ᵗ (MSISChallenge P hd)) <*> ($ᵗ (Fin P.rows → Rq P))]
    simp only [seq_eq_bind_map, map_eq_pure_bind, pure_bind, bind_assoc]
  have h := evalSPMF_map_eq_of_evalSPMF_eq
    (evalSPMF_map_bijective_uniform_cross _ e e.bijective)
    (fun forms => (chalOf hd forms, forms))
  have hp' := evalSPMF_map_eq_of_evalSPMF_eq hp
    (fun x => (x.1, formsOfChallenge P hd x.1 x.2))
  simp only [map_bind, map_pure, bind_pure_comp] at hp'
  simp only [Functor.map_map, Function.comp_def] at h
  change 𝒮[(fun x : MSISChallenge P hd × (Fin P.rows → Rq P) =>
      (chalOf hd (formsOfChallenge P hd x.1 x.2), formsOfChallenge P hd x.1 x.2)) <$>
        ($ᵗ (MSISChallenge P hd × (Fin P.rows → Rq P)))] = _ at h
  simp only [chalOf_formsOfChallenge] at h
  simpa only [bind_pure_comp, Functor.map_map, Function.comp_def] using hp'.trans h

end Praxis.Proofs.Reduction
