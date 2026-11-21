import VCVio.OracleComp.Constructions.SampleableType

open OracleComp

namespace Praxis.Proofs.Reduction

noncomputable def readFresh {I V : Type} [DecidableEq I] [SampleableType V] :
    List I → (I → Option V) → ProbComp (List (I × V) × (I → Option V))
  | [], t => pure ([], t)
  | i :: l, t => do
      let v ← $ᵗ V
      let z ← readFresh l (Function.update t i (some v))
      pure ((i, v) :: z.1, z.2)

theorem readFresh_law {I V : Type} [Fintype I] [DecidableEq I] [Fintype V]
    [Nonempty V] [SampleableType V] [SampleableType (I → V)]
    (l : List I) (t : I → Option V) (hn : l.Nodup) :
    𝒮[readFresh l t] =
      𝒮[do let g ← $ᵗ (I → V)
           pure (l.map (fun i => (i, g i)), fun i => if i ∈ l then some (g i) else t i)] := by
  classical
  induction l generalizing t with
  | nil =>
    simp only [readFresh, List.map_nil, List.not_mem_nil, if_false]
    apply evalSPMF_ext
    intro z
    simp [probOutput_bind_const]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.mp hn).1
    have hl : l.Nodup := (List.nodup_cons.mp hn).2
    simp only [readFresh]
    calc
      _ = 𝒮[do let v ← $ᵗ V
               let g ← $ᵗ (I → V)
               pure ((i, v) :: l.map (fun j => (j, g j)),
                 fun j => if j ∈ l then some (g j) else Function.update t i (some v) j)] := by
        apply evalSPMF_bind_congr
        intro v hv
        rw [evalSPMF_bind, ih _ hl, ← evalSPMF_bind]
        simp only [bind_assoc, pure_bind]
      _ = 𝒮[do let v ← $ᵗ V
               let g ← $ᵗ (I → V)
               let f := Function.update g i v
               pure ((i :: l).map (fun j => (j, f j)),
                 fun j => if j ∈ i :: l then some (f j) else t j)] := by
        apply evalSPMF_bind_congr
        intro v hv
        apply evalSPMF_bind_congr
        intro g hg
        have hm : l.map (fun j => (j, g j)) =
            l.map (fun j => (j, Function.update g i v j)) := by
          apply List.map_congr_left
          intro j hj
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
        have ht : (fun j => if j ∈ l then some (g j) else Function.update t i (some v) j) =
            (fun j => if j ∈ i :: l then some (Function.update g i v j) else t j) := by
          funext j
          by_cases hji : j = i
          · subst j; simp [hi]
          · simp [hji, Function.update_of_ne hji]
        simp [hm, ht]
      _ = _ := by
        let k := fun f : I → V => ((i :: l).map (fun j => (j, f j)),
          fun j => if j ∈ i :: l then some (f j) else t j)
        have h := evalSPMF_map_eq_of_evalSPMF_eq
          (evalSPMF_uniformSample_bind_update (R := V) i) k
        simpa only [map_bind, map_pure, bind_pure_comp, Functor.map_map,
          Function.comp_def, k] using h

end Praxis.Proofs.Reduction
