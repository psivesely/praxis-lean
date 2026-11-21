import Praxis.Proofs.Injectivity.Deterministic
import Praxis.Extractor
import Praxis.ExtractorCounted
import Praxis.Grid
import Praxis.Proofs.Injectivity.Erasure
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Units
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec

variable {q : ℕ}

def firstTable {D B : Type} [DecidableEq D] (pairs : List (D × B)) (g : D → B) (i : D) : B :=
  ((pairs.find? fun e => decide (e.1 = i)).map Prod.snd).getD (g i)

theorem firstTable_cons {D B : Type} [DecidableEq D] (i : D) (b : B)
    (pairs : List (D × B)) (g : D → B) :
    firstTable ((i, b) :: pairs) g = Function.update (firstTable pairs g) i b := by
  funext j
  by_cases h : j = i <;> simp [firstTable, h, Ne.symm]

theorem firstTable_defaults {D B : Type} [DecidableEq D] (pairs : List (D × B))
    (g h : D → B) (hc : ∀ i, i ∈ pairs.map Prod.fst) : firstTable pairs g = firstTable pairs h := by
  funext i
  have hx : ∃ e ∈ pairs, e.1 = i := by simpa using hc i
  have hf : (pairs.find? fun e => decide (e.1 = i)).isSome := by
    simpa only [List.isSome_find?, List.any_eq_true, decide_eq_true_eq] using hx
  cases he : pairs.find? (fun e => decide (e.1 = i)) with
  | none => simp [he] at hf
  | some e => simp [firstTable, he]

def samplePairs {D B : Type} (xs : List D) (c : ProbComp B) : ProbComp (List (D × B)) :=
  xs.mapM fun i => do let b ← c; pure (i, b)

theorem samplePairs_keys {D B : Type} (xs : List D) (c : ProbComp B)
    (pairs : List (D × B)) (hp : pairs ∈ support (samplePairs xs c)) :
    pairs.map Prod.fst = xs := by
  induction xs generalizing pairs with
  | nil => simpa [samplePairs] using hp
  | cons i is ih =>
    simp only [samplePairs, List.mapM_cons, bind_assoc] at hp
    obtain ⟨b, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
    simp only [pure_bind] at hp
    obtain ⟨tail, ht, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst pairs
    simp [ih tail ht]

def buildTable {D B : Type} [DecidableEq D] (xs : List D) (g : D → B) (c : ProbComp B) :
    ProbComp (D → B) := do
  let pairs ← samplePairs xs c
  pure (firstTable pairs g)

theorem buildTable_cons {D B : Type} [DecidableEq D] (i : D) (xs : List D)
    (g : D → B) (c : ProbComp B) :
    buildTable (i :: xs) g c = (do
      let b ← c
      let t ← buildTable xs g c
      pure (Function.update t i b)) := by
  simp [buildTable, samplePairs, List.mapM_cons, firstTable_cons, bind_assoc]

theorem buildTable_defaults {D B : Type} [DecidableEq D] (xs : List D)
    (g h : D → B) (c : ProbComp B) (hc : ∀ i, i ∈ xs) :
    buildTable xs g c = buildTable xs h c := by
  apply bind_congr_of_forall_mem_support
  intro pairs hp
  rw [firstTable_defaults pairs g h (by simpa [samplePairs_keys xs c pairs hp] using hc)]

theorem buildTable_patch {D B : Type} [DecidableEq D] [SampleableType B]
    (xs : List D) (g : D → B) (c : ProbComp B) (hc : evalSPMF c = evalSPMF ($ᵗ B)) :
    evalSPMF (buildTable xs g c) = evalSPMF (patchTable xs g) := by
  induction xs with
  | nil =>
    simp only [buildTable, samplePairs, List.mapM_nil, pure_bind, patchTable_nil]
    rfl
  | cons i is ih =>
    rw [buildTable_cons]
    calc
      _ = evalSPMF (do let b ← $ᵗ B; let t ← buildTable is g c; pure (Function.update t i b)) := by
        simp only [evalSPMF_bind, hc]
      _ = evalSPMF (do let t ← buildTable is g c; let b ← $ᵗ B; pure (Function.update t i b)) :=
        evalSPMF_bind_bind_swap _ _ _
      _ = evalSPMF (patchTable (i :: is) g) := by
        simp only [patchTable_cons, evalSPMF_bind, ih]

theorem buildTable_uniform {D B : Type} [Finite D] [DecidableEq D] [Finite B] [Nonempty B]
    [SampleableType B] [SampleableType (D → B)] (xs : List D) (g : D → B) (c : ProbComp B)
    (hc : evalSPMF c = evalSPMF ($ᵗ B)) (hcov : ∀ i, i ∈ xs) :
    evalSPMF (buildTable xs g c) = evalSPMF ($ᵗ (D → B)) := by
  calc
    _ = evalSPMF (do let h ← $ᵗ (D → B); buildTable xs g c) := by
      apply evalSPMF_ext
      intro y
      simp only [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
    _ = evalSPMF (do let h ← $ᵗ (D → B); buildTable xs h c) := by
      apply evalSPMF_bind_congr'
      intro h
      rw [buildTable_defaults xs g h c hcov]
    _ = evalSPMF (do let h ← $ᵗ (D → B); patchTable xs h) := by
      apply evalSPMF_bind_congr'
      intro h
      exact buildTable_patch xs h c hc
    _ = _ := evalSPMF_uniformSample_patchList xs

theorem run_funOfM_build {D B : Type} [DecidableEq D] (xs : List D) (d : B) (c : UnitComp q B) :
    runUnits (funOfM xs d (fun _ => c)) = buildTable xs (fun _ => d) (runUnits c) := by
  simp only [funOfM, buildTable, samplePairs, runUnits, simulateQ_bind, simulateQ_pure,
    simulateQ_list_mapM]
  rfl

theorem run_funOfM_uniform {D B : Type} [Finite D] [DecidableEq D] [Finite B] [Nonempty B]
    [SampleableType B] [SampleableType (D → B)] (xs : List D) (d : B) (c : UnitComp q B)
    (hc : evalSPMF (runUnits c) = evalSPMF ($ᵗ B)) (hcov : ∀ i, i ∈ xs) :
    evalSPMF (runUnits (funOfM xs d (fun _ => c))) = evalSPMF ($ᵗ (D → B)) := by
  rw [run_funOfM_build]
  exact buildTable_uniform xs _ _ hc hcov

theorem samplePairs_snd {D B : Type} (xs : List D) (c : ProbComp B) :
    List.map Prod.snd <$> samplePairs xs c = xs.mapM (fun _ => c) := by
  induction xs with
  | nil => simp [samplePairs]
  | cons i is ih =>
    simp only [samplePairs, List.mapM_cons] at *
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, List.map_cons] at *
    apply bind_congr
    intro b
    rw [← ih]
    simp [bind_assoc]

theorem firstTable_nth {D B : Type} [DecidableEq D] (pairs : List (D × B))
    (g : D → B) (hn : (pairs.map Prod.fst).Nodup) (k : Fin pairs.length) :
    firstTable pairs g pairs[k].1 = pairs[k].2 := by
  induction pairs with
  | nil => exact Fin.elim0 k
  | cons p ps ih =>
    rcases p with ⟨j, b⟩
    cases k using Fin.cases with
    | zero => simp [firstTable_cons]
    | succ k =>
      have hnd := List.nodup_cons.mp hn
      have hne : ps[k].1 ≠ j := by
        intro he
        apply hnd.1
        exact List.mem_map.mpr ⟨ps[k], List.getElem_mem k.isLt, he⟩
      change firstTable ((j, b) :: ps) g ps[k].1 = ps[k].2
      rw [firstTable_cons, Function.update_of_ne hne]
      exact ih hnd.2 k

theorem firstTable_finRange {B : Type} {n : ℕ} (pairs : List (Fin n × B))
    (g : Fin n → B) (d : B) (hk : pairs.map Prod.fst = List.finRange n) (i : Fin n) :
    firstTable pairs g i = (pairs.map Prod.snd).getD i.val d := by
  have hlen : pairs.length = n := by
    have := congrArg List.length hk
    simpa using this
  have hi : i.val < pairs.length := by simpa [hlen] using i.isLt
  have he : pairs[i.val].1 = i := by
    have := congrArg (fun xs : List (Fin n) => xs.getD i.val i) hk
    simpa [List.getD_eq_getElem?_getD, hi] using this
  have ht := firstTable_nth pairs g (hk.symm ▸ List.nodup_finRange n) ⟨i.val, hi⟩
  simpa [he, List.getD_eq_getElem?_getD, hi] using ht

theorem run_vec_build {n : ℕ} (c : UnitComp q (ZMod q)) :
    runUnits (vecOfM (fun _ : Fin n => c)) =
      buildTable (List.finRange n) (fun _ => 0) (runUnits c) := by
  unfold vecOfM
  simp only [run_bind, run_pure]
  rw [show runUnits ((List.finRange n).mapM (fun _ => c)) =
      (List.finRange n).mapM (fun _ => runUnits c) from simulateQ_list_mapM _ _ _]
  rw [← samplePairs_snd (List.finRange n) (runUnits c)]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, buildTable]
  apply bind_congr_of_forall_mem_support
  intro pairs hp
  congr 1
  funext i
  exact (firstTable_finRange pairs _ 0 (samplePairs_keys _ _ pairs hp) i).symm

section Field

variable [NeZero q] [SampleableType (ZMod q)]

theorem sampleF_uniform :
    evalSPMF (runUnits (sampleF : UnitComp q (ZMod q))) = evalSPMF ($ᵗ (ZMod q)) := by
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  let e : Fin (q - 1 + 1) ≃ ZMod q := (Fin.castOrderIso hq).toEquiv.trans (ZMod.finEquiv q).toEquiv
  have he (i : Fin (q - 1 + 1)) : e i = (i.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
      apply Fin.ext
      change i.val = i.val % (n + 1)
      exact (Nat.mod_eq_of_lt (by simpa using i.isLt)).symm
  have hr : runUnits (sampleF : UnitComp q (ZMod q)) =
      e <$> ($ᵗ (Fin (q - 1 + 1))) := by
    unfold sampleF
    rw [run_bind]
    have hf : runUnits (sampleFin (q - 1) : UnitComp q _) = $ᵗ (Fin (q - 1 + 1)) := by
      unfold runUnits sampleFin
      rw [simulateQ_spec_query]
      rfl
    rw [hf]
    simp only [run_pure, map_eq_bind_pure_comp]
    apply bind_congr
    intro i
    rw [Function.comp_apply, he]
  rw [hr]
  exact evalSPMF_map_bijective_uniform_cross _ e e.bijective

theorem vec_uniform (n : ℕ) [SampleableType (Fin n → ZMod q)] :
    evalSPMF (runUnits (vecOfM (fun _ : Fin n => (sampleF : UnitComp q (ZMod q))))) =
      evalSPMF ($ᵗ (Fin n → ZMod q)) := by
  rw [run_vec_build]
  exact buildTable_uniform _ _ _ sampleF_uniform (by simp)

end Field

section Sketch

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem drawSketches_uniform [SampleableType (Sketches P)] :
    evalSPMF (runUnits (drawSketchesC : UnitComp P.q (Sketches P))) = evalSPMF ($ᵗ (Sketches P)) := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (Fq P)
  letI := SampleableType.ofFintype ((Cell P × Fin 3 × Sector) → Algebra.Vec (Fq P) P.N)
  let e : ((Cell P × Fin 3 × Sector) → Algebra.Vec (Fq P) P.N) ≃ Sketches P :=
    ⟨fun t c l s => t (c, l, s), fun sk e => sk e.1 e.2.1 e.2.2, fun _ => rfl, fun _ => rfl⟩
  have hh := run_funOfM_uniform (q := P.q) (g2Keys P) (0 : Algebra.Vec (Fq P) P.N)
    (vecOfM (fun _ : Fin (P.N + 1) => sampleF)) (vec_uniform (P.N + 1)) (by simp)
  have hr : runUnits (drawSketchesC : UnitComp P.q (Sketches P)) =
      e <$> runUnits (funOfM (g2Keys P) 0
        (fun _ => vecOfM (fun _ : Fin (P.N + 1) => sampleF))) := by
    simp only [drawSketchesC, run_bind, run_pure, map_eq_bind_pure_comp]
    rfl
  rw [hr]
  change evalSPMF (e <$> runUnits (funOfM (g2Keys P) 0
    (fun _ => vecOfM (fun _ : Fin (P.N + 1) => sampleF)))) = _
  rw [evalSPMF_map, hh, ← evalSPMF_map]
  exact evalSPMF_map_bijective_uniform_cross _ e e.bijective

theorem extractor_law (S : Relation P) (pub : PubView P) (tr : List (TrOp P)) :
    evalSPMF (runUnits (extractorC (sparseOf S) pub tr)) = evalSPMF (extractorRef S pub tr) := by
  classical
  haveI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (Sketches P)
  rw [run_extractor]
  change evalSPMF (runUnits (drawSketchesC : UnitComp P.q (Sketches P)) >>=
      fun sk => pure (extractWith S pub tr sk)) =
    evalSPMF (($ᵗ (Sketches P)) >>= fun sk => pure (extractWith S pub tr sk))
  rw [evalSPMF_bind, drawSketches_uniform, ← evalSPMF_bind]

end Sketch

end Praxis.Proofs.Injectivity
