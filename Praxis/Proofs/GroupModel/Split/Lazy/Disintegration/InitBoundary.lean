import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitGuess
import Praxis.Enc
import Praxis.Extractor
import Praxis.Forms
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitLabels
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Published
import Praxis.Reduction

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option maxHeartbeats 500000

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

variable (pp : PublicParams P0)

attribute [local irreducible] initialise keys1 keys2 g1Order g2Order List.mapM referenceInsert formIndexList Finset.filter

lemma event_bind_point {α β : Type} (oa : ProbComp α) (f : α → ProbComp β)
    (a : α) (E : β → Prop) :
    Pr[= a | oa] * Pr[E | f a] ≤ Pr[E | oa >>= f] := by
  rw [probEvent_bind_eq_tsum]
  exact ENNReal.le_tsum a

def genericAt (A : Adversary P0) (hdr : Header P0) (forms : FormMatrix P0)
    (st : OracleState P0) : ProbComp (FullRecord pp) := do
  let z ← (referenceInitial pp forms).run (empty pp)
  let g : GenState pp :=
    ⟨{st with issuedT := (z.1.gT.map Prod.snd).toFinset}, z.2, [], []⟩
  let out ← (simulateQ (genHandler pp) (A.run z.1 hdr)).run g
  pure ⟨hdr, forms, z.1, out.2.steps⟩

def initialWorlds (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) :
    Finset (LabelEncoding P0) := by
  exact @Finset.filter (LabelEncoding P0)
    (fun σ => pubView σ pp (formVec r.forms) c.val = r.pv ∧ guessValuesσ pp r σ = x)
    (fun _ => Classical.propDecidable _) Finset.univ

lemma mem_initialWorlds (r : Record pp) (c : CoinDomain pp) (x : ℕ → k)
    (σ : LabelEncoding P0) : σ ∈ initialWorlds pp r c x ↔
      pubView σ pp (formVec r.forms) c.val = r.pv ∧ guessValuesσ pp r σ = x := by
  simp only [initialWorlds, Finset.mem_filter, Finset.mem_univ, true_and]

lemma record_eq_iff (r : Record pp) (steps : List (Step pp))
    (pending : Option (AdvModel P0).Domain) (pendingOrder : Option (List GuessVar)) :
    (⟨r.header, r.forms, r.pv, steps, pending, pendingOrder⟩ : Record pp) = r ↔
      steps = r.steps ∧ pending = r.pending ∧ pendingOrder = r.pendingOrder := by
  cases r
  simp only [Record.mk.injEq, true_and]

lemma initial_sum_bound (A : Adversary P0) (n : ℕ) (r : Record pp)
    (c : CoinDomain pp) (x : ℕ → k) (pad : Msg P0) (st : OracleState P0)
    (hc : (initialise pp r.forms r.pv).first = none)
    (hind : IndStmt pp n r c x pad (A.run r.pv r.header)) :
    let g : GenState pp :=
      ⟨{st with issuedT := (r.pv.gT.map Prod.snd).toFinset},
        initialise pp r.forms r.pv, [], []⟩
    let W := initialWorlds pp r c x
    (∑ σ ∈ W, Pr[fun z => RGood pp n r z.2 |
      (simulateQ (obsHandler pp σ c.val) (A.run r.pv r.header)).run
        (lift pp c.val pad σ g)]) ≤
      Fintype.card (LabelEncoding P0) *
        Pr[fun R => R.cut n = r | genericAt pp A r.header r.forms st] *
          Pr[= x | guessDraw pp r c] := by
  dsimp only
  let g : GenState pp :=
    ⟨{st with issuedT := (r.pv.gT.map Prod.snd).toFinset},
      initialise pp r.forms r.pv, [], []⟩
  let W := initialWorlds pp r c x
  change (∑ σ ∈ W, _) ≤ _
  have memW (σ : LabelEncoding P0) : σ ∈ W ↔
      pubView σ pp (formVec r.forms) c.val = r.pv ∧ guessValuesσ pp r σ = x := by
    exact mem_initialWorlds pp r c x σ
  by_cases hW : W.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hW, Finset.sum_empty]
    exact zero_le
  obtain ⟨σ, hσ⟩ := hW
  obtain ⟨hpv, hx⟩ := (memW σ).mp hσ
  have hI : Inv pp g := initial_inv pp r.forms r.pv st hc
  have hcons : ∀ τ ∈ W, τ ∈ cons pp g.shadow g.order c x ∧ guessValuesσ pp r τ = x := by
    intro τ hτ
    obtain ⟨hpv', hx'⟩ := (memW τ).mp hτ
    refine ⟨?_, hx'⟩
    change τ ∈ cons pp (initialise pp r.forms r.pv) [] c x
    rw [← hpv']
    exact initialise_cons pp r.forms c x τ
  have hsh : ShadowOf pp r g := by
    intro h
    unfold Record.shadow
    rw [h]
    rfl
  have hi := hind g W hI hsh hcons
  have hC : ((cons pp g.shadow g.order c x).card : ℝ≥0∞) ≤
      Fintype.card (LabelEncoding P0) *
        Pr[= (r.pv, initialise pp r.forms r.pv) |
          (referenceInitial pp r.forms).run (empty pp)] := by
    have h := initial_count pp c x r.forms σ (by rwa [hpv])
    simpa only [hpv] using h
  have hxprob := guess_lower pp r c x σ hx
  have hG : Pr[= (r.pv, initialise pp r.forms r.pv) |
        (referenceInitial pp r.forms).run (empty pp)] *
      Pr[fun z => GGood pp n r z.2 | (simulateQ (genHandler pp) (A.run r.pv r.header)).run g] ≤
      Pr[fun R => R.cut n = r | genericAt pp A r.header r.forms st] := by
    unfold genericAt
    apply le_trans _ (event_bind_point _ _ (r.pv, initialise pp r.forms r.pv) _)
    apply mul_le_mul_right
    apply le_of_eq
    rw [bind_pure_comp, probEvent_map]
    apply probEvent_congr' (fun z _ => ?_) rfl
    simp only [FullRecord.cut, record_eq_iff, true_and, GGood, cutOf, Prod.mk.injEq, Function.comp_def]
  apply hi.trans
  calc
    _ ≤ (Fintype.card (LabelEncoding P0) *
        Pr[= (r.pv, initialise pp r.forms r.pv) |
          (referenceInitial pp r.forms).run (empty pp)]) *
        Pr[fun z => GGood pp n r z.2 |
          (simulateQ (genHandler pp) (A.run r.pv r.header)).run g] *
          Pr[= x | guessDraw pp r c] :=
      mul_le_mul (mul_le_mul_left hC _) hxprob zero_le zero_le
    _ = Fintype.card (LabelEncoding P0) *
        (Pr[= (r.pv, initialise pp r.forms r.pv) |
          (referenceInitial pp r.forms).run (empty pp)] *
        Pr[fun z => GGood pp n r z.2 |
          (simulateQ (genHandler pp) (A.run r.pv r.header)).run g]) *
          Pr[= x | guessDraw pp r c] := by ring
    _ ≤ _ := mul_le_mul_left (mul_le_mul_right hG _) _

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init
