import Praxis.Proofs.Basic
import Praxis.Grid
import Praxis.Params
import Praxis.Search
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler

namespace Praxis.Proofs.Sampling

open OracleComp OracleSpec

theorem light_locus (W : Stack P0) (t : Cell P0 → Algebra.Vec (Fq P0) P0.N) :
    (Pr[fun s => ∀ c, (W c).mulVec (rField s) = t c | searchLaw]).toReal ≤ gp W := by
  classical
  set f : SearchSample P0 → (Cell P0 → Algebra.Vec (Fq P0) P0.N) :=
    fun w c => (W c).mulVec (rField w) with hf
  have hev : Pr[fun s => ∀ c, (W c).mulVec (rField s) = t c | searchLaw] =
      Pr[fun s => f s = t | searchLaw] := by
    congr 1
    ext s
    simp only [hf]
    exact ⟨fun h => funext h, fun h c => congrFun h c⟩
  rw [hev]
  unfold searchLaw
  rw [probEvent_uniformSample, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  have hbdd : BddAbove (Set.range fun y => Algebra.atom f y) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    unfold Algebra.atom
    have hpos : (0 : ℝ) < Fintype.card (SearchSample P0) :=
      by exact_mod_cast Fintype.card_pos
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_univ _
  have := le_ciSup hbdd t
  unfold gp Algebra.maxAtom
  refine le_trans (le_of_eq ?_) this
  unfold Algebra.atom
  congr

end Praxis.Proofs.Sampling
