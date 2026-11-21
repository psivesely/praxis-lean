import Praxis.Search
import Praxis.Algebra.RankMass.Light4
import Praxis.Constants
import Praxis.Grid
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation
import Praxis.Algebra.Definitions.Sampler
import Praxis.Algebra.Definitions.Stack

namespace Praxis.Bounds.Rank

set_option maxRecDepth 4096

set_option maxHeartbeats 2000000

open Praxis.Constants

theorem grid_four_lt_theta : 1 / (g : ℝ) ^ 4 < (theta : ℝ) := by
  norm_num [g, theta]

theorem rank_four_light {N d rows : ℕ} [Fact q.Prime]
    (W : Algebra.Stack (ZMod q) N d rows)
    (hr : 4 ≤ Algebra.stackRank W) :
    Algebra.stackMass g (fun _ => g) W ≤ (theta : ℝ) := by
  have hp : g ≤ q := by norm_num [g, q]
  have hg : 0 < g := by norm_num [g]
  have h := Algebra.RankMass.rank_ge_four_light_holds q N d rows g (fun _ => g)
    hg (fun _ => ⟨le_rfl, hp⟩) hp W hr
  exact h.trans (le_of_lt grid_four_lt_theta)

noncomputable def cellEquiv (P : Praxis.Params) :
    Praxis.Cell P ≃ Algebra.Cell 0 (Fintype.card (Praxis.Cell P)) where
  toFun c := (0, Fintype.equivFin (Praxis.Cell P) c)
  invFun k := (Fintype.equivFin (Praxis.Cell P)).symm k.2
  left_inv c := by simp
  right_inv k := by cases k with | mk a b => simp [Fin.eq_zero a]

noncomputable def stackAsBase {P : Praxis.Params} (W : Praxis.Stack P) :
    Algebra.Stack (Praxis.Fq P) P.N 0 (Fintype.card (Praxis.Cell P)) :=
  fun c => W ((cellEquiv P).symm c)

private noncomputable def outputEquiv (P : Praxis.Params) :
    (Praxis.Cell P → Fin (P.N + 1) → Praxis.Fq P) ≃
      (Algebra.Cell 0 (Fintype.card (Praxis.Cell P)) × Fin (P.N + 1) → Praxis.Fq P) where
  toFun f k := f ((cellEquiv P).symm k.1) k.2
  invFun f c i := f (cellEquiv P c, i)
  left_inv f := by funext c i; simp
  right_inv f := by funext k; simp

private theorem maxAtom_equiv {X Y Z : Type*} [Fintype X]
    (e : Y ≃ Z) (f : X → Y) : Algebra.maxAtom (fun x => e (f x)) = Algebra.maxAtom f := by
  classical
  unfold Algebra.maxAtom
  symm
  apply Equiv.iSup_congr e
  intro y
  unfold Algebra.atom
  apply congrArg (fun n : ℕ => (n : ℝ) / Fintype.card X)
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  exact e.injective.eq_iff

theorem gp_eq_stackMass {P : Praxis.Params} (W : Praxis.Stack P) :
    Praxis.gp W = Algebra.stackMass P.g (fun _ => P.g) (stackAsBase W) := by
  unfold Praxis.gp Algebra.stackMass
  have h : (fun x : Praxis.SearchSample P => fun ki =>
      Algebra.dot (Algebra.stackRows (stackAsBase W) ki) (Algebra.centeredF x)) =
      (fun x : Praxis.SearchSample P => outputEquiv P (fun c => (W c).mulVec (Praxis.rField x))) := by
    funext x ki
    rfl
  exact (maxAtom_equiv (outputEquiv P) _).symm.trans (congrArg Algebra.maxAtom h.symm)

theorem rank_four_bound [Fact (Nat.Prime Praxis.Params.main.q)] (W : Praxis.Stack Praxis.Params.main)
    (hr : 4 ≤ Algebra.stackRank (stackAsBase W)) : Praxis.Light W := by
  unfold Praxis.Light
  rw [gp_eq_stackMass]
  letI : Fact q.Prime := ⟨by simpa only [Praxis.Params.main] using
    (Fact.out : Nat.Prime Praxis.Params.main.q)⟩
  exact rank_four_light (stackAsBase W) hr

end Praxis.Bounds.Rank
