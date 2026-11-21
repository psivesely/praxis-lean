import Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.InitLabels
import Praxis.Enc
import Praxis.Games
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSimulation
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Proofs.GroupModel.Split.Disintegration

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option maxHeartbeats 1600000

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Simulation

variable (pp : PublicParams P0)

attribute [local irreducible] guessPool usedBefore reservoirDraw draw

def trunc (x : ℕ → k) (n : ℕ) : ℕ → k := fun t => if t < n then x t else 0

lemma trunc_update (x : ℕ → k) (n : ℕ) :
    Function.update (trunc x n) n (x n) = trunc x (n+1) := by
  funext t
  by_cases h : t = n
  · subst t; simp [trunc]
  · by_cases ht : t < n
    · simp only [Function.update_of_ne h, trunc, if_pos ht, if_pos (show t < n+1 by omega)]
    · simp only [Function.update_of_ne h, trunc, if_neg ht, if_neg (show ¬ t < n+1 by omega)]

lemma valueAt_trunc (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (t : ℕ)
    (P : Poly pp) (h : ∀ v ∈ P.vars, r.order.idxOf v < t) :
    valueAt pp r.order c (trunc x t) P = valueAt pp r.order c x P := by
  unfold valueAt
  simp only [MvPolynomial.coe_eval₂Hom]
  apply MvPolynomial.eval₂_congr
  intro v d hv hd
  have hv' : v ∈ P.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨d, MvPolynomial.mem_support_iff.mpr hd, hv⟩
  exact if_pos (h v hv')

lemma pool_trunc (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (t : ℕ) :
    guessPool pp r c t (trunc x t) = guessPool pp r c t x := by
  have hused : usedBefore pp r c t (trunc x t) = usedBefore pp r c t x := by
    ext a
    simp only [usedBefore, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, P, hd, hv, ha⟩
      exact ⟨l, P, hd, hv, (valueAt_trunc pp r c x t P hv).symm.trans ha⟩
    · rintro ⟨l, P, hd, hv, ha⟩
      exact ⟨l, P, hd, hv, (valueAt_trunc pp r c x t P hv).trans ha⟩
  simp only [guessPool, hused]

lemma draw_mass (pool : Finset k) (hne : pool.Nonempty) (a : k) :
    Pr[= a | draw pool hne] = if a ∈ pool then (pool.card : ℝ≥0∞)⁻¹ else 0 := by
  by_cases ha : a ∈ pool
  · rw [if_pos ha]
    unfold draw
    rw [show a = (⟨a, ha⟩ : {a // a ∈ pool}).val from rfl,
      probOutput_map_injective _ Subtype.val_injective]
    simp
  · rw [if_neg ha]
    apply probOutput_eq_zero
    simp only [draw, support_map, Set.mem_image, not_exists, not_and]
    intro a' _ h
    exact ha (h ▸ a'.property)

lemma reservoir_lower (r : Record pp) (c : CoinDomain pp) (x : ℕ → k) (N : ℕ) :
    (∏ t ∈ Finset.range N,
      if x t ∈ guessPool pp r c t x then ((guessPool pp r c t x).card : ℝ≥0∞)⁻¹ else 0) ≤
      Pr[= trunc x N |
        reservoirDraw (guessPool pp r c) (guessPool_nonempty pp r c) N] := by
  induction N with
  | zero =>
    have hz : trunc x 0 = (fun _ => 0) := by funext t; simp only [trunc, Nat.not_lt_zero, if_false]
    rw [Finset.prod_range_zero, reservoirDraw, hz, probOutput_pure_self]
  | succ N ih =>
    rw [Finset.prod_range_succ, reservoirDraw]
    apply le_trans (mul_le_mul_left ih _)
    apply le_trans _ (bind_point _ _ (trunc x N) (trunc x (N+1)))
    apply mul_le_mul_right
    rw [bind_pure_comp]
    have h := map_point (draw (guessPool pp r c N (trunc x N))
        (guessPool_nonempty pp r c N (trunc x N)))
      (Function.update (trunc x N) N) (x N)
    have ho : Pr[= Function.update (trunc x N) N (x N) |
        Function.update (trunc x N) N <$>
          draw (guessPool pp r c N (trunc x N)) (guessPool_nonempty pp r c N (trunc x N))] =
        Pr[= trunc x (N+1) | Function.update (trunc x N) N <$>
          draw (guessPool pp r c N (trunc x N)) (guessPool_nonempty pp r c N (trunc x N))] :=
      probOutput_congr (trunc_update x N) rfl
    calc
      _ = (if x N ∈ guessPool pp r c N (trunc x N) then
          ((guessPool pp r c N (trunc x N)).card : ℝ≥0∞)⁻¹ else 0) :=
        congrArg (fun pool : Finset k => if x N ∈ pool then (pool.card : ℝ≥0∞)⁻¹ else 0)
          (pool_trunc pp r c x N).symm
      _ = Pr[= x N | draw (guessPool pp r c N (trunc x N))
          (guessPool_nonempty pp r c N (trunc x N))] := (draw_mass _ _ _).symm
      _ ≤ _ := h.trans_eq ho

lemma guess_lower (r : Record pp) (c : CoinDomain pp) (x : ℕ → k)
    (σ : LabelEncoding P0) (hx : guessValuesσ pp r σ = x) :
    guessFactor pp r c x 0 ≤ Pr[= x | guessDraw pp r c] := by
  have ht : trunc x r.order.length = x := by
    funext t
    by_cases h : t < r.order.length
    · exact if_pos h
    · have hget : r.order[t]? = none := List.getElem?_eq_none (by omega)
      rw [← hx]
      simp [trunc, h, guessValuesσ, hget]
  simpa only [guessFactor, Nat.Ico_zero_eq_range, ht, guessDraw] using
    reservoir_lower pp r c x r.order.length

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Init
