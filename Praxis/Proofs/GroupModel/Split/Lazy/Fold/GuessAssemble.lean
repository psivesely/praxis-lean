import Praxis.Proofs.GroupModel.Split.Lazy.Fold.GuessCount
import Praxis.Domain
import Praxis.Enc
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingModel
import Praxis.Proofs.GroupModel.Split.Lazy.CouplingSymbolic
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.GuessBuild
import Praxis.Proofs.GroupModel.Split.Lazy.Fold.GuessTyped
import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Proofs.GroupModel.Split.Lazy.Invariants
import Praxis.Relation
import Praxis.Search

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

open scoped BigOperators

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 16384

set_option linter.constructorNameAsVariable false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild

open Classical Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

def build (pp : PublicParams P0) (r : Record pp) (e : Collision pp) (s : SearchSample P0) :
    Option GuessTest :=
  if h : ∃ t, Interprets pp r e s t then some h.choose else none

lemma build_interprets (pp : PublicParams P0) (r : Record pp) (e : Collision pp)
    (s : SearchSample P0) (t : GuessTest) (ht : build pp r e s = some t) :
    Interprets pp r e s t := by
  unfold build at ht
  split_ifs at ht with h
  · cases ht
    exact h.choose_spec

lemma build_isSome (pp : PublicParams P0) (r : Record pp) (e : Collision pp)
    (s : SearchSample P0) (h : ∃ t, Interprets pp r e s t) : (build pp r e s).isSome := by
  simp only [build, dif_pos h, Option.isSome_some]

lemma certificate_observed (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0)
    (A : Adversary P0) (Q QH : ℕ) (hA : InClass A Q QH) (ω : World (ppOf ch S))
    (hω : ω ∈ support (observedRun (ppOf ch S) m A)) (e : Collision (ppOf ch S))
    (he : BadAt ω e) (n : ℕ) (e' : Collision (ppOf ch S))
    (hs : e'.sort = e.sort) (hd : e'.diff = e.diff)
    (hv : e'.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset) :
    Certificate (ppOf ch S) ((fullRecord ω).cut n) e' := by
  have htyped := badAt_typed ch S m A
  have hused := used_observedRun (ppOf ch S) m A Q QH hA
  generalize observedRun (ppOf ch S) m A = obs at htyped hused hω
  have ht := htyped ω hω e he
  have ht' : Typed (ppOf ch S) ((fullRecord ω).cut n).forms e'.sort e'.diff := by
    rw [hs, hd]
    exact ht
  refine ⟨hv, ?_, ?_, ?_, ?_⟩
  · exact ht'.degree.trans (by cases e'.sort <;> decide)
  · intro m hm
    exact ht'.coinCoefficient m
  · intro m hm hm0
    exact ht'.sourceCoefficient m hm0
  · intro j hj c x
    exact hused ω hω n j c x

lemma guess_build (ch : AdmissibleChoice P0) (S : Relation P0) (m : Msg P0)
    (A : Adversary P0) (hS : InShape P0 S) (Q QH : ℕ) (hA : InClass A Q QH)
    (hreal : ∀ ω ∈ support (observedRun (ppOf ch S) m A),
      ∀ e, BadAt ω e → ∀ hc : ValidCoins (ppOf ch S).qap ω.1.out.coins,
      evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.new =
        evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e.old) :
    ∃ make : Record (ppOf ch S) → Collision (ppOf ch S) → SearchSample P0 → Option GuessTest,
      (∀ r e s t, make r e s = some t → StdGuess (ppOf ch S) r s t) ∧
      ∀ ω ∈ support (observedRun (ppOf ch S) m A), ∀ e, BadAt ω e → ¬ GuessFree e →
        ∀ n e', Clean n ω → e'.sort = e.sort → e'.diff = e.diff →
          e'.diff.vars ⊆ ((fullRecord ω).cut n).order.toFinset →
          (∀ s, (make ((fullRecord ω).cut n) e' s).isSome) ∧
          ∃ t, make ((fullRecord ω).cut n) e' ω.1.out.coins.2.1 = some t ∧
            MvPolynomial.eval (encode ω.1.out.coins
              (guessValues ((fullRecord ω).cut n) ω)) t.polynomial = 0 := by
  refine ⟨build (ppOf ch S), ?_, ?_⟩
  · intro r e s t ht
    exact (build_interprets _ r e s t ht).1
  have hcert := certificate_observed ch S m A Q QH hA
  have hvalid := valid_observedRun (ppOf ch S) m A
  generalize observedRun (ppOf ch S) m A = obs at hcert hvalid hreal ⊢
  intro ω hω e he hg n e' hclean hs hd hv
  have hc := hvalid ω hω
  have hce := hcert ω hω e he n e' hs hd hv
  have hg' : ¬ GuessFree e' := by
    simpa only [GuessFree, Collision.value, hd] using hg
  have hall : ∀ s, (build (ppOf ch S) ((fullRecord ω).cut n) e' s).isSome :=
    fun s => build_isSome _ _ _ s (exists_test ch S hS _ e' hg' hce s)
  refine ⟨hall, ?_⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hall ω.1.out.coins.2.1)
  refine ⟨t, ht, ?_⟩
  have hint := (build_interprets _ _ _ _ _ ht).2 ⟨ω.1.out.coins, hc⟩
    (guessValues ((fullRecord ω).cut n) ω) rfl
  rw [hint, valueAt_guessValues _ ω hc e'.diff hv]
  have hr : evaluate (ppOf ch S) ω.1.enc ⟨ω.1.out.coins, hc⟩ e'.diff = 0 := by
    rw [hd]
    change evaluate _ _ _ (e.new - e.old) = 0
    rw [map_sub, hreal ω hω e he hc, sub_self]
  rw [hr, mul_zero]

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.GuessBuild
