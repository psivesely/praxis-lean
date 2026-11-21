import Praxis.Forms
import Praxis.Encryption.BN254
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Order.Interval.Finset.Nat
import Praxis.Proofs.Unit.WKey
import Praxis.Proofs.Decryption.Correct
import Praxis.Dec
import Praxis.Domain
import Praxis.Enc
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.Basic
import Praxis.Params
import Praxis.Relation
import Praxis.Scheme
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Assembly

open OracleComp OracleSpec

open Praxis.Algebra (Vec)

theorem correctness_of_lemmas (ch : AdmissibleChoice Params.main)
    (h_unit : type_of% @Praxis.Proofs.Unit.wkey_vanish)
    (h_decref : type_of% @Praxis.Proofs.Decryption.decref_correct) :
    ∀ S : Relation (scheme ch).params, InShape (scheme ch).params S →
    ∀ x : Vec (Fq (scheme ch).params) (scheme ch).params.N, IsWitness S x →
    ∀ m : Msg (scheme ch).params,
      (Pr[fun out => out ≠ some m | (scheme ch).decExp S m x]).toReal ≤
        2 / ((scheme ch).params.q : ℝ) := by
  classical
  dsimp only [Scheme.decExp, scheme]
  intro S hS x hx m
  have : Nonempty {c : Coins P0 // ValidCoins (ppOf ch S).qap c} := ppOf_coins ch S
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  change Pr[fun out => out ≠ some m | do
    let HF ← $ᵗ (FormOracle P0)
    let kdf ← $ᵗ (KDF P0)
    let ct ← Enc (expGroups P0.q) HF kdf canonName (ppOf ch S) m
    pure (decRef (expGroups P0.q) HF kdf canonName (ppOf ch S) ct x)] ≤
      ENNReal.ofReal (2 / (P0.q : ℝ))
  simp only [Enc, bind_assoc, pure_bind]
  rw [probEvent_bind_bind_swap ($ᵗ (FormOracle P0)) ($ᵗ (KDF P0))]
  apply probEvent_bind_le_of_forall_le
  intro kdf _
  rw [probEvent_bind_bind_swap ($ᵗ (FormOracle P0)) ($ᵗ (Seed P0))]
  apply probEvent_bind_le_of_forall_le
  intro seed _
  refine le_trans (probEvent_bind_le_probEvent
    (p := fun HF => wKey (formsOf HF seed) x = 0) ?_) ?_
  · intro HF _ hw
    have hzero : ∀ c : {c : Coins P0 // ValidCoins (ppOf ch S).qap c},
        decRef (expGroups P0.q) HF kdf canonName (ppOf ch S)
          (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c.1) x = some m :=
      fun c => h_decref ch S hS HF kdf m seed c.1 c.2 x hx hw
    rw [probEvent_bind_eq_tsum]
    apply ENNReal.tsum_eq_zero.mpr
    intro c
    rw [hzero c]
    simp only [probEvent_pure, ne_eq, not_true_eq_false, ite_false, mul_zero]
  · exact (ENNReal.le_ofReal_iff_toReal_le probEvent_ne_top (by positivity)).mpr
      (h_unit x hx.1 seed)

end Praxis.Proofs.Assembly
