import Praxis.Proofs.Monitor.Recover.Transport
import Praxis.Proofs.Monitor.Recover.ProbeBound
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Monitor.Recover.Helpers
import Praxis.Proofs.Monitor.Recover.Sampling
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

def probeVariable {P : Params} : ProbeVar P → RecoveryVar P
  | .inl i => .inl i
  | .inr (.inl .E) => .inr (.inr .bE)
  | .inr (.inl .O) => .inr (.inr .bO)
  | .inr (.inl .V) => .inr (.inr .bV)
  | .inr (.inr false) => .inr (.inr .u)
  | .inr (.inr true) => .inr (.inr .eps)

def recoverProbeVariable {P : Params} : RecoveryVar P → Option (ProbeVar P)
  | .inl i => some (.inl i)
  | .inr (.inr .bE) => some (.inr (.inl .E))
  | .inr (.inr .bO) => some (.inr (.inl .O))
  | .inr (.inr .bV) => some (.inr (.inl .V))
  | .inr (.inr .u) => some (.inr (.inr false))
  | .inr (.inr .eps) => some (.inr (.inr true))
  | _ => none

theorem probeVariable_injective {P : Params} : Function.Injective (probeVariable (P := P)) := by
  intro x y h
  have h' := congrArg recoverProbeVariable h
  have hid (z : ProbeVar P) : recoverProbeVariable (probeVariable z) = some z := by
    cases z with
    | inl i => rfl
    | inr z => cases z with
      | inl k => cases k <;> rfl
      | inr b => cases b <;> rfl
  rw [hid, hid] at h'
  exact Option.some.inj h'

theorem probeValues_coordinates {P : Params} [Fact (Nat.Prime P.q)]
    {pp : PublicParams P} (a : ValidDraw pp) :
    recoveryCoordinates a ∘ probeVariable = recoveryValues a.1.val := by
  funext z
  cases z with
  | inl i => rfl
  | inr z => cases z with
    | inl k => cases k <;> rfl
    | inr b => cases b <;> rfl

theorem probeGrid_roots {P : Params} [Fact (Nat.Prime P.q)] (pp : PublicParams P)
    [Nonempty {c : Coins P // ValidCoins pp.qap c}] (hP : P.Valid)
    (hKD : P.K1 + 1 ≤ P.D) (hDq : P.D < P.q)
    (p : MvPolynomial (ProbeVar P) (Fq P)) (hp : p ≠ 0) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (ValidDraw pp)
    Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryValues a.1.val) p = 0 |
      $ᵗ (ValidDraw pp)] ≤ (p.totalDegree : ENNReal) / ((P.q - P.D : ℕ) : ENNReal) := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (ValidDraw pp)
  have hp' : MvPolynomial.rename probeVariable p ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.rename_injective probeVariable probeVariable_injective) (by simpa using h)
  have h := recoveryGrid_roots pp hP hKD hDq (MvPolynomial.rename probeVariable p) hp'
  have heval (a : ValidDraw pp) :
      MvPolynomial.eval (recoveryCoordinates a) (MvPolynomial.rename probeVariable p) =
        MvPolynomial.eval (recoveryValues a.1.val) p := by
    rw [MvPolynomial.eval_rename, probeValues_coordinates]
  have h' : Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryValues a.1.val) p = 0 |
      $ᵗ (ValidDraw pp)] ≤ ((MvPolynomial.rename probeVariable p).totalDegree : ENNReal) /
        ((P.q - P.D : ℕ) : ENNReal) := by
    simpa only [heval] using h
  exact h'.trans (ENNReal.div_le_div_right (by exact_mod_cast
    (MvPolynomial.totalDegree_rename_le probeVariable p)) _)

theorem recoveryPolynomial_root_bound {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (hP : P.Valid) (hKD : P.K1 + 1 ≤ P.D) (hDq : P.D < P.q)
    (W : Stack P) (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P)
    (hp : recoveryPolynomial W φ ≠ 0) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (ValidDraw pp)
    (Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryValues a.1.val)
      (recoveryPolynomial W φ) = 0 | $ᵗ (ValidDraw pp)]).toReal ≤
        ((P.n + 3 : ℕ) : ℝ) / ((P.q : ℝ) - P.D) := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (ValidDraw pp)
  have hm : (((P.q - P.D : ℕ) : ENNReal)) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hDq).ne'
  have h := probeGrid_roots pp hP hKD hDq (recoveryPolynomial W φ) hp
  have hr := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hm) h
  have hr' : (Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryValues a.1.val)
      (recoveryPolynomial W φ) = 0 | $ᵗ (ValidDraw pp)]).toReal ≤
      ((recoveryPolynomial W φ).totalDegree : ℝ) / ((P.q : ℝ) - P.D) := by
    simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.cast_sub (Nat.le_of_lt hDq)] using hr
  have hden : 0 ≤ (P.q : ℝ) - P.D := by
    apply sub_nonneg.mpr
    exact_mod_cast (Nat.le_of_lt hDq)
  refine hr'.trans (div_le_div_of_nonneg_right ?_ hden)
  have hd := recoveryPolynomial_degree hP W φ
  exact_mod_cast (show (recoveryPolynomial W φ).totalDegree ≤ P.n + 3 by omega)

end Praxis.Proofs.Monitor
