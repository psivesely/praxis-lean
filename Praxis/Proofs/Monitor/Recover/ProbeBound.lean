import Praxis.Proofs.Monitor.Recover.Span
import Praxis.Enc
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.Monitor.Recover.Helpers
import Praxis.Proofs.Monitor.Recover.Sampling
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Monitor

open Praxis.Algebra (Vec)

open OracleComp OracleSpec

theorem gradient_root_of_mem {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (D : ExprT P) (σ : Sector) (ω : Assign P)
    (U : Submodule (Fq P) (Vec (Fq P) P.N))
    (φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P)
    (hvalid : ValidCoins pp.qap ω.coins)
    (hsym : ∀ cl, (exprStack D σ cl).IsSymm)
    (hnormal : rGrad pp ω D σ = sectorScale ω.coins σ •
      ∑ cl : Cell P, gamma ω.coins cl • ((exprStack D σ cl).transpose.mulVec ω.coins.1))
    (hφ : U.map φ = ⊥) (hmem : rGrad pp ω D σ ∈ U) :
    MvPolynomial.eval (recoveryValues ω.coins) (recoveryPolynomial (exprStack D σ) φ) = 0 := by
  apply recoveryPolynomial_zero_of_mem pp.qap (exprStack D σ) φ U ω.coins σ hvalid hφ
  rw [hnormal] at hmem
  have heq : (∑ cl : Cell P, gamma ω.coins cl •
      ((exprStack D σ cl).transpose.mulVec ω.coins.1)) =
      ∑ cl : Cell P, gamma ω.coins cl • ((exprStack D σ cl).mulVec ω.coins.1) := by
    apply Finset.sum_congr rfl
    intro cl _
    rw [hsym cl]
  rw [heq] at hmem
  exact hmem

theorem oneGradient_bound_of_roots {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (D : ExprT P) (σ : Sector) (ε : ℝ)
    (hsym : ∀ cl, (exprStack D σ cl).IsSymm)
    (hnormal : ∀ ω, ValidCoins pp.qap ω.coins → rGrad pp ω D σ = sectorScale ω.coins σ •
      ∑ cl : Cell P, gamma ω.coins cl • ((exprStack D σ cl).transpose.mulVec ω.coins.1)) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (ValidDraw pp)
    (∀ φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P,
      recoveryPolynomial (exprStack D σ) φ ≠ 0 →
      (Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryValues a.1.val)
        (recoveryPolynomial (exprStack D σ) φ) = 0 | $ᵗ (ValidDraw pp)]).toReal ≤ ε) →
    ∀ U : Submodule (Fq P) (Vec (Fq P) P.N), U < jointSpace (exprStack D σ) →
      (Pr[fun a : ValidDraw pp => rGrad pp (drawAssign a) D σ ∈ U | $ᵗ (ValidDraw pp)]).toReal ≤ ε := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (ValidDraw pp)
  intro hroot U hU
  obtain ⟨cl, j, φ, hcol, hφ⟩ := jointSpace_separating (exprStack D σ) U hU
  have hp := recoveryPolynomial_ne_zero (exprStack D σ) φ cl j hcol
  have hprob : Pr[fun a : ValidDraw pp => rGrad pp (drawAssign a) D σ ∈ U | $ᵗ (ValidDraw pp)] ≤
      Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryValues a.1.val)
        (recoveryPolynomial (exprStack D σ) φ) = 0 | $ᵗ (ValidDraw pp)] := by
    apply probEvent_mono''
    intro a ha
    exact gradient_root_of_mem pp D σ (drawAssign a) U φ a.1.2 hsym (hnormal _ a.1.2) hφ ha
  exact (ENNReal.toReal_mono probEvent_ne_top hprob).trans (hroot φ hp)

theorem sampleGradients_bound_of_roots {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) [Nonempty {c : Coins P // ValidCoins pp.qap c}]
    (D : ExprT P) (σ : Sector) (ε : ℝ) (hε : 0 ≤ ε)
    (hsym : ∀ cl, (exprStack D σ cl).IsSymm)
    (hnormal : ∀ ω, ValidCoins pp.qap ω.coins → rGrad pp ω D σ = sectorScale ω.coins σ •
      ∑ cl : Cell P, gamma ω.coins cl • ((exprStack D σ cl).transpose.mulVec ω.coins.1))
    (hrank : Module.finrank (Fq P) (jointSpace (exprStack D σ)) ≤ 3) :
    letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
    letI := SampleableType.ofFintype (ValidDraw pp)
    (∀ φ : Vec (Fq P) P.N →ₗ[Fq P] Fq P,
      recoveryPolynomial (exprStack D σ) φ ≠ 0 →
      (Pr[fun a : ValidDraw pp => MvPolynomial.eval (recoveryValues a.1.val)
        (recoveryPolynomial (exprStack D σ) φ) = 0 | $ᵗ (ValidDraw pp)]).toReal ≤ ε) →
    (Pr[fun as : Fin 3 → Assign P => Submodule.span (Fq P)
      (Set.range (fun l => rGrad pp (as l) D σ)) ≠ jointSpace (exprStack D σ) |
      sampleAssigns pp 3]).toReal ≤ 3 * ε := by
  classical
  letI : NeZero P.q := ⟨(Fact.out : Nat.Prime P.q).ne_zero⟩
  letI := SampleableType.ofFintype (ValidDraw pp)
  intro hroot
  apply sampleGradients_bound pp D σ (exprStack D σ) ε hε
  · intro a
    exact normalGradient_mem pp D (drawAssign a) σ hsym (hnormal _ a.1.2)
  · exact hrank
  · exact oneGradient_bound_of_roots pp D σ ε hsym hnormal hroot

end Praxis.Proofs.Monitor
