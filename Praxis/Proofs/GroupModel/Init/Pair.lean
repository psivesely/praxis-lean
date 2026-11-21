import Praxis.Proofs.GroupModel.Init.Values
import Praxis.Proofs.GroupModel.Init.Keys
import Praxis.Proofs.View.SZ
import Praxis.Constants
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Proofs.Basic
import Praxis.Proofs.View.Locus
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.GroupModel

open OracleComp OracleSpec

variable {P : Params} [Fact (Nat.Prime P.q)]

private theorem sum_map_sub {I F : Type} [AddCommGroup F] (xs : List I) (f g : I → F) :
    (xs.map fun x => f x - g x).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih]; abel

theorem valT_sub (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (A B : ExprT P) :
    valT pp v ω (A - B) = valT pp v ω A - valT pp v ω B := by
  simp only [valT, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, sum_map_sub]
  ring

theorem valT_pair_gen2 (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (E : Expr1 P) :
    valT pp v ω (pairExpr E (Pi.single none 1)) = val1 pp ω E := by
  simp [valT, val1, pairExpr, keys2, e2At, Pi.single_apply, List.map_map,
    Function.comp_def]

theorem valT_pair_gen1 (pp : PublicParams P) (v : Fin P.n → Algebra.Vec (Fq P) P.N)
    (ω : Assign P) (E : Expr2 P) :
    valT pp v ω (pairExpr (Pi.single none 1) E) = val2 pp v ω E := by
  simp [valT, val2, pairExpr, keys1, e1At, Pi.single_apply, List.map_map,
    Function.comp_def]

theorem g1_initial_pair_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (a b : Option (G1Idx P0))
    (hne : ¬ FormalEq1 (ppOf ch S) (Pi.single a 1) (Pi.single b 1)) :
    (Pr[fun c => e1At (ppOf ch S) (Assign.ofCoins c.1) a =
        e1At (ppOf ch S) (Assign.ofCoins c.1) b |
      coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ) := by
  let D : ExprT P0 := pairExpr (Pi.single a 1) (Pi.single none 1) -
    pairExpr (Pi.single b 1) (Pi.single none 1)
  have hval (ω : Assign P0) : valT (ppOf ch S) (formVec A) ω D =
      e1At (ppOf ch S) ω a - e1At (ppOf ch S) ω b := by
    simp only [D, valT_sub, valT_pair_gen2,
      val1_single _ _ _ keys1_nodup (mem_keys1 _)]
  have hn : ¬ IdentityAtR (ppOf ch S) (formVec A) 0 D 0 := by
    obtain ⟨c, hv, hw⟩ := g1_initial_witness (ppOf ch S) a b keys1_nodup
      (mem_keys1 _) (mem_keys1 _) hne 0
    intro hi
    have h := hi c hv
    simp only [hval, zero_mul, sub_eq_zero] at h
    exact hw h
  have h := View.view_sz ch S hS A D 0 0 hn
  have he : (fun c : {c : Coins P0 // ValidCoins (ppOf ch S).qap c} =>
      e1At (ppOf ch S) (Assign.ofCoins c.1) a = e1At (ppOf ch S) (Assign.ofCoins c.1) b) =
      (fun c => valT (ppOf ch S) (formVec A) ⟨c.1, 0⟩ D = 0 * kappa (ppOf ch S) c.1) := by
    funext c
    apply propext
    simp only [hval, zero_mul, sub_eq_zero, e1At, Assign.ofCoins]
  rw [he]
  exact h

theorem g2_fixed_pair_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (a b : Option (G2Idx P0))
    (r : Algebra.Vec (Fq P0) P0.N)
    (hne : ¬ ∀ c : Coins P0, ValidCoins (ppOf ch S).qap c →
      e2At (ppOf ch S) (formVec A) ⟨c, r⟩ a = e2At (ppOf ch S) (formVec A) ⟨c, r⟩ b) :
    (Pr[fun c => e2At (ppOf ch S) (formVec A) ⟨c.1, r⟩ a =
        e2At (ppOf ch S) (formVec A) ⟨c.1, r⟩ b |
      coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ) := by
  let D : ExprT P0 := pairExpr (Pi.single none 1) (Pi.single a 1) -
    pairExpr (Pi.single none 1) (Pi.single b 1)
  have hval (ω : Assign P0) : valT (ppOf ch S) (formVec A) ω D =
      e2At (ppOf ch S) (formVec A) ω a - e2At (ppOf ch S) (formVec A) ω b := by
    simp only [D, valT_sub, valT_pair_gen1,
      val2_single _ _ _ _ keys2_nodup (mem_keys2 _)]
  have hn : ¬ IdentityAtR (ppOf ch S) (formVec A) r D 0 := by
    intro hi
    apply hne
    intro c hc
    have h := hi c hc
    simpa only [hval, zero_mul, sub_eq_zero] using h
  have h := View.view_sz ch S hS A D r 0 hn
  simpa only [hval, zero_mul, sub_eq_zero] using h

theorem g2_initial_identity_all_search (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (a b : Option (G2Idx P0))
    (r : Algebra.Vec (Fq P0) P0.N)
    (h : ∀ c : Coins P0, ValidCoins (ppOf ch S).qap c →
      e2At (ppOf ch S) (formVec A) ⟨c, r⟩ a =
        e2At (ppOf ch S) (formVec A) ⟨c, r⟩ b) :
    FormalEq2 (ppOf ch S) (formVec A) (Pi.single a 1) (Pi.single b 1) := by
  let D : ExprT P0 := pairExpr (Pi.single none 1) (Pi.single a 1) -
    pairExpr (Pi.single none 1) (Pi.single b 1)
  have hval (ω : Assign P0) : valT (ppOf ch S) (formVec A) ω D =
      e2At (ppOf ch S) (formVec A) ω a - e2At (ppOf ch S) (formVec A) ω b := by
    simp only [D, valT_sub, valT_pair_gen1,
      val2_single _ _ _ _ keys2_nodup (mem_keys2 _)]
  have hi : IdentityAtR (ppOf ch S) (formVec A) r D 0 := by
    intro c hc
    simp only [hval, zero_mul, sub_eq_zero]
    exact h c hc
  have hs (σ : Sector) (c : Cell P0) : exprStack D σ c = 0 := by
    funext i j
    simp [exprStack, D, pairExpr, Pi.single_apply]
  have hc (σ : Sector) (c : Cell P0) : exprSC D σ c = 0 := by
    funext i
    simp [exprSC, D, pairExpr, Pi.single_apply]
  intro ω hv
  have hi' := View.view_locus ch S hS A D r 0 hi ω.r (by
    intro σ c
    rw [hs, hc]
    simp)
  have he := hi' ω.coins hv
  simp only [hval, zero_mul, sub_eq_zero] at he
  simpa only [val2_single _ _ _ _ keys2_nodup (mem_keys2 _)] using he

theorem gt_initial_pair_bound (ch : AdmissibleChoice P0) (S : Relation P0)
    (hS : InShape P0 S) (A : FormMatrix P0) (a b : Option Unit)
    (hne : ¬ FormalEqT (ppOf ch S) (formVec A) (gtInit a) (gtInit b)) :
    (Pr[fun c => valT (ppOf ch S) (formVec A) (Assign.ofCoins c.1) (gtInit a) =
        valT (ppOf ch S) (formVec A) (Assign.ofCoins c.1) (gtInit b) |
      coinLaw (ppOf ch S)]).toReal ≤ (Constants.eps_f : ℝ) := by
  let D : ExprT P0 := gtInit a - gtInit b
  have hn : ¬ IdentityAtR (ppOf ch S) (formVec A) 0 D 0 := by
    obtain ⟨c, hv, hw⟩ := gt_initial_witness (ppOf ch S) (formVec A) a b hne 0
    intro hi
    have h := hi c hv
    simp only [D, valT_sub, zero_mul, sub_eq_zero] at h
    exact hw h
  have h := View.view_sz ch S hS A D 0 0 hn
  have he : (fun c : {c : Coins P0 // ValidCoins (ppOf ch S).qap c} =>
      valT (ppOf ch S) (formVec A) (Assign.ofCoins c.1) (gtInit a) =
        valT (ppOf ch S) (formVec A) (Assign.ofCoins c.1) (gtInit b)) =
      (fun c => valT (ppOf ch S) (formVec A) ⟨c.1, 0⟩ D = 0 * kappa (ppOf ch S) c.1) := by
    funext c
    apply propext
    simp only [D, valT_sub, zero_mul, sub_eq_zero, valT_init, Assign.ofCoins]
  rw [he]
  exact h

end Praxis.Proofs.GroupModel
