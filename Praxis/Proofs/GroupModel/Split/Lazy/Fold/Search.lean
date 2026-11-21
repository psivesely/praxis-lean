import Praxis.Proofs.GroupModel.Split.Lazy.FoldModel
import Praxis.Domain
import Praxis.Enc
import Praxis.Proofs.Basic
import Praxis.Proofs.GroupModel.Split.Disintegration
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

open Praxis Praxis.Proofs Praxis.Algebra

noncomputable section

set_option autoImplicit false

namespace Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Search

private lemma values_search_indep {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (c c' : Coins P) (r : Vec (Fq P) P.N) (h1 : c'.1 = c.1)
    (h2 : c'.2.2 = c.2.2) :
    (∀ E, val1 pp ⟨c', r⟩ E = val1 pp ⟨c, r⟩ E) ∧
    (∀ v E, val2 pp v ⟨c', r⟩ E = val2 pp v ⟨c, r⟩ E) ∧
    (∀ v E, valT pp v ⟨c', r⟩ E = valT pp v ⟨c, r⟩ E) ∧
    kappa pp c' = kappa pp c := by
  have he1 (a : Option (G1Idx P)) :
      e1At pp ⟨c', r⟩ a = e1At pp ⟨c, r⟩ a := by
    cases a with
    | none => rfl
    | some a =>
      cases a <;> simp [e1At, g1Exp, piAt, coin, h1, h2]
  have he2 (v : Fin P.n → Vec (Fq P) P.N) (a : Option (G2Idx P)) :
      e2At pp v ⟨c', r⟩ a = e2At pp v ⟨c, r⟩ a := by
    cases a with
    | none => rfl
    | some a =>
      cases a <;> simp [e2At, g2Exp, r1ExpAt, r2Exp, H2, legScale, legScaleAt, bOf,
        coin, sectorScale, legMask, gamma, piAt, crossVal, cTie, kummerAtU, h1, h2]
  have hk : kappa pp c' = kappa pp c := by
    simp [kappa, gammaKey, piAt, legScaleAt, bOf, coin, h2]
  refine ⟨?_, ?_, ?_, hk⟩
  · intro E
    simp only [val1, he1]
  · intro v E
    simp only [val2, he2]
  · intro v E
    simp only [valT, he1, he2, gtExp, hk, coin, h2]

lemma val_search_indep (ch : AdmissibleChoice P0) (S : Relation P0)
    (c c' : Coins P0) (r : Vec k P0.N) (h1 : c'.1 = c.1)
    (h2 : c'.2.2 = c.2.2) :
    (∀ E, val1 (ppOf ch S) ⟨c', r⟩ E = val1 (ppOf ch S) ⟨c, r⟩ E) ∧
    (∀ v E, val2 (ppOf ch S) v ⟨c', r⟩ E = val2 (ppOf ch S) v ⟨c, r⟩ E) ∧
    (∀ v E, valT (ppOf ch S) v ⟨c', r⟩ E = valT (ppOf ch S) v ⟨c, r⟩ E) ∧
    kappa (ppOf ch S) c' = kappa (ppOf ch S) c := by
  exact values_search_indep (ppOf ch S) c c' r h1 h2

end Praxis.Proofs.GroupModel.Split.Lazy.Disintegration.Fold.Search
