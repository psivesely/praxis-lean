import Praxis.Proofs.Basic
import Praxis.Domain
import Praxis.Params
import Praxis.QAP
import Praxis.Relation
import Praxis.Setting

namespace Praxis.Proofs.QAP

open Polynomial

private theorem card_index (P : Params) :
    Fintype.card (QAPIndex P) = P.N + 2 + P.U * P.gatesMax := by
  simp only [QAPIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit]
  ring

private theorem eval_interp {P : Params} [Fact (Nat.Prime P.q)]
    (pts : RowPoints P) (h : Function.Injective pts.point)
    (r : QAPIndex P → Fq P) (k : QAPIndex P) :
    (pts.interp r).eval (pts.point k) = r k :=
  Lagrange.eval_interpolate_at_node r (fun _ _ _ _ e => h e) (Finset.mem_univ k)

private theorem interp_degree {P : Params} [Fact (Nat.Prime P.q)]
    (hD : P.D = P.N + 2 + P.U * P.gatesMax)
    (pts : RowPoints P) (h : Function.Injective pts.point)
    (r : QAPIndex P → Fq P) : (pts.interp r).natDegree < P.D := by
  have hd := Lagrange.degree_interpolate_lt r (s := Finset.univ) (v := pts.point)
    (fun _ _ _ _ e => h e)
  rw [Finset.card_univ, card_index, ← hD] at hd
  by_cases h0 : pts.interp r = 0
  · rw [h0, natDegree_zero]
    rw [hD]
    omega
  · exact (natDegree_lt_iff_degree_lt h0).mpr hd

private theorem domainMap_valid_of_size {P : Params} [Fact (Nat.Prime P.q)]
    (hD : P.D = P.N + 2 + P.U * P.gatesMax)
    (ch : AdmissibleChoice P) (S : Relation P) :
    ValidQAP (domainMap ch S) S := by
  let pts := ch.1
  have h : Function.Injective pts.point := ch.2.distinct
  have hp : (pts.toQAP S).point = pts.point := by
    funext k
    rcases k with i | _ | tj <;> rfl
  change ValidQAP (pts.toQAP S) S
  refine {
    distinct := ?_
    mu_order := ch.2.mu_order
    cosets_distinct := ch.2.cosets_distinct
    Z0_eq := rfl
    Z_eq := rfl
    Lrho_degree := interp_degree hD pts h _
    Lrho_eval := ?_
    A_degree := fun i => interp_degree hD pts h _
    B_degree := fun i => interp_degree hD pts h _
    A_col := ?_
    B_col := ?_
    A_rho := ?_
    B_rho := ?_
    A_gate := ?_
    B_gate := ?_ }
  · rw [hp]; exact h
  · intro k
    rw [hp]
    exact eval_interp pts h _ k
  · intro i j
    exact eval_interp pts h (pts.aVal S i) (.inl j)
  · intro i j
    exact eval_interp pts h (pts.bVal S i) (.inl j)
  · intro i
    exact eval_interp pts h (pts.aVal S i) (.inr (.inl ()))
  · intro i
    exact eval_interp pts h (pts.bVal S i) (.inr (.inl ()))
  · intro t j i
    exact eval_interp pts h (pts.aVal S i) (.inr (.inr (t, j)))
  · intro t j i
    exact eval_interp pts h (pts.bVal S i) (.inr (.inr (t, j)))

theorem domainMap_valid (ch : AdmissibleChoice P0) (S : Relation P0) :
    ValidQAP (domainMap ch S) S :=
  domainMap_valid_of_size (by decide +kernel) ch S

end Praxis.Proofs.QAP
