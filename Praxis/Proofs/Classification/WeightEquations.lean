import Praxis.Proofs.Classification.CoeffMul
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Ties.Grid
import Praxis.Grid
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Coeff
import Praxis.Proofs.Classification.Moore
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

open Praxis.Algebra (Vec)

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

local instance : NeZero P0.n := ⟨by decide⟩

attribute [local irreducible] KummerPoly

def Z (v : Fin P0.n → Vec (Fq P0) P0.N) (x : Vec (Fq P0) P0.N) : KummerField P0 :=
  toK (zOf v x)

theorem kConj_m_norm (z : KummerField P0) :
    kConj P0.m (z * kConj P0.m z) = z * kConj P0.m z := by
  rw [map_mul, ← kConj_add, show P0.m + P0.m = P0.n by decide, kConj_n, mul_comm]

theorem sigma_m_odd_zero (a : KPoly (Fq P0) P0.n) (h : sigma P0 P0.m a = a)
    (e : Fin P0.n) (he : e.val % 2 ≠ 0) : a e = 0 := by
  have hpow : betaF P0 ^ (P0.m * e.val) = -1 := by
    rw [pow_mul, KummerIrr.main_betaLaws.2.2]
    exact (show Odd e.val from ⟨e.val / 2, by omega⟩).neg_one_pow
  have h' := congrFun h e
  change betaF P0 ^ (P0.m * e.val) * a e = a e at h'
  rw [hpow, neg_one_mul] at h'
  have htwo : (2 : Fq P0) ≠ 0 := by decide
  have hzero : (2 : Fq P0) * a e = 0 := by linear_combination -h'
  exact (mul_eq_zero.mp hzero).resolve_left htwo

theorem norm_coeff_odd_zero (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Vec (Fq P0) P0.N) (e : Fin P0.n) (he : e.val % 2 ≠ 0) :
    kmul P0 (zOf v x) (sigma P0 P0.m (zOf v x)) e = 0 := by
  apply sigma_m_odd_zero _ _ e he
  apply toK_injective
  rw [← kConj_toK, toK_kmul, ← kConj_toK, kConj_m_norm]

theorem weight_u (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Vec (Fq P0) P0.N) (c : Cell P0) (hc : IsUCell c) :
    weight v x c = Uw v x (cellExp c) := by
  exact if_neg hc

theorem weight_v (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Vec (Fq P0) P0.N) (c : Cell P0) (hc : ¬IsUCell c) :
    weight v x c = Vw v x (cellExp c / 2) := by
  exact if_pos (not_not.mp hc)

end

end Praxis.Proofs.Classification
