import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Coordinates
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

attribute [local irreducible] KummerPoly

def sigmaLin (s : ℕ) : KPoly (Fq P0) P0.n →ₗ[Fq P0] KPoly (Fq P0) P0.n where
  toFun := sigma P0 s
  map_add' a b := by ext e; simp [sigma, frob, mul_add]
  map_smul' r a := by
    ext e
    change betaF P0 ^ (s * e.val) * (r * a e) = r * (betaF P0 ^ (s * e.val) * a e)
    ring

theorem moore_columns_span {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) :
    Submodule.span (KummerField P0)
      (Set.range (fun j : Fin d => fun i => toK (sigma P0 j.val (a i)))) = ⊤ := by
  let M : Matrix (Fin d) (Fin d) (KummerField P0) :=
    Matrix.of fun i j => toK (sigma P0 j.val (a i))
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (moore_spanning a ha)
  have hs : Function.Surjective M.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  apply top_unique
  intro x _
  obtain ⟨v, rfl⟩ := hs x
  rw [Matrix.mulVec_eq_sum]
  apply Submodule.sum_mem
  intro j _
  have heq : MulOpposite.op (v j) • M.transpose j = v j • (fun i => M i j) := by
    ext i
    change M i j * v j = v j * M i j
    exact mul_comm _ _
  rw [heq]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j, rfl⟩

theorem moore_consecutive_span {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) (s : ℕ) :
    Submodule.span (KummerField P0)
      (Set.range (fun j : Fin d => fun i => toK (sigma P0 (s + j.val) (a i)))) = ⊤ := by
  have hli := ha.map' (sigmaLin s) (LinearMap.ker_eq_bot.mpr (sigma_injective s))
  have h := moore_columns_span (fun i => sigma P0 s (a i)) hli
  simpa only [← sigma_add, Nat.add_comm _ s] using h

theorem moore_three_span {d : ℕ} (a : Fin d → KPoly (Fq P0) P0.n)
    (ha : LinearIndependent (Fq P0) a) (hd : d ≤ 3) (s : ℕ) :
    Submodule.span (KummerField P0)
      (Set.range (fun j : Fin 3 => fun i => toK (sigma P0 (s + j.val) (a i)))) = ⊤ := by
  apply top_unique
  rw [← moore_consecutive_span a ha s]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j.val, lt_of_lt_of_le j.isLt hd⟩, rfl⟩

def restrictedForms {P : Params} [Fact (Nat.Prime P.q)] (v : Fin P.n → Vec (Fq P) P.N)
    (V : Submodule (Fq P) (Vec (Fq P) P.N)) : V →ₗ[Fq P] KPoly (Fq P) P.n :=
  zLin v ∘ₗ V.subtype

theorem restrictedForms_injective {P : Params} [Fact (Nat.Prime P.q)] (v : Fin P.n → Vec (Fq P) P.N)
    (V : Submodule (Fq P) (Vec (Fq P) P.N))
    (hinj : V ⊓ LinearMap.ker (zLin v) = ⊥) : Function.Injective (restrictedForms v V) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have h : (x : Vec (Fq P) P.N) ∈ V ⊓ LinearMap.ker (zLin v) := ⟨x.property, hx⟩
  rw [hinj] at h
  exact Subtype.ext ((Submodule.mem_bot (Fq P)).mp h)

def basisForms {P : Params} [Fact (Nat.Prime P.q)] (v : Fin P.n → Vec (Fq P) P.N)
    (V : Submodule (Fq P) (Vec (Fq P) P.N))
    (r : Fin (Module.finrank (Fq P) V)) : KPoly (Fq P) P.n :=
  restrictedForms v V (Module.finBasis (Fq P) V r)

theorem basisForms_independent {P : Params} [Fact (Nat.Prime P.q)] (v : Fin P.n → Vec (Fq P) P.N)
    (V : Submodule (Fq P) (Vec (Fq P) P.N))
    (hinj : V ⊓ LinearMap.ker (zLin v) = ⊥) :
    LinearIndependent (Fq P) (basisForms v V) := by
  exact (Module.finBasis (Fq P) V).linearIndependent.map' (restrictedForms v V)
    (LinearMap.ker_eq_bot.mpr (restrictedForms_injective v V hinj))

end

end Praxis.Proofs.Classification
