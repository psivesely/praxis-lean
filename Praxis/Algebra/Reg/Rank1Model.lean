import Praxis.Algebra.Reg.Definitions
import Praxis.Algebra.Prefix.Definitions
import Praxis.Algebra.Inverse.Definitions

set_option autoImplicit false

set_option maxRecDepth 8192

set_option exponentiation.threshold 512

namespace Praxis.Algebra.Reg.Rank1Model

open Finset Module Praxis.Algebra.Inverse.Definitions Praxis.Algebra.Reg.Definitions Praxis.Algebra.Prefix.Definitions

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun x := x ∘ e
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def Rank1Stretch (L0 : ℕ) {n : ℕ} {κ : Fin (n + 1) → Type*}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 1)
    (width order : Fin n → ℕ) : Prop :=
  7 ≤ L0 →
  (∀ k i, 0 < G k i) →
  (∀ k, 2 ^ L0 ≤ width k) →
  (∀ k, 2 ≤ order k ∧ order k < width k) →
  (∀ k, (L k.succ).H = order k * (L k.castSucc).H) →
  (∀ k, (L k.succ).mZ (G k.succ) ≤
    (L k.castSucc).mZ (G k.castSucc) *
      (((width k + order k - 1) / order k : ℕ) : ℝ) / (width k : ℝ)) →
  (((L (Fin.last n)).mZ (G (Fin.last n)) *
      ((L (Fin.last n)).H : ℝ)) ^ (L0 - 1)) *
      (L (Fin.last n)).mZ (G (Fin.last n)) ≤
    (((L 0).mZ (G 0) * ((L 0).H : ℝ)) ^ (L0 - 1)) * (L 0).mZ (G 0)

def Rank1Promotion (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 1)
    (t : Fin 1 → ℤ) (F : Finset (Grid G)) : Prop :=
  GridBudget P.toVITData G →
  atom G (imageZ G L.matrix) t = L.mZ G →
  F.Nonempty → F ⊆ ordinaryFibre G L t →
  L.mZ G - P.eps ≤ density G F → P.toVITData.mu ≤ density G F →
  (Module.finrank ℤ (ordinaryNormals G F) = 2 ∨
    Module.finrank ℤ (ordinaryNormals G F) = 3 ∨
    ∃ (i : ι) (a : ℤ), (∀ r ∈ F, ((r i : ℕ) : ℤ) = a) ∧
      Pi.single i 1 ∉ L.carrier) →
  (∃ L2 : IntLat ι 2, L.carrier ≤ L2.carrier ∧
    L.mZ G - P.eps ≤ L2.mZ G) ∨
  (∃ L3 : IntLat ι 3, L.carrier ≤ L3.carrier ∧
    L.mZ G - P.eps ≤ L3.mZ G ∧
    (L3.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G L3)

def Rank1Return21 (P : VITParameters) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G2 : ι → ℕ) (L2 : IntLat ι 2)
    (G1 : κ → ℕ) (L1 : IntLat κ 1) (trimmedDensity : ℝ) : Prop :=
  P.toVITData.mu ≤ L1.mZ G1 →
  L1.mZ G1 - P.eps ≤ trimmedDensity →
  Regular P.toVITData G2 L2 →
  trimmedDensity * (L1.H : ℝ) ≤
    P.D * (P.g : ℝ) * (L2.H : ℝ) * L2.mZ G2 →
  L1.mZ G1 * (L1.H : ℝ) ≤ P.A * P.D * P.C2 / (P.g : ℝ)

def Rank1Return31 (P : VITParameters) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G3 : ι → ℕ) (L3 : IntLat ι 3)
    (G1 : κ → ℕ) (L1 : IntLat κ 1) (trimmedDensity : ℝ) : Prop :=
  P.toVITData.mu ≤ L1.mZ G1 →
  L1.mZ G1 - P.eps ≤ trimmedDensity →
  Regular P.toVITData G3 L3 →
  trimmedDensity * (L1.H : ℝ) ≤
    P.E * (P.g : ℝ)^2 * (L3.H : ℝ) * L3.mZ G3 →
  L1.mZ G1 * (L1.H : ℝ) ≤ P.A * P.E * P.C3 / (P.g : ℝ)

def Rank1NestedCall (P : VITParameters) (G : ι → ℕ)
    (L1 : IntLat ι 1) (L2 : IntLat ι 2) : Prop :=
  GridBudget P.toVITData G → P.theta0 - 20 * P.eps ≤ L1.mZ G →
  L1.carrier ≤ L2.carrier → L1.mZ G - P.eps ≤ L2.mZ G →
  Regularize2 P G L2 →
  P.theta0 - 30 * P.eps ≤ L2.mZ G ∧
    ((∃ M2 : IntLat ι 2, L1.carrier ≤ M2.carrier ∧
      L1.mZ G - 2 * P.eps ≤ M2.mZ G ∧ Regular P.toVITData G M2) ∨
     (∃ M3 : IntLat ι 3, L1.carrier ≤ M3.carrier ∧
      L1.mZ G - 2 * P.eps ≤ M3.mZ G ∧
      (M3.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G M3))

end Praxis.Algebra.Reg.Rank1Model
