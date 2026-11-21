import Praxis.Algebra.Inverse.Definitions
import Praxis.Algebra.DifferenceLattice.Definitions
import Praxis.Algebra.InverseBranches.NormalBranches

set_option autoImplicit false

namespace Praxis.Algebra.Reg.Definitions

open Finset Module Praxis.Algebra.Inverse.Definitions

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def density (G : ι → ℕ) (F : Finset (Grid G)) : ℝ :=
  (F.card : ℝ) / (Fintype.card (Grid G) : ℝ)

noncomputable def ordinaryFibre {d : ℕ} (G : ι → ℕ)
    (L : IntLat ι d) (t : Fin d → ℤ) : Finset (Grid G) :=
  univ.filter fun r => imageZ G L.matrix r = t

def ordinaryNormals (G : ι → ℕ) (F : Finset (Grid G)) :
    Submodule ℤ (ι → ℤ) :=
  Algebra.VectorInverse.normalLattice (Algebra.DifferenceLattice.differenceLattice 0 F)

def Rank3Height (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 3) : Prop :=
  GridBudget P.toVITData G → P.toVITData.mu ≤ L.mZ G →
    (L.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G L

def Regularize2 (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 2) : Prop :=
  GridBudget P.toVITData G → P.theta0 - 30 * P.eps ≤ L.mZ G →
    Regular P.toVITData G L ∨
      ∃ L3 : IntLat ι 3, L.carrier ≤ L3.carrier ∧
        L.mZ G - P.eps ≤ L3.mZ G ∧
        (L3.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G L3

def Regularize1 (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 1) : Prop :=
  GridBudget P.toVITData G → P.theta0 - 20 * P.eps ≤ L.mZ G →
    Regular P.toVITData G L ∨
      (∃ L2 : IntLat ι 2, L.carrier ≤ L2.carrier ∧
        L.mZ G - 2 * P.eps ≤ L2.mZ G ∧ Regular P.toVITData G L2) ∨
      (∃ L3 : IntLat ι 3, L.carrier ≤ L3.carrier ∧
        L.mZ G - 2 * P.eps ≤ L3.mZ G ∧
        (L3.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G L3)

def Rank2Stretch (L0 : ℕ) {n : ℕ} {κ : Fin (n + 1) → Type*}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]
    (G : (k : Fin (n + 1)) → κ k → ℕ)
    (L : (k : Fin (n + 1)) → IntLat (κ k) 2)
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

def Rank2Promotion (P : VITParameters) (G : ι → ℕ) (L : IntLat ι 2)
    (t : Fin 2 → ℤ) (F : Finset (Grid G)) : Prop :=
  GridBudget P.toVITData G →
  atom G (imageZ G L.matrix) t = L.mZ G →
  F.Nonempty → F ⊆ ordinaryFibre G L t →
  L.mZ G - P.eps ≤ density G F → P.toVITData.mu ≤ density G F →
  (Module.finrank ℤ (ordinaryNormals G F) = 3 ∨
    ∃ (i : ι) (a : ℤ), (∀ r ∈ F, ((r i : ℕ) : ℤ) = a) ∧
      Pi.single i 1 ∉ L.carrier) →
  ∃ L3 : IntLat ι 3, L.carrier ≤ L3.carrier ∧
    L.mZ G - P.eps ≤ L3.mZ G ∧
    (L3.H : ℝ) ≤ P.toVITData.H3 ∧ Regular P.toVITData G L3

def Rank2Return (P : VITParameters) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G3 : ι → ℕ) (L3 : IntLat ι 3)
    (G2 : κ → ℕ) (L2 : IntLat κ 2) (trimmedDensity : ℝ) : Prop :=
  P.toVITData.mu ≤ L2.mZ G2 →
  L2.mZ G2 - P.eps ≤ trimmedDensity →
  Regular P.toVITData G3 L3 →
  trimmedDensity * (L2.H : ℝ) ≤
    P.D * (P.g : ℝ) * (L3.H : ℝ) * L3.mZ G3 →
  L2.mZ G2 * (L2.H : ℝ) ≤ P.A * P.D * P.C3 / (P.g : ℝ)^2

end Praxis.Algebra.Reg.Definitions

set_option autoImplicit false

set_option maxRecDepth 4096

set_option exponentiation.threshold 512
