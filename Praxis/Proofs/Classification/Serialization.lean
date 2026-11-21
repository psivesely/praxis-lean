import Praxis.Proofs.Classification.WeightEquations
import Praxis.Grid
import Praxis.Kummer
import Praxis.KummerIrr
import Praxis.Proofs.Basic
import Praxis.Proofs.Classification.Coeff
import Praxis.Proofs.Classification.CoeffMul
import Praxis.Proofs.Classification.Conj
import Praxis.Proofs.Classification.Moore
import Praxis.Proofs.Ties.Grid
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

set_option maxRecDepth 2048

namespace Praxis.Proofs.Classification

open scoped BigOperators

open Praxis.Algebra (Vec Mat)

noncomputable section

local instance : Fact (Irreducible (KummerPoly P0)) := ⟨KummerIrr.main⟩

attribute [local irreducible] KummerPoly

def UField (W : Stack P0) : Matrix (Fin (P0.N + 1)) (Fin (P0.N + 1)) (KummerField P0) :=
  fun i j => toK (fun e => polyU W e i j)

def VField (W : Stack P0) : Matrix (Fin (P0.N + 1)) (Fin (P0.N + 1)) (KummerField P0) :=
  fun i j => toK (fun e => polyV W e i j)

theorem stackU_cell (W : Stack P0) (c : Cell P0) (hc : IsUCell c) :
    stackU W (cellExp c) = W c := by
  classical
  unfold stackU
  apply Finset.sum_eq_single c
  · intro b hb hbc
    have hb' := (Finset.mem_filter.mp hb).2
    exact False.elim (hbc (Proofs.Ties.uCell_exp_bijOn.injOn hb'.1 hc hb'.2))
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, rfl⟩))

theorem stackV_cell (W : Stack P0) (c : Cell P0) (hc : ¬IsUCell c) :
    stackV W (cellExp c / 2) = W c := by
  classical
  have heven := (Proofs.Ties.vCell_exp_bijOn.mapsTo hc).2
  have heq : 2 * (cellExp c / 2) = cellExp c := by
    obtain ⟨a, ha⟩ := heven
    omega
  unfold stackV
  apply Finset.sum_eq_single c
  · intro b hb hbc
    have hb' := (Finset.mem_filter.mp hb).2
    exact False.elim (hbc (Proofs.Ties.vCell_exp_bijOn.injOn hb'.1 hc (hb'.2.trans heq)))
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, heq.symm⟩))

theorem serialization_injective (W W' : Stack P0)
    (hu : UField W = UField W') (hv : VField W = VField W') : W = W' := by
  funext c
  by_cases hc : IsUCell c
  · have hlt := Proofs.Ties.uCell_exp_bijOn.mapsTo hc
    have hp : polyU W = polyU W' := by
      funext e
      ext i j
      exact congrFun (toK_injective (congrFun (congrFun hu i) j)) e
    have h := congrFun hp ⟨cellExp c, hlt⟩
    exact (stackU_cell W c hc).symm.trans (h.trans (stackU_cell W' c hc))
  · have hcprop := Proofs.Ties.vCell_exp_bijOn.mapsTo hc
    have heven : cellExp c % 2 = 0 := Nat.mod_eq_zero_of_dvd hcprop.2.two_dvd
    have hp : polyV W = polyV W' := by
      funext e
      ext i j
      exact congrFun (toK_injective (congrFun (congrFun hv i) j)) e
    have h := congrFun hp ⟨cellExp c, hcprop.1⟩
    simp only [polyV, heven, if_pos] at h
    exact (stackV_cell W c hc).symm.trans (h.trans (stackV_cell W' c hc))

theorem polyU_honest (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Vec (Fq P0) P0.N) (e : Fin P0.n) :
    polyU (honestStack v x) e =
      kmul P0 (zOf v x) (sigma P0 (P0.m - 1) (zOf v x)) e • Matrix.vecMulVec x x := by
  obtain ⟨c, hc, hce⟩ := Proofs.Ties.uCell_exp_bijOn.surjOn (a := e.val) e.isLt
  dsimp only at hce
  unfold polyU
  rw [← hce, stackU_cell _ c hc]
  change weight v x c • Matrix.vecMulVec x x = _
  rw [weight_u v x c hc, Uw, hce, kcoeff, dif_pos e.isLt]

theorem polyV_honest (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Vec (Fq P0) P0.N) (e : Fin P0.n) :
    polyV (honestStack v x) e =
      kmul P0 (zOf v x) (sigma P0 P0.m (zOf v x)) e • Matrix.vecMulVec x x := by
  by_cases he : e.val % 2 = 0
  · have heven : Even e.val := ⟨e.val / 2, by omega⟩
    obtain ⟨c, hc, hce⟩ := Proofs.Ties.vCell_exp_bijOn.surjOn (a := e.val) ⟨e.isLt, heven⟩
    dsimp only at hce
    simp only [polyV, he, if_pos]
    rw [← hce, stackV_cell _ c hc]
    change weight v x c • Matrix.vecMulVec x x = _
    rw [weight_v v x c hc, Vw, hce, show 2 * (e.val / 2) = e.val by omega,
      kcoeff, dif_pos e.isLt]
  · simp only [polyV, if_neg he, norm_coeff_odd_zero v x e he, zero_smul]

theorem toK_mul_const (a : KPoly (Fq P0) P0.n) (r : Fq P0) :
    toK (fun e => a e * r) = toK a * algebraMap (Fq P0) (KummerField P0) r := by
  have h : (fun e => a e * r) = r • a := by ext e; exact mul_comm _ _
  rw [h, toK_smul, mul_comm]

theorem UField_honest (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Vec (Fq P0) P0.N) :
    UField (honestStack v x) = (Z v x * kConj (P0.m - 1) (Z v x)) •
      Matrix.vecMulVec (fun i => algebraMap (Fq P0) (KummerField P0) (x i))
        (fun i => algebraMap (Fq P0) (KummerField P0) (x i)) := by
  ext i j
  simp only [UField, polyU_honest, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [show (fun e => kmul P0 (zOf v x) (sigma P0 (P0.m - 1) (zOf v x)) e * (x i * x j)) =
      (fun e => (kmul P0 (zOf v x) (sigma P0 (P0.m - 1) (zOf v x)) e * x i) * x j) by
        funext e; ring,
    toK_mul_const, toK_mul_const, toK_kmul, ← kConj_toK]
  simp only [Z, mul_assoc]

theorem VField_honest (v : Fin P0.n → Vec (Fq P0) P0.N)
    (x : Vec (Fq P0) P0.N) :
    VField (honestStack v x) = (Z v x * kConj P0.m (Z v x)) •
      Matrix.vecMulVec (fun i => algebraMap (Fq P0) (KummerField P0) (x i))
        (fun i => algebraMap (Fq P0) (KummerField P0) (x i)) := by
  ext i j
  simp only [VField, polyV_honest, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [show (fun e => kmul P0 (zOf v x) (sigma P0 P0.m (zOf v x)) e * (x i * x j)) =
      (fun e => (kmul P0 (zOf v x) (sigma P0 P0.m (zOf v x)) e * x i) * x j) by
        funext e; ring,
    toK_mul_const, toK_mul_const, toK_kmul, ← kConj_toK]
  simp only [Z, mul_assoc]

theorem polyU_add (W W' : Stack P0) : polyU (P := P0) (fun c => W c + W' c) =
    (fun e => polyU W e + polyU W' e) := by
  funext e
  simp only [polyU, stackU, Pi.add_apply, Finset.sum_add_distrib]

theorem polyU_smul (r : Fq P0) (W : Stack P0) : polyU (r • W) = r • polyU W := by
  funext e
  simp only [polyU, stackU, Pi.smul_apply, Finset.smul_sum]

theorem polyV_add (W W' : Stack P0) : polyV (P := P0) (fun c => W c + W' c) =
    (fun e => polyV W e + polyV W' e) := by
  funext e
  simp only [polyV, stackV, Pi.add_apply]
  split_ifs <;> simp only [Finset.sum_add_distrib, add_zero]

theorem polyV_smul (r : Fq P0) (W : Stack P0) : polyV (r • W) = r • polyV W := by
  funext e
  simp only [polyV, stackV, Pi.smul_apply]
  split_ifs <;> simp only [Finset.smul_sum, smul_zero]

def ULinear : Stack P0 →ₗ[Fq P0]
    Matrix (Fin (P0.N + 1)) (Fin (P0.N + 1)) (KummerField P0) where
  toFun := UField
  map_add' W W' := by
    ext i j
    change UField (fun c => W c + W' c) i j = (UField W + UField W') i j
    simp only [UField, polyU_add, Pi.add_apply, Matrix.add_apply]
    exact toK_add (fun e => polyU W e i j) (fun e => polyU W' e i j)
  map_smul' r W := by
    ext i j
    simp only [UField, polyU_smul, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    exact (toK_smul r _).trans (Algebra.smul_def _ _).symm

def VLinear : Stack P0 →ₗ[Fq P0]
    Matrix (Fin (P0.N + 1)) (Fin (P0.N + 1)) (KummerField P0) where
  toFun := VField
  map_add' W W' := by
    ext i j
    change VField (fun c => W c + W' c) i j = (VField W + VField W') i j
    simp only [VField, polyV_add, Pi.add_apply, Matrix.add_apply]
    exact toK_add (fun e => polyV W e i j) (fun e => polyV W' e i j)
  map_smul' r W := by
    ext i j
    simp only [VField, polyV_smul, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    exact (toK_smul r _).trans (Algebra.smul_def _ _).symm

theorem ULinear_apply (W : Stack P0) : ULinear W = UField W := rfl

theorem VLinear_apply (W : Stack P0) : VLinear W = VField W := rfl

theorem VField_fixed (W : Stack P0) : (VField W).map (kConj P0.m) = VField W := by
  ext i j
  simp only [Matrix.map_apply, VField]
  rw [kConj_toK]
  apply congrArg toK
  funext e
  change betaF P0 ^ (P0.m * e.val) * polyV W e i j = polyV W e i j
  by_cases he : e.val % 2 = 0
  · have hpow : betaF P0 ^ (P0.m * e.val) = 1 := by
      rw [pow_mul, KummerIrr.main_betaLaws.2.2]
      exact (show Even e.val from ⟨e.val / 2, by omega⟩).neg_one_pow
    rw [hpow, one_mul]
  · simp only [polyV, if_neg he, Matrix.zero_apply, mul_zero]

end

end Praxis.Proofs.Classification
