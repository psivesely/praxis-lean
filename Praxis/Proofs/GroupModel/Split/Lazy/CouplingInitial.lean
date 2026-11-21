import Praxis.Proofs.GroupModel.Split.Lazy.Coupling
import Praxis.Enc
import Praxis.Grid
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

open Praxis Praxis.Proofs Praxis.Algebra OracleComp OracleSpec

noncomputable section

set_option autoImplicit false

set_option maxRecDepth 4096

namespace Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic

variable (P : Params)

private lemma nodup_flatMap_map {α β γ : Type} (l : List α) (m : List β)
    (hl : l.Nodup) (hm : m.Nodup) (f : α → β → γ)
    (hf : Function.Injective fun p : α × β => f p.1 p.2) :
    (l.flatMap fun a => m.map (f a)).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun a _ => hm.map ?_, hl.imp ?_⟩
  · intro b b' h
    exact congrArg Prod.snd (@hf (a, b) (a, b') h)
  · intro a a' hne
    rw [Function.onFun, List.disjoint_left]
    rintro z hz hz'
    rcases List.mem_map.mp hz with ⟨b, _, rfl⟩
    rcases List.mem_map.mp hz' with ⟨b', _, he⟩
    exact hne (congrArg Prod.fst (@hf (a, b) (a', b') he.symm))

lemma g1Order_nodup : (g1Order P).Nodup := by
  classical
  have hL1 := nodup_flatMap_map _ _ (List.nodup_finRange P.K1)
    (List.nodup_finRange (P.N + 1)) (@G1Idx.L1 P) (by
      intro a b h; exact Prod.ext (G1Idx.L1.inj h).1 (G1Idx.L1.inj h).2)
  have hL2 := nodup_flatMap_map _ _ (List.nodup_finRange P.K1)
    (List.nodup_finRange (P.N + 1)) (@G1Idx.L2 P) (by
      intro a b h; exact Prod.ext (G1Idx.L2.inj h).1 (G1Idx.L2.inj h).2)
  have ht1 := (List.nodup_finRange P.K1).map (@G1Idx.totL1.inj P)
  have ht2 := (List.nodup_finRange P.K1).map (@G1Idx.totL2.inj P)
  have hQ := (List.nodup_finRange P.E1).map (@G1Idx.QP.inj P)
  have hY := (List.nodup_finRange (P.N + 1)).map (@G1Idx.GY.inj P)
  have hR : (List.filterMap (fun s : Fin (P.U * P.E1p) =>
      if h : P.U ∣ s.val then none else some (G1Idx.RP ⟨s, h⟩))
      (List.finRange (P.U * P.E1p))).Nodup := by
    apply (List.nodup_finRange _).filterMap
    intro a a' b h h'
    split_ifs at h h' with ha ha' <;> simp_all
    exact congrArg Subtype.val (G1Idx.RP.inj (h.trans h'.symm))
  simp only [g1Order, List.nodup_append, hL1, hL2, ht1, ht2, hQ, hY, hR,
    List.mem_flatMap, List.mem_map, List.mem_filterMap]
  aesop

lemma legList_nodup : (legList P).Nodup := by
  exact nodup_flatMap_map [LegKind.E, .O, .V] _ (by decide)
    (List.nodup_finRange P.K2) Prod.mk (fun _ _ h => h)

lemma cellList_nodup : (cellList P).Nodup := by
  exact nodup_flatMap_map _ _ (List.nodup_finRange P.K1)
    (legList_nodup P) Prod.mk (fun _ _ h => h)

set_option maxHeartbeats 800000 in
lemma g2OrderSector_nodup (σ : Sector) : (g2OrderSector P σ).Nodup := by
  classical
  have hR1 := nodup_flatMap_map _ _ (legList_nodup P)
    (List.nodup_finRange (P.N + 1)) (G2Idx.ZeroCoordinate σ) (by
      intro a b h; exact Prod.ext (G2Idx.ZeroCoordinate.inj h).2.1 (G2Idx.ZeroCoordinate.inj h).2.2)
  have hR2 := nodup_flatMap_map _ _ (legList_nodup P)
    (List.nodup_finRange (P.N + 1)) (G2Idx.R2 σ) (by
      intro a b h; exact Prod.ext (G2Idx.R2.inj h).2.1 (G2Idx.R2.inj h).2.2)
  have ht1 := (legList_nodup P).map (f := G2Idx.totR1 σ) (fun _ _ h => (G2Idx.totR1.inj h).2)
  have ht2 := (legList_nodup P).map (f := G2Idx.totR2 σ) (fun _ _ h => (G2Idx.totR2.inj h).2)
  have hQ := nodup_flatMap_map _ _ (cellList_nodup P)
    (List.nodup_finRange P.Mq) (G2Idx.QB σ) (by
      intro a b h; exact Prod.ext (G2Idx.QB.inj h).2.1 (G2Idx.QB.inj h).2.2)
  have hB := nodup_flatMap_map _ _ (cellList_nodup P)
    (List.nodup_finRange P.Wr) (G2Idx.RB σ) (by
      intro a b h; exact Prod.ext (G2Idx.RB.inj h).2.1 (G2Idx.RB.inj h).2.2)
  have hS := (legList_nodup P).map (f := G2Idx.SC σ) (fun _ _ h => (G2Idx.SC.inj h).2)
  have hG (g : CrossIdx) :
      (List.map (G2Idx.GB σ g) (List.finRange (2 * P.n - 1))).Nodup :=
    (List.nodup_finRange _).map (fun _ _ h => (G2Idx.GB.inj h).2.2)
  have hM (s : TieIdx) :
      (List.map (G2Idx.GM σ s) (List.finRange (P.n - 1))).Nodup :=
    (List.nodup_finRange _).map (fun _ _ h => (G2Idx.GM.inj h).2.2)
  simp [g2OrderSector, List.nodup_append, hR1, hR2, ht1, ht2, hQ, hB, hS, hG, hM,
    List.mem_append, List.mem_flatMap, List.mem_map]
  aesop

lemma g2Order_nodup : (g2Order P).Nodup := by
  simp only [g2Order, List.nodup_append, g2OrderSector_nodup, true_and]
  simp only [g2OrderSector, List.mem_append, List.mem_flatMap, List.mem_map]
  aesop

lemma g1Order_complete (i : G1Idx P) : i ∈ g1Order P := by
  cases i <;> simp [g1Order, List.mem_flatMap, List.mem_filterMap]
  aesop

lemma legList_complete (l : Leg P) : l ∈ legList P := by
  rcases l with ⟨X, k⟩
  cases X <;> simp [legList]

lemma cellList_complete (c : Cell P) : c ∈ cellList P := by
  rcases c with ⟨i, l⟩
  simp [cellList, List.mem_flatMap, legList_complete]

lemma g2Order_complete (i : G2Idx P) : i ∈ g2Order P := by
  cases i <;> simp [g2Order, g2OrderSector, List.mem_flatMap,
    legList_complete, cellList_complete]
  all_goals aesop (add safe cases [Sector, CrossIdx, TieIdx])

lemma keys1_nodup : (keys1 P).Nodup := by
  unfold keys1
  exact List.nodup_cons.mpr ⟨by simp, (g1Order_nodup P).map (Option.some_injective _)⟩

lemma keys2_nodup : (keys2 P).Nodup := by
  unfold keys2
  exact List.nodup_cons.mpr ⟨by simp, (g2Order_nodup P).map (Option.some_injective _)⟩

lemma keys1_complete (a : Option (G1Idx P)) : a ∈ keys1 P := by
  cases a <;> simp [keys1, g1Order_complete]

lemma keys2_complete (a : Option (G2Idx P)) : a ∈ keys2 P := by
  cases a <;> simp [keys2, g2Order_complete]

private lemma sum_single_mul {K α : Type} [CommRing K] [DecidableEq α]
    (l : List α) (hl : l.Nodup) (a : α) (ha : a ∈ l) (c : K) (f : α → K) :
    (l.map (fun x => (Pi.single a c : α → K) x * f x)).sum = c * f a := by
  rw [List.sum_map_eq_nsmul_single a _ (by
    intro x hx _
    simp [hx.symm])]
  simp [List.count_eq_one_of_mem hl ha]

variable {P : Params} [Fact (Nat.Prime P.q)]

variable (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N) (ω : Assign P)

@[simp] lemma val1_zero : val1 pp ω (0 : Expr1 P) = 0 := by simp [val1]

@[simp] lemma val2_zero : val2 pp v ω (0 : Expr2 P) = 0 := by simp [val2]

lemma val1_single (a : Option (G1Idx P)) (c : Fq P) :
    val1 pp ω (Pi.single a c) = c * e1At pp ω a := by
  exact sum_single_mul _ (keys1_nodup P) a (keys1_complete P a) c _

lemma val2_single (a : Option (G2Idx P)) (c : Fq P) :
    val2 pp v ω (Pi.single a c) = c * e2At pp v ω a := by
  exact sum_single_mul _ (keys2_nodup P) a (keys2_complete P a) c _

lemma valT_gtInit (i : Option Unit) :
    valT pp v ω (gtInit i) = match i with
      | none => 1
      | some () => gtExp pp ω.coins := by
  cases i with
  | none => simp [valT, gtInit, keys1, keys2, e1At, e2At, Pi.single_apply, Function.comp_def]
  | some i => cases i; simp [valT, gtInit]

end Praxis.Proofs.GroupModel.Split.Lazy.Coupling.Symbolic
