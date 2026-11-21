import Praxis.Proofs.GroupModel.Init.Counts
import Praxis.Grid
import Praxis.Params
import Praxis.Published
import Praxis.Reduction

namespace Praxis.Proofs.GroupModel

theorem mem_legList {P : Params} (l : Leg P) : l ∈ legList P := by
  rcases l with ⟨X, k⟩
  cases X <;> simp [legList]

theorem mem_cellList {P : Params} (c : Cell P) : c ∈ cellList P := by
  rcases c with ⟨k, l⟩
  simp [cellList, mem_legList]

theorem mem_g1Order {P : Params} (a : G1Idx P) : a ∈ g1Order P := by
  cases a with
  | RP s =>
    have hm : G1Idx.RP s ∈ ((List.finRange (P.U * P.E1p)).filterMap fun t =>
        if h : P.U ∣ t.val then none else some (G1Idx.RP ⟨t, h⟩)) := by
      apply List.mem_filterMap.mpr
      exact ⟨s.1, List.mem_finRange _, by simp [s.2]⟩
    simp [g1Order, hm]
  | _ => simp [g1Order]

theorem mem_g2OrderSector {P : Params} (a : G2Idx P) (σ : Sector)
    (h : match a with
      | .ZeroCoordinate s _ _ | .R2 s _ _ | .totR1 s _ | .totR2 s _ | .QB s _ _ |
        .RB s _ _ | .SC s _ | .GB s _ _ | .GM s _ _ => s = σ) :
    a ∈ g2OrderSector P σ := by
  cases a with
  | ZeroCoordinate s l j => subst s; simp [g2OrderSector, mem_legList]
  | R2 s l j => subst s; simp [g2OrderSector, mem_legList]
  | totR1 s l => subst s; simp [g2OrderSector, mem_legList]
  | totR2 s l => subst s; simp [g2OrderSector, mem_legList]
  | QB s c j => subst s; simp [g2OrderSector, mem_cellList]
  | RB s c j => subst s; simp [g2OrderSector, mem_cellList]
  | SC s l => subst s; simp [g2OrderSector, mem_legList]
  | GB s g e => subst s; cases g <;> simp [g2OrderSector]
  | GM s t e => subst s; cases t <;> simp [g2OrderSector]

theorem mem_g2Order {P : Params} (a : G2Idx P) : a ∈ g2Order P := by
  cases a with
  | ZeroCoordinate s l j =>
    have h := mem_g2OrderSector (G2Idx.ZeroCoordinate s l j) s rfl
    cases s <;> simp [g2Order, h]
  | R2 s l j =>
    have h := mem_g2OrderSector (G2Idx.R2 s l j) s rfl
    cases s <;> simp [g2Order, h]
  | totR1 s l =>
    have h := mem_g2OrderSector (G2Idx.totR1 s l) s rfl
    cases s <;> simp [g2Order, h]
  | totR2 s l =>
    have h := mem_g2OrderSector (G2Idx.totR2 s l) s rfl
    cases s <;> simp [g2Order, h]
  | QB s c j =>
    have h := mem_g2OrderSector (G2Idx.QB s c j) s rfl
    cases s <;> simp [g2Order, h]
  | RB s c j =>
    have h := mem_g2OrderSector (G2Idx.RB s c j) s rfl
    cases s <;> simp [g2Order, h]
  | SC s l =>
    have h := mem_g2OrderSector (G2Idx.SC s l) s rfl
    cases s <;> simp [g2Order, h]
  | GB s g e =>
    have h := mem_g2OrderSector (G2Idx.GB s g e) s rfl
    cases s <;> simp [g2Order, h]
  | GM s t e =>
    have h := mem_g2OrderSector (G2Idx.GM s t e) s rfl
    cases s <;> simp [g2Order, h]

theorem mem_keys1 {P : Params} (a : Option (G1Idx P)) : a ∈ keys1 P := by
  cases a with
  | none => simp [keys1]
  | some a => simp [keys1, mem_g1Order]

theorem mem_keys2 {P : Params} (a : Option (G2Idx P)) : a ∈ keys2 P := by
  cases a with
  | none => simp [keys2]
  | some a => simp [keys2, mem_g2Order]

private theorem nodup_flatMap_map {A B C : Type} (xs : List A) (ys : List B)
    (hx : xs.Nodup) (hy : ys.Nodup) (f : A → B → C)
    (hf : ∀ a b a' b', f a b = f a' b' → a = a' ∧ b = b') :
    (xs.flatMap fun a => ys.map (f a)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨?_, hx.imp ?_⟩
  · intro a _
    apply hy.map
    intro b b' h
    exact (hf a b a b' h).2
  · intro a a' hn c hc hc'
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨b', _, h⟩ := List.mem_map.mp hc'
    exact hn (hf a' b' a b h).1.symm

theorem g1Order_nodup {P : Params} : (g1Order P).Nodup := by
  have h1 : (((List.finRange P.K1).flatMap fun k =>
      (List.finRange (P.N + 1)).map (G1Idx.L1 k)) : List (G1Idx P)).Nodup := by
    apply nodup_flatMap_map _ _ (List.nodup_finRange _) (List.nodup_finRange _)
    intro a b a' b' h
    cases h
    exact ⟨rfl, rfl⟩
  have h2 : (((List.finRange P.K1).flatMap fun k =>
      (List.finRange (P.N + 1)).map (G1Idx.L2 k)) : List (G1Idx P)).Nodup := by
    apply nodup_flatMap_map _ _ (List.nodup_finRange _) (List.nodup_finRange _)
    intro a b a' b' h
    cases h
    exact ⟨rfl, rfl⟩
  have hr : (((List.finRange (P.U * P.E1p)).filterMap fun s =>
      if h : P.U ∣ s.val then none else some (G1Idx.RP (P := P) ⟨s, h⟩))).Nodup := by
    apply List.Nodup.filterMap _ (List.nodup_finRange _)
    intro a b c ha hb
    split at ha <;> split at hb <;> simp_all
    cases ha.trans hb.symm
    rfl
  have ht1 : ((List.finRange P.K1).map (G1Idx.totL1 (P := P))).Nodup :=
    (List.nodup_finRange _).map (by intro x y h; cases h; rfl)
  have ht2 : ((List.finRange P.K1).map (G1Idx.totL2 (P := P))).Nodup :=
    (List.nodup_finRange _).map (by intro x y h; cases h; rfl)
  have hq : ((List.finRange P.E1).map (G1Idx.QP (P := P))).Nodup :=
    (List.nodup_finRange _).map (by intro x y h; cases h; rfl)
  have hg : ((List.finRange (P.N + 1)).map (G1Idx.GY (P := P))).Nodup :=
    (List.nodup_finRange _).map (by intro x y h; cases h; rfl)
  simp only [g1Order, List.nodup_append]
  simp [h1, h2, hr, ht1, ht2, hq, hg, List.mem_flatMap]
  aesop

theorem keys1_nodup {P : Params} : (keys1 P).Nodup := by
  have hm := (g1Order_nodup (P := P)).map (Option.some_injective _)
  simpa [keys1] using hm

theorem legList_nodup {P : Params} : (legList P).Nodup := by
  apply nodup_flatMap_map _ _ (by simp) (List.nodup_finRange _)
  intro a b a' b' h
  cases h
  exact ⟨rfl, rfl⟩

theorem cellList_nodup {P : Params} : (cellList P).Nodup := by
  apply nodup_flatMap_map _ _ (List.nodup_finRange _) legList_nodup
  intro a b a' b' h
  cases h
  exact ⟨rfl, rfl⟩

private theorem g2Sector_h1_nodup {P : Params} (σ : Sector) : ((legList P).flatMap fun l =>
    (List.finRange (P.N + 1)).map (G2Idx.ZeroCoordinate σ l)).Nodup := by
  apply nodup_flatMap_map _ _ legList_nodup (List.nodup_finRange _)
  intro a b a' b' h; cases h; exact ⟨rfl, rfl⟩

private theorem g2Sector_h2_nodup {P : Params} (σ : Sector) : ((legList P).flatMap fun l =>
    (List.finRange (P.N + 1)).map (G2Idx.R2 σ l)).Nodup := by
  apply nodup_flatMap_map _ _ legList_nodup (List.nodup_finRange _)
  intro a b a' b' h; cases h; exact ⟨rfl, rfl⟩

private theorem g2Sector_ht1_nodup {P : Params} (σ : Sector) : ((legList P).map (G2Idx.totR1 σ)).Nodup :=
  legList_nodup.map (by intro x y h; cases h; rfl)

private theorem g2Sector_ht2_nodup {P : Params} (σ : Sector) : ((legList P).map (G2Idx.totR2 σ)).Nodup :=
  legList_nodup.map (by intro x y h; cases h; rfl)

private theorem g2Sector_hq_nodup {P : Params} (σ : Sector) : ((cellList P).flatMap fun c =>
    (List.finRange P.Mq).map (G2Idx.QB σ c)).Nodup := by
  apply nodup_flatMap_map _ _ cellList_nodup (List.nodup_finRange _)
  intro a b a' b' h; cases h; exact ⟨rfl, rfl⟩

private theorem g2Sector_hr_nodup {P : Params} (σ : Sector) : ((cellList P).flatMap fun c =>
    (List.finRange P.Wr).map (G2Idx.RB σ c)).Nodup := by
  apply nodup_flatMap_map _ _ cellList_nodup (List.nodup_finRange _)
  intro a b a' b' h; cases h; exact ⟨rfl, rfl⟩

private theorem g2Sector_hs_nodup {P : Params} (σ : Sector) : ((legList P).map (G2Idx.SC σ)).Nodup :=
  legList_nodup.map (by intro x y h; cases h; rfl)

private theorem g2Sector_hb_nodup {P : Params} (σ : Sector) : ([CrossIdx.c1eps, .c2eps, .c3eps, .c2div, .c3div].flatMap fun g =>
    (List.finRange (2 * P.n - 1)).map (G2Idx.GB σ g)).Nodup := by
  apply nodup_flatMap_map _ _ (by simp) (List.nodup_finRange _)
  intro a b a' b' h; cases h; exact ⟨rfl, rfl⟩

private theorem g2Sector_hm_nodup {P : Params} (σ : Sector) : ([TieIdx.t1, .t2, .t3].flatMap fun t =>
    (List.finRange (P.n - 1)).map (G2Idx.GM σ t)).Nodup := by
  apply nodup_flatMap_map _ _ (by simp) (List.nodup_finRange _)
  intro a b a' b' h; cases h; exact ⟨rfl, rfl⟩

private def g2Tag {P : Params} : G2Idx P → ℕ
  | .ZeroCoordinate _ _ _ => 0
  | .R2 _ _ _ => 1
  | .totR1 _ _ => 2
  | .totR2 _ _ => 3
  | .QB _ _ _ => 4
  | .RB _ _ _ => 5
  | .SC _ _ => 6
  | .GB _ _ _ => 7
  | .GM _ _ _ => 8

private def g2Parts (P : Params) (σ : Sector) : ℕ → List (G2Idx P)
  | 0 => (legList P).flatMap fun l => (List.finRange (P.N + 1)).map (G2Idx.ZeroCoordinate σ l)
  | 1 => (legList P).flatMap fun l => (List.finRange (P.N + 1)).map (G2Idx.R2 σ l)
  | 2 => (legList P).map (G2Idx.totR1 σ)
  | 3 => (legList P).map (G2Idx.totR2 σ)
  | 4 => (cellList P).flatMap fun c => (List.finRange P.Mq).map (G2Idx.QB σ c)
  | 5 => (cellList P).flatMap fun c => (List.finRange P.Wr).map (G2Idx.RB σ c)
  | 6 => (legList P).map (G2Idx.SC σ)
  | 7 => [CrossIdx.c1eps, .c2eps, .c3eps, .c2div, .c3div].flatMap fun g =>
      (List.finRange (2 * P.n - 1)).map (G2Idx.GB σ g)
  | 8 => [TieIdx.t1, .t2, .t3].flatMap fun t =>
      (List.finRange (P.n - 1)).map (G2Idx.GM σ t)
  | _ => []

private theorem g2Parts_nodup {P : Params} (σ : Sector) (k : ℕ) :
    (g2Parts P σ k).Nodup := by
  unfold g2Parts
  split <;> simp only [g2Sector_h1_nodup, g2Sector_h2_nodup, g2Sector_ht1_nodup,
    g2Sector_ht2_nodup, g2Sector_hq_nodup, g2Sector_hr_nodup, g2Sector_hs_nodup,
    g2Sector_hb_nodup, g2Sector_hm_nodup, List.nodup_nil]

private theorem g2Parts_tag {P : Params} (σ : Sector) (k : ℕ) (a : G2Idx P)
    (ha : a ∈ g2Parts P σ k) : g2Tag a = k := by
  unfold g2Parts at ha
  split at ha <;> simp only [List.mem_flatMap, List.mem_map, List.not_mem_nil] at ha
  all_goals first
    | (obtain ⟨i, _, j, _, rfl⟩ := ha; rfl)
    | (obtain ⟨i, _, rfl⟩ := ha; rfl)
    | contradiction

theorem g2OrderSector_nodup {P : Params} (σ : Sector) : (g2OrderSector P σ).Nodup := by
  have he : g2OrderSector P σ = [0, 1, 2, 3, 4, 5, 6, 7, 8].flatMap (g2Parts P σ) := by
    simp only [g2OrderSector, List.flatMap_cons, List.flatMap_nil, g2Parts, List.append_nil, List.append_assoc]
  rw [he]
  apply List.nodup_flatMap.mpr
  refine ⟨fun k _ => g2Parts_nodup σ k, ?_⟩
  have hn : ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List ℕ).Nodup := by decide
  apply hn.imp
  intro a b hab x hx hx'
  exact hab ((g2Parts_tag σ a x hx).symm.trans (g2Parts_tag σ b x hx'))

theorem g2Order_nodup {P : Params} : (g2Order P).Nodup := by
  simp only [g2Order, List.nodup_append, g2OrderSector_nodup, true_and]
  simp [g2OrderSector, List.mem_flatMap, List.disjoint_left]
  aesop

theorem keys2_nodup {P : Params} : (keys2 P).Nodup := by
  have hm := (g2Order_nodup (P := P)).map (Option.some_injective _)
  simpa [keys2] using hm

end Praxis.Proofs.GroupModel
