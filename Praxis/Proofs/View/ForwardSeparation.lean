import Praxis.Proofs.View.ForwardHelpers
import Praxis.Enc
import Praxis.Params
import Praxis.Published
import Praxis.Reduction
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.View

open Praxis.Algebra (Vec Mat dot)

open Polynomial

section PolynomialSeparation

lemma polynomial_list_degree_le {F α : Type*} [Semiring F] (l : List α)
    (f : α → Polynomial F) (d : ℕ) (h : ∀ a ∈ l, (f a).natDegree ≤ d) :
    (l.map f).sum.natDegree ≤ d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (Polynomial.natDegree_add_le _ _).trans
        (max_le (h a (by simp)) (ih (fun a ha => h a (by simp [ha]))))

lemma polynomial_zero_off_zero {F : Type*} [Field F] [Fintype F]
    (p : Polynomial F) (hd : p.natDegree < Fintype.card F - 1)
    (h : ∀ t : F, t ≠ 0 → p.eval t = 0) : p = 0 := by
  let : DecidableEq F := Classical.typeDecidableEq F
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (Finset.univ.erase (0 : F))
  · intro t ht
    exact h t (Finset.ne_of_mem_erase ht)
  · simpa using hd

lemma list_monomial_separation {F α : Type*} [Field F] [Fintype F] (l : List α)
    (e : α → ℕ) (f : α → F) (d : ℕ) (hd : d < Fintype.card F - 1)
    (he : ∀ a ∈ l, e a ≤ d)
    (h : ∀ t : F, t ≠ 0 → (l.map fun a => f a * t ^ e a).sum = 0) (k : ℕ) :
    (l.map fun a => if e a = k then f a else 0).sum = 0 := by
  classical
  let p : Polynomial F := (l.map fun a => monomial (e a) (f a)).sum
  have hp : p = 0 := by
    apply polynomial_zero_off_zero
    · exact (polynomial_list_degree_le l _ d (fun a ha =>
        (natDegree_monomial_le _).trans (he a ha))).trans_lt hd
    · intro t ht
      simpa only [p, eval_listSum, List.map_map, Function.comp_def, eval_monomial] using h t ht
  have hh := congrArg (fun p : Polynomial F => p.coeff k) hp
  simpa only [p, coeff_list_sum_map, coeff_monomial, coeff_zero] using hh

lemma mono_sep {F α : Type*} [Field F] [Fintype F] [DecidableEq α] (s : Finset α)
    (e : α → ℕ) (f : α → F) (he : Set.InjOn e s)
    (hd : ∀ a ∈ s, e a < Fintype.card F - 1)
    (h : ∀ t : F, t ≠ 0 → ∑ a ∈ s, f a * t ^ e a = 0) : ∀ a ∈ s, f a = 0 := by
  classical
  let p : Polynomial F := ∑ a ∈ s, monomial (e a) (f a)
  have hp : p = 0 := by
    apply polynomial_zero_off_zero
    · by_cases hs : s.Nonempty
      · obtain ⟨a, ha, hmax⟩ := s.exists_max_image e hs
        apply (Polynomial.natDegree_sum_le_of_forall_le _ (fun a => monomial (e a) (f a))
          (fun b hb => (natDegree_monomial_le _).trans (hmax b hb))).trans_lt (hd a ha)
      · have hcard : 0 < Fintype.card F - 1 := by
          have hc := Fintype.one_lt_card (α := F)
          omega
        simpa [p, Finset.not_nonempty_iff_eq_empty.mp hs] using hcard
    · intro t ht
      simpa only [p, eval_finsetSum, eval_monomial] using h t ht
  intro a ha
  have hc := congrArg (fun p : Polynomial F => p.coeff (e a)) hp
  have hh : p.coeff (e a) = f a := by
    simp only [p, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      exact if_neg (fun hba' => hba (he hb ha hba'))
    · simp [ha]
  simpa only [hh, coeff_zero] using hc

end PolynomialSeparation

section Scaling

variable {P : Params} [Fact (Nat.Prime P.q)]

def IdentityTo (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (D : ExprT P) (K : Coins P → Fq P) : Prop :=
  ∀ c, ValidCoins pp.qap c → valT pp v ⟨c, r⟩ D = K c

def restrictW (w1 : Option (G1Idx P) → Fin 3) (w2 : Option (G2Idx P) → Fin 3)
    (wT k : ℕ) (D : ExprT P) : ExprT P :=
  (fun ab => if (w1 ab.1).val + (w2 ab.2).val = k then D.1 ab else 0,
    if wT = k then D.2 else 0)

set_option maxHeartbeats 1000000 in
lemma sep_by_scaling (pp : PublicParams P) (v : Fin P.n → Vec (Fq P) P.N)
    (r : Vec (Fq P) P.N) (φ : Fq P → Coins P → Coins P)
    (w1 : Option (G1Idx P) → Fin 3) (w2 : Option (G2Idx P) → Fin 3)
    (wT wK : Fin 5) (K : Coins P → Fq P)
    (hcard : 4 < P.q - 1)
    (hv : ∀ t c, t ≠ 0 → ValidCoins pp.qap c → ValidCoins pp.qap (φ t c))
    (h1 : ∀ t c a, t ≠ 0 → ValidCoins pp.qap c →
      t * e1At pp ⟨φ t c, r⟩ a = t ^ (w1 a).val * e1At pp ⟨c, r⟩ a)
    (h2 : ∀ t c b, t ≠ 0 → ValidCoins pp.qap c →
      t * e2At pp v ⟨φ t c, r⟩ b = t ^ (w2 b).val * e2At pp v ⟨c, r⟩ b)
    (hT : ∀ t c, t ≠ 0 → ValidCoins pp.qap c →
      t ^ 2 * gtExp pp (φ t c) = t ^ wT.val * gtExp pp c)
    (hK : ∀ t c, t ≠ 0 → ValidCoins pp.qap c →
      t ^ 2 * K (φ t c) = t ^ wK.val * K c)
    (D : ExprT P) (h : IdentityTo pp v r D K) (k : ℕ) :
    IdentityTo pp v r (restrictW w1 w2 wT.val k D)
      (fun c => if wK.val = k then K c else 0) := by
  classical
  intro c hc
  let L : List (ℕ × Fq P) :=
    (keys1 P).flatMap (fun a => (keys2 P).map fun b =>
      ((w1 a).val + (w2 b).val, D.1 (a, b) * (e1At pp ⟨c, r⟩ a * e2At pp v ⟨c, r⟩ b))) ++
      [(wT.val, D.2 * gtExp pp c), (wK.val, -K c)]
  have hL : ∀ t : Fq P, t ≠ 0 → (L.map fun a => a.2 * t ^ a.1).sum = 0 := by
    intro t ht
    have hp (a : Option (G1Idx P)) (b : Option (G2Idx P)) :
        (D.1 (a, b) * (e1At pp ⟨c, r⟩ a * e2At pp v ⟨c, r⟩ b)) *
          t ^ ((w1 a).val + (w2 b).val) =
        t ^ 2 * (D.1 (a, b) * (e1At pp ⟨φ t c, r⟩ a * e2At pp v ⟨φ t c, r⟩ b)) := by
      rw [pow_add]
      calc
        _ = D.1 (a,b) * ((t ^ (w1 a).val * e1At pp ⟨c,r⟩ a) *
            (t ^ (w2 b).val * e2At pp v ⟨c,r⟩ b)) := by ring
        _ = _ := by rw [← h1 t c a ht hc, ← h2 t c b ht hc]; ring
    simp only [L, List.map_append, List.sum_append, list_sum_flatMap, List.map_map,
      Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, hp, List.sum_map_mul_left]
    have hgt := hT t c ht hc
    have hk := hK t c ht hc
    have hid := h (φ t c) (hv t c ht hc)
    unfold valT at hid
    linear_combination t ^ 2 * hid - D.2 * hgt + hk
  have hd : ∀ a ∈ L, a.1 ≤ 4 := by
    intro a ha
    simp only [L, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with ⟨a', _, b, _, rfl⟩ | rfl | rfl
    · have hwa := (w1 a').isLt
      have hwb := (w2 b).isLt
      omega
    · exact Nat.le_of_lt_succ wT.isLt
    · exact Nat.le_of_lt_succ wK.isLt
  have hs := list_monomial_separation L Prod.fst Prod.snd 4 (by simpa using hcard) hd hL k
  simp only [L, List.map_append, List.sum_append, list_sum_flatMap, List.map_map,
    Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
  have hh : valT pp v ⟨c, r⟩ (restrictW w1 w2 wT.val k D) =
      ((keys1 P).map fun a => ((keys2 P).map fun b =>
        if (w1 a).val + (w2 b).val = k then
          D.1 (a,b) * (e1At pp ⟨c,r⟩ a * e2At pp v ⟨c,r⟩ b) else 0).sum).sum +
        (if wT.val = k then D.2 * gtExp pp c else 0) := by
    simp only [valT, restrictW, ite_mul, zero_mul]
  rw [hh]
  split_ifs at hs ⊢ <;> linear_combination hs

end Scaling

end Praxis.Proofs.View
