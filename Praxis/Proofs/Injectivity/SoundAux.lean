import Praxis.Proofs.Injectivity.Deterministic
import Praxis.Extractor
import Praxis.Keys
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Injectivity

open OracleComp OracleSpec

variable {P : Params} [Fact (Nat.Prime P.q)]

theorem testSketches_sound (S : Relation P) (F : Fin 3 → Algebra.Vec (Fq P) P.N)
    (x : Algebra.Vec (Fq P) P.N) (h : testSketches S F = some x) : IsWitness S x := by
  have hp : decide (Algebra.Sat S x) = true :=
    List.find?_some (p := fun v => decide (Algebra.Sat S v)) h
  exact of_decide_eq_true hp

theorem testExpr_sound (S : Relation P) (F : Fin 3 → Sector → Algebra.Vec (Fq P) P.N)
    (x : Algebra.Vec (Fq P) P.N) (h : testExpr S F = some x) : IsWitness S x := by
  unfold testExpr at h
  cases hp : testSketches S (fun l => F l .plain) with
  | none =>
    simp only [hp, Option.orElse_none] at h
    exact testSketches_sound S _ x h
  | some y =>
    simp only [hp, Option.orElse_some, Option.some.injEq] at h
    subst y
    exact testSketches_sound S _ x hp

theorem gtStep_sound (S : Relation P) (st : ExState P)
    (F : Fin 3 → Sector → Algebra.Vec (Fq P) P.N) (l : Label P)
    (x : Algebra.Vec (Fq P) P.N) (h : (gtStep S st F l).found = some x) : IsWitness S x := by
  unfold gtStep at h
  dsimp only at h
  cases hp : testExpr S F with
  | some y =>
    simp only [hp, Option.orElse_some, Option.some.injEq] at h
    subst y
    exact testExpr_sound S F x hp
  | none =>
    cases he : st.dT l with
    | none => simp [hp, he] at h
    | some E =>
      simp only [hp, Option.orElse_none, he] at h
      exact testExpr_sound S (F - E) x h

def Verified (S : Relation P) (st : ExState P) : Prop :=
  ∀ x, st.found = some x → IsWitness S x

theorem exStep_sound (S : Relation P) (st : ExState P) (op : TrOp P)
    (h : Verified S st) : Verified S (exStep S st op) := by
  intro x hx
  cases hf : st.found with
  | some y => simp only [exStep, hf] at hx; exact h x (hf.trans hx)
  | none =>
    cases op with
    | lin sort a b u v l =>
      cases sort with
      | g₁ => simp [exStep, hf] at hx
      | g₂ => simp [exStep, hf] at hx
      | gₜ => exact gtStep_sound S st _ l x (by simpa only [exStep, hf] using hx)
    | pair u v l => exact gtStep_sound S st _ l x (by simpa only [exStep, hf] using hx)
    | name v l =>
      cases hn : st.named v with
      | true => simp [exStep, hf, hn] at hx
      | false => exact gtStep_sound S _ _ _ x (by simpa only [exStep, hf, hn, Bool.false_eq_true, ↓reduceIte] using hx)

theorem transcript_sound (S : Relation P) (tr : List (TrOp P)) (st : ExState P)
    (h : Verified S st) : Verified S (tr.foldl (exStep S) st) := by
  induction tr generalizing st with
  | nil => exact h
  | cons op ops ih => exact ih _ (exStep_sound S st op h)

theorem extractWith_sound (S : Relation P) (pub : PubView P) (tr : List (TrOp P))
    (sk : Sketches P) (x : Algebra.Vec (Fq P) P.N) (h : extractWith S pub tr sk = some x) :
    IsWitness S x :=
  transcript_sound S tr (initState pub sk) (by intro x hx; simp [initState] at hx) x h

end Praxis.Proofs.Injectivity
