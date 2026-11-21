import Praxis.Proofs.NamesGame
import Praxis.Proofs.NamesMonitor
import Praxis.Games
import Praxis.Keys
import Praxis.Proofs.NamesReservoir
import Praxis.Params
import Praxis.Setting
import Praxis.Algebra.Label.Injections
import Praxis.Algebra.Definitions.Games
import Praxis.Encryption.GroupModel

namespace Praxis.Proofs.Names.Reservoir

open OracleComp OracleSpec

variable {α β γ η : Type}

theorem run_bind [DecidableEq α] (left right : α) (σ : α ↪ β)
    (oa : OracleComp (Definitions α β) γ) (k : γ → OracleComp (Definitions α β) η) (p : Phase) :
    run left right σ (oa >>= k) p =
      (run left right σ oa p >>= fun z => run left right σ (k z.1) z.2) := by
  simp [run, simulateQ_bind, StateT.run_bind]

theorem run_map [DecidableEq α] (left right : α) (σ : α ↪ β)
    (oa : OracleComp (Definitions α β) γ) (f : γ → η) (p : Phase) :
    run left right σ (f <$> oa) p =
      (fun z => (f z.1, z.2)) <$> run left right σ oa p := by
  simp [run, simulateQ_map, StateT.run_map]

@[simp] theorem advance_success [DecidableEq α] (left right : α)
    (q : Query α β) (o : q.Answer) : advance left right .success q o = .success := rfl

theorem advance_decode_dead_iff [DecidableEq α] (left right : α) (p : Phase)
    (t : β) (o : Option α) : advance left right p (.decode t) o = .dead ↔ p = .dead := by
  cases p <;> simp [advance] <;> split_ifs <;> simp

theorem advance_encode_dead_imp [DecidableEq α] (left right x : α) (p : Phase) (o : β)
    (h : advance left right p (.encode x) o = .dead) :
    p = .dead ∨ x = left ∨ x = right := by
  cases p <;> simp_all [advance] <;> tauto

theorem decode_pair_success [DecidableEq α] (left right : α) (hne : left ≠ right)
    (p : Phase) (hp : p ≠ .dead) (a b : β) :
    advance left right (advance left right p (.decode a) (some left))
      (.decode b) (some right) = .success := by
  cases p <;> simp_all [advance, hne.symm]

theorem decode_pair_success_rev [DecidableEq α] (left right : α) (hne : left ≠ right)
    (p : Phase) (hp : p ≠ .dead) (a b : β) :
    advance left right (advance left right p (.decode a) (some right))
      (.decode b) (some left) = .success := by
  cases p <;> simp_all [advance, hne.symm]

end Praxis.Proofs.Names.Reservoir

namespace Praxis.Proofs.Names.Game

open OracleComp OracleSpec

variable {P : Params}

theorem liftCoins_tracked (left right : Fq P) (σ : Fq P ↪ Label P)
    {α : Type} (oa : ProbComp α) (p : Reservoir.Phase) :
    Reservoir.run left right σ (liftCoins oa) p = (fun a => (a, p)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    change Reservoir.run left right σ
      ((liftM ((ObsModel P).query (.inl n)) : ObsComp P _) >>= fun u => liftCoins (k u)) p = _
    rw [Reservoir.run_coin]
    simp only [ih, map_bind]
    rfl

theorem liftGame_tracked (left right : Fq P) (σ : Fq P ↪ Label P)
    {α : Type} (oa : GameM P α) (st : OracleState P) (p : Reservoir.Phase) :
    Reservoir.run left right σ ((liftGame oa).run st) p =
      (fun a => (a, p)) <$> oa.run st := liftCoins_tracked left right σ _ p

theorem encodeGT_tracked (left right : Fq P) (σ : Fq P ↪ Label P)
    (x : Fq P) (st : OracleState P) (p : Reservoir.Phase) :
    Reservoir.run left right σ ((encodeGT x).run st) p =
      pure ((σ x, st), Reservoir.advance left right p (.encode x) (σ x)) := by
  simp [encodeGT, StateT.run_lift, Reservoir.run_map, Reservoir.run,
    Reservoir.impl, simulateQ_query, Reservoir.observe]

theorem decodeGT_tracked (left right : Fq P) (σ : Fq P ↪ Label P)
    (t : Label P) (st : OracleState P) (p : Reservoir.Phase) :
    Reservoir.run left right σ ((decodeGT t).run st) p =
      pure ((Algebra.decodeLabel σ t, st), Reservoir.advance left right p (.decode t)
        (Algebra.decodeLabel σ t)) := by
  simp [decodeGT, StateT.run_lift, Reservoir.run_map, Reservoir.run,
    Reservoir.impl, simulateQ_query, Reservoir.observe, decode_eq]

noncomputable def answerPhase (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (issued : Finset (Label P)) (qr : GQuery P) (p : Reservoir.Phase) :
    Reservoir.Phase :=
  match qr with
  | .lin .g₁ .. | .lin .g₂ .. => p
  | .lin .gₜ a b u v =>
    let x := Algebra.decodeLabel σ u
    let y := Algebra.decodeLabel σ v
    let p' := Reservoir.advance κ (-κ) p (.decode u) x
    let p'' := Reservoir.advance κ (-κ) p' (.decode v) y
    match x, y with
    | some x, some y => Reservoir.advance κ (-κ) p'' (.encode (a*x+b*y)) (σ (a*x+b*y))
    | _, _ => p''
  | .pair u v =>
    match Algebra.decodeLabel (src .g₁) u, Algebra.decodeLabel (src .g₂) v with
    | some x, some y => Reservoir.advance κ (-κ) p (.encode (x*y)) (σ (x*y))
    | _, _ => p
  | .name v =>
    if v ∈ issued then
      let x := Algebra.decodeLabel σ v
      let p' := Reservoir.advance κ (-κ) p (.decode v) x
      match x with
      | none => p'
      | some x => Reservoir.advance κ (-κ) p' (.encode (-x)) (σ (-x))
    else p

theorem answer_tracked (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (issued : Finset (Label P)) (qr : GQuery P) (st : OracleState P)
    (p : Reservoir.Phase) :
    Reservoir.run κ (-κ) σ ((answer src issued qr).run st) p =
      pure ((groupAnswer (withGT src σ) issued qr, st), answerPhase src σ κ issued qr p) := by
  classical
  cases qr with
  | lin s a b u v =>
    cases s
    · simp [answer, answerPhase, groupAnswer, withGT]
    · simp [answer, answerPhase, groupAnswer, withGT]
    · cases hx : Algebra.decodeLabel σ u <;> cases hy : Algebra.decodeLabel σ v <;>
        simp [answer, answerPhase, StateT.run_bind, StateT.run_map, Reservoir.run_bind,
          Reservoir.run_map, decodeGT_tracked, encodeGT_tracked, groupAnswer, withGT, hx, hy]
  | pair u v =>
    cases hx : Algebra.decodeLabel (src .g₁) u <;> cases hy : Algebra.decodeLabel (src .g₂) v <;>
      simp [answer, answerPhase, StateT.run_map, Reservoir.run_map,
        encodeGT_tracked, groupAnswer, withGT, hx, hy]
  | name v =>
    by_cases hv : v ∈ issued
    · cases hx : Algebra.decodeLabel σ v with
      | none =>
        simp [answer, answerPhase, hv, StateT.run_bind, Reservoir.run_bind,
          decodeGT_tracked, groupAnswer, withGT, hx]
      | some x =>
        have he := (Algebra.Label.RefCoupling.decodeLabel_eq_some_iff σ v x).mp hx
        simp [answer, answerPhase, hv, StateT.run_bind, Reservoir.run_bind, Reservoir.run_map,
          decodeGT_tracked, encodeGT_tracked, groupAnswer, withGT, hx, labelName, he]
    · simp [answer, answerPhase, hv, groupAnswer]

theorem answerPhase_success (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (issued : Finset (Label P)) (qr : GQuery P) :
    answerPhase src σ κ issued qr .success = .success := by
  cases qr with
  | lin s a b u v =>
    cases s <;> simp only [answerPhase]
    split <;> simp
  | pair u v => simp only [answerPhase]; split <;> simp
  | name v => simp only [answerPhase]; split <;> simp; split <;> simp

def issuedAfter (issued : Finset (Label P)) (qr : GQuery P) (r : qr.Result) :
    Finset (Label P) :=
  match trEntry qr r with
  | none => issued
  | some e => match e.issuedGT with
    | none => issued
    | some l => insert l issued

theorem answerPhase_dead (src : LabelEncoding P) (σ : Fq P ↪ Label P)
    (κ : Fq P) (issued : Finset (Label P)) (qr : GQuery P) (p : Reservoir.Phase)
    (h : answerPhase src σ κ issued qr p = .dead) :
    p = .dead ∨ σ κ ∈ issuedAfter issued qr (groupAnswer (withGT src σ) issued qr) ∨
      σ (-κ) ∈ issuedAfter issued qr (groupAnswer (withGT src σ) issued qr) := by
  classical
  cases qr with
  | lin s a b u v =>
    cases s
    · exact Or.inl h
    · exact Or.inl h
    · cases hx : Algebra.decodeLabel σ u <;> cases hy : Algebra.decodeLabel σ v
      all_goals simp only [answerPhase, hx, hy] at h
      all_goals try exact Or.inl ((Reservoir.advance_decode_dead_iff ..).mp
        ((Reservoir.advance_decode_dead_iff ..).mp h))
      rcases Reservoir.advance_encode_dead_imp _ _ _ _ _ h with hd | hl | hr
      · exact Or.inl ((Reservoir.advance_decode_dead_iff ..).mp
          ((Reservoir.advance_decode_dead_iff ..).mp hd))
      · exact Or.inr (Or.inl (by simp [issuedAfter, groupAnswer, withGT, hx, hy, hl, trEntry,
          TrOp.issuedGT]))
      · exact Or.inr (Or.inr (by simp [issuedAfter, groupAnswer, withGT, hx, hy, hr, trEntry,
          TrOp.issuedGT]))
  | pair u v =>
    cases hx : Algebra.decodeLabel (src .g₁) u <;> cases hy : Algebra.decodeLabel (src .g₂) v
    all_goals simp only [answerPhase, hx, hy] at h
    all_goals try exact Or.inl h
    rcases Reservoir.advance_encode_dead_imp _ _ _ _ _ h with hd | hl | hr
    · exact Or.inl hd
    · exact Or.inr (Or.inl (by simp [issuedAfter, groupAnswer, withGT, hx, hy, hl, trEntry,
        TrOp.issuedGT]))
    · exact Or.inr (Or.inr (by simp [issuedAfter, groupAnswer, withGT, hx, hy, hr, trEntry,
        TrOp.issuedGT]))
  | name v =>
    by_cases hv : v ∈ issued
    · cases hx : Algebra.decodeLabel σ v with
      | none =>
        exact Or.inl ((Reservoir.advance_decode_dead_iff ..).mp
          (by simpa [answerPhase, hv, hx] using h))
      | some x =>
        have he := (Algebra.Label.RefCoupling.decodeLabel_eq_some_iff σ v x).mp hx
        have hh : Reservoir.advance κ (-κ)
            (Reservoir.advance κ (-κ) p (.decode v) (some x)) (.encode (-x)) (σ (-x)) = .dead :=
          by simpa [answerPhase, hv, hx] using h
        rcases Reservoir.advance_encode_dead_imp _ _ _ _ _ hh with hd | hl | hr
        · exact Or.inl ((Reservoir.advance_decode_dead_iff ..).mp hd)
        · have hxk : x = -κ := by simpa using congrArg Neg.neg hl
          exact Or.inr (Or.inr (by simpa [issuedAfter, groupAnswer, hv, withGT, hx, trEntry,
            TrOp.issuedGT, ← hxk, he] using hv))
        · have hxk : x = κ := by simpa using congrArg Neg.neg hr
          exact Or.inr (Or.inl (by simpa [issuedAfter, groupAnswer, hv, withGT, hx, trEntry,
            TrOp.issuedGT, ← hxk, he] using hv))
    · exact Or.inl (by simpa [answerPhase, hv] using h)

end Praxis.Proofs.Names.Game
