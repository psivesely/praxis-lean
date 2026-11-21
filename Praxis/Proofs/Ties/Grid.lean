import Praxis.Proofs.Basic
import Praxis.Grid
import Praxis.Params

namespace Praxis.Proofs.Ties

private lemma cellExp_lt (c : Cell P0) : cellExp c < P0.n := by
  rcases c with ⟨i, X, j⟩
  have hi : i.val < 192 := i.isLt
  have hj : j.val < 12 := j.isLt
  change 2 * i.val + (X.base + 384 * j.val) < 4608
  cases X <;> simp only [LegKind.base] <;> omega

private lemma exp_digits_unique (i i' : Fin P0.K1) (j j' : Fin P0.K2)
    (e e' : ℕ) (he : e ≤ 1) (he' : e' ≤ 1)
    (h : 2 * i.val + (e + 384 * j.val) = 2 * i'.val + (e' + 384 * j'.val)) :
    i = i' ∧ e = e' ∧ j = j' := by
  have hi : i.val < 192 := i.isLt
  have hi' : i'.val < 192 := i'.isLt
  have heq : e = e' := by omega
  have hieq : i.val = i'.val := by omega
  have hjeq : j.val = j'.val := by omega
  exact ⟨Fin.ext hieq, heq, Fin.ext hjeq⟩

private lemma cellExp_digits {c d : Cell P0} (h : cellExp c = cellExp d) :
    c.1 = d.1 ∧ c.2.1.base = d.2.1.base ∧ c.2.2 = d.2.2 := by
  exact exp_digits_unique c.1 d.1 c.2.2 d.2.2 c.2.1.base d.2.1.base
    (by cases c.2.1 <;> decide) (by cases d.2.1 <;> decide) h

theorem uCell_exp_bijOn :
    Set.BijOn (fun c : Cell P0 => cellExp c) {c | IsUCell c} {k | k < P0.n} := by
  refine ⟨fun c _ => cellExp_lt c, ?_, ?_⟩
  · intro c hc d hd h
    obtain ⟨hi, hbase, hj⟩ := cellExp_digits h
    have hkind : c.2.1 = d.2.1 := by
      change c.2.1 ≠ .V at hc
      change d.2.1 ≠ .V at hd
      cases hX : c.2.1 <;> cases hY : d.2.1 <;>
        simp_all [LegKind.base]
    exact Prod.ext hi (Prod.ext hkind hj)
  · intro k hk
    change k < 4608 at hk
    have hi : k / 2 % 192 < P0.K1 := Nat.mod_lt _ (by decide)
    have hj : k / 384 < P0.K2 := by change k / 384 < 12; omega
    by_cases he : k % 2 = 0
    · refine ⟨(⟨k / 2 % 192, hi⟩, .E, ⟨k / 384, hj⟩), ?_, ?_⟩
      · simp [IsUCell]
      · change 2 * (k / 2 % 192) + (0 + 384 * (k / 384)) = k
        omega
    · refine ⟨(⟨k / 2 % 192, hi⟩, .O, ⟨k / 384, hj⟩), ?_, ?_⟩
      · simp [IsUCell]
      · change 2 * (k / 2 % 192) + (1 + 384 * (k / 384)) = k
        omega

theorem vCell_exp_bijOn :
    Set.BijOn (fun c : Cell P0 => cellExp c) {c | ¬ IsUCell c} {k | k < P0.n ∧ Even k} := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    refine ⟨cellExp_lt c, ?_⟩
    have hkind : c.2.1 = .V := by simpa [IsUCell] using hc
    refine ⟨c.1.val + 192 * c.2.2.val, ?_⟩
    change 2 * c.1.val + (c.2.1.base + 384 * c.2.2.val) = _
    rw [hkind]
    simp only [LegKind.base]
    omega
  · intro c hc d hd h
    obtain ⟨hi, _, hj⟩ := cellExp_digits h
    have hX : c.2.1 = .V := by simpa [IsUCell] using hc
    have hY : d.2.1 = .V := by simpa [IsUCell] using hd
    exact Prod.ext hi (Prod.ext (hX.trans hY.symm) hj)
  · intro k hk
    rcases hk with ⟨hk, he⟩
    change k < 4608 at hk
    have hi : k / 2 % 192 < P0.K1 := Nat.mod_lt _ (by decide)
    have hj : k / 384 < P0.K2 := by change k / 384 < 12; omega
    refine ⟨(⟨k / 2 % 192, hi⟩, .V, ⟨k / 384, hj⟩), ?_, ?_⟩
    · simp [IsUCell]
    · rcases he with ⟨a, ha⟩
      change 2 * (k / 2 % 192) + (0 + 384 * (k / 384)) = k
      omega

end Praxis.Proofs.Ties
