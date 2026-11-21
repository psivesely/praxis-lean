import Praxis.Proofs.Decryption.FindT
import Praxis.Proofs.DecryptionAlgebra.Lambda
import Praxis.Proofs.Basic
import Praxis.Dec
import Praxis.Domain
import Praxis.Enc
import Praxis.Forms
import Praxis.Grid
import Praxis.Keys
import Praxis.Proofs.DecryptionAlgebra.Psi
import Praxis.Proofs.Decryption.Range
import Praxis.Params
import Praxis.Published
import Praxis.Relation
import Praxis.Scheme
import Praxis.Search
import Praxis.Setting
import Praxis.Algebra.Definitions.Relation

namespace Praxis.Proofs.Decryption

open Praxis.Algebra (Vec)

set_option maxHeartbeats 10000 in
private theorem finish {P : Params} [Fact (Nat.Prime P.q)]
    (name : (expGroups P.q).GT → ClassName P) (kdf : KDF P) (m : Msg P)
    (a w k ψ : Fq P) (r cx t : ℤ) (ha : a ≠ 0) (hw : w ≠ 0)
    (hs : ψ ≠ 0 → findT (P := P) (a * (w * k + (r : Fq P) * ψ) -
      w * (a * k) - (cx : Fq P) * (a * ψ)) (a * ψ) = some t)
    (hk : w⁻¹ * (w * k + (r : Fq P) * ψ - ((cx + t : ℤ) : Fq P) * ψ) = k) :
    (match (if (a * ψ : (expGroups P.q).GT) ≠ 0 then
      findT (P := P) (a * (w * k + (r : Fq P) * ψ) - w • (a * k) -
        (cx : Fq P) • (a * ψ)) (a * ψ)
    else if (a * (w * k + (r : Fq P) * ψ) - w • (a * k) -
        (cx : Fq P) • (a * ψ) : (expGroups P.q).GT) = 0 then some 0 else none) with
    | none => none
    | some s => some (maskMsg kdf (name (w⁻¹ • (w * k + (r : Fq P) * ψ -
        ((cx + s : ℤ) : Fq P) • ψ))) (maskMsg kdf (name k) m))) = some m := by
  change (match (if a * ψ ≠ 0 then
      findT (P := P) (a * (w * k + (r : Fq P) * ψ) - w * (a * k) -
        (cx : Fq P) * (a * ψ)) (a * ψ)
    else if a * (w * k + (r : Fq P) * ψ) - w * (a * k) -
        (cx : Fq P) * (a * ψ) = 0 then some 0 else none) with
    | none => none
    | some s => some (maskMsg kdf (name (w⁻¹ * (w * k + (r : Fq P) * ψ -
        ((cx + s : ℤ) : Fq P) * ψ))) (maskMsg kdf (name k) m))) = some m
  by_cases hψ : ψ = 0
  · subst ψ
    simp only [mul_zero, add_zero, sub_zero, ne_eq, not_true_eq_false, if_false]
    have hz : a * (w * k) - w * (a * k) = 0 := by ring
    rw [hz]
    simp [hw, maskMsg, BitVec.xor_assoc]
  · rw [if_pos (mul_ne_zero ha hψ), hs hψ]
    simp only
    rw [hk]
    simp [maskMsg, BitVec.xor_assoc]

set_option maxRecDepth 4096 in
private theorem assemble {P : Params} [Fact (Nat.Prime P.q)]
    (pp : PublicParams P) (HF : FormOracle P) (kdf : KDF P)
    (name : (expGroups P.q).GT → ClassName P) (m : Msg P) (seed : Seed P) (c : Coins P)
    (x : Vec (Fq P) P.N) (ψ : Fq P) (r cx t : ℤ)
    (ha : coin c .alpha ≠ 0) (hw : wKey (formsOf HF seed) x ≠ 0)
    (hl0 : evalComb (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c) .plain
      (lambdaCoeffs pp (formsOf HF seed) x) = wKey (formsOf HF seed) x * kappa pp c + (r : Fq P) * ψ)
    (hl1 : evalComb (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c) .alpha
      (lambdaCoeffs pp (formsOf HF seed) x) = coin c .alpha *
        (wKey (formsOf HF seed) x * kappa pp c + (r : Fq P) * ψ))
    (hp0 : psi (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c)
      (formsOf HF seed) x .plain = ψ)
    (hp1 : psi (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c)
      (formsOf HF seed) x .alpha = coin c .alpha * ψ)
    (hcx : cx = cX (toInt x))
    (hs : ψ ≠ 0 → findT (P := P) (coin c .alpha *
      (wKey (formsOf HF seed) x * kappa pp c + (r : Fq P) * ψ) -
      wKey (formsOf HF seed) x * (coin c .alpha * kappa pp c) -
      (cx : Fq P) * (coin c .alpha * ψ)) (coin c .alpha * ψ) = some t)
    (hk : (wKey (formsOf HF seed) x)⁻¹ *
      (wKey (formsOf HF seed) x * kappa pp c + (r : Fq P) * ψ -
        ((cx + t : ℤ) : Fq P) * ψ) = kappa pp c) :
    decRef (expGroups P.q) HF kdf name pp
      (encrypt (expGroups P.q) HF kdf name pp m seed c) x = some m := by
  have henc (z : Fq P) : (expGroups P.q).encT z = z := by
    change z * (1 * 1) = z
    simp
  have hseed : (encrypt (expGroups P.q) HF kdf name pp m seed c).header.seed = seed := rfl
  have hgt : (encrypt (expGroups P.q) HF kdf name pp m seed c).gT =
      (expGroups P.q).encT (gtExp pp c) := rfl
  have hcm : (encrypt (expGroups P.q) HF kdf name pp m seed c).header.cm =
      maskMsg kdf (name ((expGroups P.q).encT (kappa pp c))) m := rfl
  unfold decRef
  simp only [hseed, hw, ↓reduceIte, hl0, hl1, hp0, hp1, hgt, hcm]
  simp only [hseed, hp1, henc, gtExp]
  rw [show psi (expGroups P.q) (encrypt (expGroups P.q) HF kdf name pp m seed c)
      (formsOf HF (encrypt (expGroups P.q) HF kdf name pp m seed c).header.seed)
      x .alpha = coin c .alpha * ψ from hp1]
  subst cx
  exact finish (P := P) name kdf m (coin c .alpha) (wKey (formsOf HF seed) x)
    (kappa pp c) ψ r (cX (toInt x)) t ha hw hs hk

set_option maxRecDepth 4096 in

theorem decref_correct (ch : AdmissibleChoice P0) (S : Relation P0) (hS : InShape P0 S)
    (HF : FormOracle P0) (kdf : KDF P0) (m : Msg P0) (seed : Seed P0) (c : Coins P0)
    (hc : ValidCoins (ppOf ch S).qap c) (x : Vec (Fq P0) P0.N) (hx : IsWitness S x)
    (hw : wKey (formsOf HF seed) x ≠ 0) :
    decRef (expGroups P0.q) HF kdf canonName (ppOf ch S)
      (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) x = some m := by
  have hr := decref_range x hx.1 hx.2.1 c.2.1
  have hl := DecryptionAlgebra.decryption_lambda ch S hS HF kdf m seed c hc x hx hw
  have hp := DecryptionAlgebra.decryption_psi (ppOf ch S) HF kdf m seed c x
  let ψ : Fq P0 := ∑ cl : Cell P0, weight (formsOf HF seed) x cl * gamma c cl * ∑ i, x i * c.1 i
  let r : ℤ := rOf (toInt x) (rInt c.2.1)
  let cx : ℤ := cX (toInt x)
  let t : ℤ := r - cx
  have ht : |t| ≤ (P0.tBound : ℤ) := hr.1
  have ha : coin c .alpha ≠ 0 := hc.2.1 .alpha rfl
  have henc (z : Fq P0) : (expGroups P0.q).encT z = z := by
    change z * (1 * 1) = z
    simp
  have hl0 : evalComb (expGroups P0.q)
      (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .plain
      (lambdaCoeffs (ppOf ch S) (formsOf HF seed) x) =
      wKey (formsOf HF seed) x * kappa (ppOf ch S) c + (r : Fq P0) * ψ := by
    simpa only [henc, hr.2] using hl.1
  have hl1 : evalComb (expGroups P0.q)
      (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c) .alpha
      (lambdaCoeffs (ppOf ch S) (formsOf HF seed) x) =
      coin c .alpha * (wKey (formsOf HF seed) x * kappa (ppOf ch S) c + (r : Fq P0) * ψ) := by
    simpa only [henc, hr.2] using hl.2
  have hp0 : psi (expGroups P0.q)
      (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c)
      (formsOf HF seed) x .plain = ψ := by
    simpa only [henc] using hp.1
  have hp1 : psi (expGroups P0.q)
      (encrypt (expGroups P0.q) HF kdf canonName (ppOf ch S) m seed c)
      (formsOf HF seed) x .alpha = coin c .alpha * ψ := by
    simpa only [henc] using hp.2
  have hsearch (hψ : ψ ≠ 0) :
      findT (P := P0)
        (coin c .alpha * (wKey (formsOf HF seed) x * kappa (ppOf ch S) c + (r : Fq P0) * ψ) -
          wKey (formsOf HF seed) x * (coin c .alpha * kappa (ppOf ch S) c) -
          (cx : Fq P0) * (coin c .alpha * ψ)) (coin c .alpha * ψ) = some t := by
    apply findT_spec _ _ (mul_ne_zero ha hψ) t ht
    change _ = (t : Fq P0) * (coin c .alpha * ψ)
    dsimp [t]
    push_cast
    ring
  have hkey : (wKey (formsOf HF seed) x)⁻¹ *
      (wKey (formsOf HF seed) x * kappa (ppOf ch S) c + (r : Fq P0) * ψ -
        ((cx + t : ℤ) : Fq P0) * ψ) = kappa (ppOf ch S) c := by
    dsimp [t]
    push_cast
    field_simp
    <;> ring
  exact assemble (P := P0) (ppOf ch S) HF kdf canonName m seed c x ψ r cx t ha hw
    hl0 hl1 hp0 hp1 rfl hsearch hkey

end Praxis.Proofs.Decryption
