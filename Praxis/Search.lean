import Praxis.QAP
import Praxis.Algebra.Definitions.Sampler
import Praxis.Grid
import Praxis.Params
import Praxis.Setting
import Praxis.Stack
import Praxis.Algebra.Definitions.Relation

namespace Praxis

open Praxis.Algebra (Vec Mat GridSample centerA centeredZ centeredF maxAtom)

variable (P : Params)

def widths : Fin P.N → ℕ := fun _ => P.g

abbrev SearchSample : Type := GridSample P.g (widths P)

variable {P}

def rInt (w : SearchSample P) : Vec ℤ P.N := centeredZ (widths P) w

def rField (w : SearchSample P) : Vec (Fq P) P.N := centeredF (p := P.q) w

def toInt (x : Vec (Fq P) P.N) : Vec ℤ P.N := fun i => ((x i).val : ℤ)

def rOf (x r : Vec ℤ P.N) : ℤ := ∑ i, x i * r i

def muX (x : Vec ℤ P.N) : ℚ :=
  (centerA (widths P) : ℚ) + (((P.g : ℚ) + 1) / 2 + 1) +
    ∑ i : Fin P.N, ((x i.succ : ℚ) - 1 / 2) * (((P.g : ℚ) + 1) / 2 + 1)

def cX (x : Vec ℤ P.N) : ℤ := ⌊muX x⌋

noncomputable def gp (W : Stack P) : ℝ :=
  maxAtom (fun w : SearchSample P => fun c : Cell P => (W c).mulVec (rField w))

def Light (W : Stack P) : Prop := gp W ≤ (P.theta : ℝ)

def Heavy (W : Stack P) : Prop := ¬ Light W

end Praxis
