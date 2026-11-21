import Praxis.Search
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Embedding.Basic
import Praxis.Forms
import Praxis.Params

namespace Praxis

variable (P : Params)

abbrev Msg : Type := BitVec P.messageBits

abbrev Label : Type := BitVec P.labelBits

abbrev ClassName : Type := Sym2 (Label P)

abbrev KDF : Type := ClassName P → Msg P

abbrev NameRef : Type := ℕ

inductive KdfQuery
  | ref (k : NameRef)
  | guess (nm : ClassName P)

structure Header where
  seed : Seed P
  cm : Msg P

variable {P}

def labelName (σT : ZMod P.q ↪ Label P) (v : ZMod P.q) : ClassName P :=
  s(σT v, σT (-v))

def maskMsg (kdf : KDF P) (nm : ClassName P) (m : Msg P) : Msg P := m ^^^ kdf nm

end Praxis
