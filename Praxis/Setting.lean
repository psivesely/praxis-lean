import Praxis.Params
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Field.ZMod

namespace Praxis

abbrev Fq (P : Params) : Type := ZMod P.q

structure BilinearGroups (q : ℕ) where
  G1 : Type
  G2 : Type
  GT : Type
  [addG1 : AddCommGroup G1]
  [addG2 : AddCommGroup G2]
  [addGT : AddCommGroup GT]
  [modG1 : Module (ZMod q) G1]
  [modG2 : Module (ZMod q) G2]
  [modGT : Module (ZMod q) GT]
  [decGT : DecidableEq GT]
  gen1 : G1
  gen2 : G2

  pair : G1 →ₗ[ZMod q] G2 →ₗ[ZMod q] GT

attribute [instance] BilinearGroups.addG1 BilinearGroups.addG2 BilinearGroups.addGT
  BilinearGroups.modG1 BilinearGroups.modG2 BilinearGroups.modGT BilinearGroups.decGT

namespace BilinearGroups

variable {q : ℕ} (B : BilinearGroups q)

def genT : B.GT := B.pair B.gen1 B.gen2

def enc1 (v : ZMod q) : B.G1 := v • B.gen1

def enc2 (v : ZMod q) : B.G2 := v • B.gen2

def encT (v : ZMod q) : B.GT := v • B.genT

end BilinearGroups

def expGroups (q : ℕ) : BilinearGroups q where
  G1 := ZMod q
  G2 := ZMod q
  GT := ZMod q
  gen1 := 1
  gen2 := 1
  pair := LinearMap.mul (ZMod q) (ZMod q)

end Praxis
