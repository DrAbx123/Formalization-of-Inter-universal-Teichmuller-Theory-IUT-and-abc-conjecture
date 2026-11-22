import tmp.sheaf.takkun.IutLean.HodgeTheater.Defs
import tmp.sheaf.takkun.IutLean.HodgeTheater.PrimeStripData
import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem

/-!
# Thm 3.11 Hodge theater / prime-strip reference projections (green Takkun layer)

Reuses the green Takkun modules `HodgeTheater/Defs`, `HodgeTheater/PrimeStripData`
and `Frobenioid/PrimeStripSystem`: a `Full` (Theta-ellNF) theater carries the
`PrimeStripSystem` (additive/multiplicative labeled strips + Gaussian theta
values + glue + nondegeneracy).  This file exposes those fields and the proved
theta sign symmetry / Kummer cyclotomic character as reference objects for
Theorem 3.11 (multiradial input data).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripSystemGlueActual

open LeanFormal.IUT

noncomputable section

/-- The `PrimeStripSystem` carried by the additive (D-Theta-ell) half of a
`Full` theater. -/
def thm311SystemOfFull (F : _root_.IUT.HodgeTheater.Full) :
    _root_.IUT.HodgeTheater.PrimeStripSystem F.l :=
  F.add.primeStrips

@[simp] theorem thm311SystemOfFull_V (F : _root_.IUT.HodgeTheater.Full) :
    (thm311SystemOfFull F).V = F.add.primeStrips.V := rfl

@[simp] theorem thm311SystemOfFull_addSystem (F : _root_.IUT.HodgeTheater.Full) :
    (thm311SystemOfFull F).addSystem = F.add.primeStrips.addSystem := rfl

@[simp] theorem thm311SystemOfFull_mulSystem (F : _root_.IUT.HodgeTheater.Full) :
    (thm311SystemOfFull F).mulSystem = F.add.primeStrips.mulSystem := rfl

@[simp] theorem thm311SystemOfFull_glue (F : _root_.IUT.HodgeTheater.Full) :
    (thm311SystemOfFull F).glue = F.add.primeStrips.glue := rfl

/-- Gaussian theta values `q_v^{j^2}` carried by a `Full` theater. -/
def thm311ThetaValue (F : _root_.IUT.HodgeTheater.Full)
    (v : F.add.primeStrips.V) (j : Int) :=
  F.add.primeStrips.gaussian.thetaValueAt v j

/-- `sign` symmetry of the Gaussian theta values (proved in Takkun
`PrimeStripSystem.theta_symmetric`). -/
theorem thm311ThetaValue_neg (F : _root_.IUT.HodgeTheater.Full)
    (v : F.add.primeStrips.V) (j : Int) :
    thm311ThetaValue F v (-j) = thm311ThetaValue F v j :=
  _root_.IUT.HodgeTheater.PrimeStripSystem.theta_symmetric F.add.primeStrips v j

/-- Kummer cyclotomic character attached to the Gaussian strip (proved
consequence of the Gaussian strip structure). -/
def thm311Kummer (F : _root_.IUT.HodgeTheater.Full)
    (v : F.add.primeStrips.V) :
    F.add.primeStrips.gaussian.G v →*
      MulAut (_root_.IUT.Cyclotome.FrobeniusCyclotome
        (F.add.primeStrips.gaussian.Mon v)) :=
  _root_.IUT.HodgeTheater.PrimeStripSystem.kummer F.add.primeStrips v

/-- Common `l` of the additive/multiplicative halves (Takkun `Full.glue`). -/
theorem thm311Full_add_mul_l (F : _root_.IUT.HodgeTheater.Full) :
    F.add.l = F.mul.l := F.glue

@[simp] theorem thm311Full_l (F : _root_.IUT.HodgeTheater.Full) :
    F.l = F.add.l := rfl

end

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripSystemGlueActual
