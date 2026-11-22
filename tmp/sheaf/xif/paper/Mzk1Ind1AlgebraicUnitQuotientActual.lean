import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1AlgebraicUnitQuotientActual
open LeanFormal.IUT

universe u
variable {V : Type u} {F F' : LeanFormal.IUT.FPrimeStrip V}

/-- Algebraic unit-quotient action induced by an actual `FPrimeStripEquiv`:
`isoMon` on units, then quotient by torsion.  This is the algebraic layer of
the Ind1 `β_a`; topology/actual completion units are not supplied here. -/
def fPrimeStripUnitQuotientEquiv (a : LeanFormal.IUT.FPrimeStripEquiv F F')
    (v : V) :
    TimesMuQuotient ((F.Mon v)ˣ) ≃* TimesMuQuotient ((F'.Mon v)ˣ) :=
  QuotientGroup.congr (CommGroup.torsion ((F.Mon v)ˣ))
    (CommGroup.torsion ((F'.Mon v)ˣ))
    (Units.mapEquiv (a.isoMon v))
    (Units.mapEquiv (a.isoMon v)).map_torsion

theorem fPrimeStripUnitQuotientEquiv_mk
    (a : LeanFormal.IUT.FPrimeStripEquiv F F') (v : V)
    (u : (F.Mon v)ˣ) :
    fPrimeStripUnitQuotientEquiv a v (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (Units.mapEquiv (a.isoMon v) u) := rfl

#print axioms fPrimeStripUnitQuotientEquiv_mk
end LeanFormal.IUT.XiFPaper.Mzk1Ind1AlgebraicUnitQuotientActual