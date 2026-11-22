import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Hodge theater / F-prime-strip object for Theorem 3.11

Reference object layer over the actual `gaussianHodgeTheater` and
`gaussianThreeTheaterSystem`: the Hodge theater already contains a genuine
F-prime-strip and finite theta packet.  No new carrier is introduced. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgePrimeStripObjectsActual

open LeanFormal.IUT

/-- The concrete Hodge theater object of IUT III, Theorem 3.11. -/
def thm311HodgeTheater (l : PrimeGeFive) :
    HodgeTheater l RationalPrimePlace :=
  gaussianHodgeTheater l

theorem thm311HodgeTheater_q (l : PrimeGeFive) :
    (thm311HodgeTheater l).thetaPacket.q = (1 / 2 : Real) :=
  gaussianHodgeTheater_q l

/-- Its F-prime-strip component, referenced from the theater. -/
def thm311FPrimeStrip (l : PrimeGeFive) :
    FPrimeStrip (RationalPrimePlace) :=
  (thm311HodgeTheater l).primeStrip

theorem thm311FPrimeStrip_totalDegree_mul (l : PrimeGeFive)
    (s : Finset RationalPrimePlace) (x y : ∀ v, (thm311FPrimeStrip l).Mon v) :
    (thm311FPrimeStrip l).totalDegree s (x * y) =
      (thm311FPrimeStrip l).totalDegree s x +
        (thm311FPrimeStrip l).totalDegree s y :=
  FPrimeStrip.totalDegree_mul (F := thm311FPrimeStrip l) s x y

/-- The three-theater system of 3.11 with its source-to-target link. -/
def thm311ThreeTheaterSystem (l : PrimeGeFive) :
    ThreeTheaterSystem l RationalPrimePlace :=
  gaussianThreeTheaterSystem l

theorem thm311ThreeTheaterSystem_sourceToTarget_q (l : PrimeGeFive) :
    (thm311ThreeTheaterSystem l).source.thetaPacket.q =
      (thm311ThreeTheaterSystem l).target.thetaPacket.q :=
  gaussianThreeTheaterSystem_q l

def thm311HodgeTheaterLink_refl (l : PrimeGeFive) :
    HodgeTheaterLink (thm311HodgeTheater l) (thm311HodgeTheater l) :=
  HodgeTheaterLink.refl _

end LeanFormal.IUT.XiFPaper.Mzk1HodgePrimeStripObjectsActual

end
