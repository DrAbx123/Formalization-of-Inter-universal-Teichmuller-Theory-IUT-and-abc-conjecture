import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

open CategoryTheory
open LeanFormal.IUT

namespace Probe

#check Iut.OrbicurveFiniteEtaleCover
#check Iut.OrbicurveFiniteEtaleCoverMap

noncomputable abbrev X : Iut.HyperbolicOrbicurve LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual.S1726K :=
  LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual.S1726Orbicurve

#check Iut.OrbicurveFiniteEtaleCover X
#check Iut.OrbicurveFiniteEtaleCoverMap (X := X)

def Cover : Type 1 := Iut.OrbicurveFiniteEtaleCover X

def Map (A B : Cover) : Type 1 := Iut.OrbicurveFiniteEtaleCoverMap A B

#check Category.{0, 1} Cover
#check @GaloisCategory.{0, 1} Cover
#check CategoryTheory.Core
#check CategoryTheory.Bicategory.Pith
#check @Quot

example (A B : Cover) : Type 1 := Map A B

end Probe
