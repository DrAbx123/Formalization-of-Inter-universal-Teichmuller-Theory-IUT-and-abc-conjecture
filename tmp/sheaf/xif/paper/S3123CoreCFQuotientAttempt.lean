import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import Iut.Foundations.Orbicurve

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3123CoreCFQuotientAttempt

variable {l : PrimeGeFive}

/-- Core cF/cK data with sign action, quotient invariant, quotient witness, and
boundary cusp. All objects are explicit parameters; nothing is fabricated. -/
structure S3123CoreCFData where
  cF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F
  cK : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F
  signAction : Iut.OrbicurveSignAction cK
  quotientInv : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotientInv
  epsilon : Iut.OrbicurveBoundaryCusp cK

/-- Exact target: existence of the core cF/cK quotient data. -/
def S3123CoreCFQuotientTarget : Prop :=
  Nonempty (S3123CoreCFData (l := l))

#check S3123CoreCFData
#check S3123CoreCFQuotientTarget

end LeanFormal.IUT.XiFPaper.S3123CoreCFQuotientAttempt
end