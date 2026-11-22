import tmp.sheaf.xif.paper.S2482QiCurveActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2463InvariantQuotientActual

/-- The invariant coordinate ring model of the sign quotient: F[x]. -/
abbrev S2463InvariantCoordinateRing : Type := MvPolynomial (Fin 1) F

/-- The invariant coordinate function. -/
def S2463InvariantCoordinate : S2463InvariantCoordinateRing := MvPolynomial.X 0

/-- The affine scheme model Spec F[x] of the quotient cF. -/
abbrev S2463cFScheme : Scheme :=
  Spec (CommRingCat.of S2463InvariantCoordinateRing)

/-- The affine scheme Spec F[x] as an object over Spec F. -/
abbrev S2463cFOver : Iut.SchemeOverField F :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F S2463InvariantCoordinateRing)))

/-- Base change model K[x] of the quotient. -/
abbrev S2463cKCoordinateRing (K : Type) [Field K] [Algebra F K] : Type :=
  MvPolynomial (Fin 1) K

/-- Spec K[x] as a scheme over K. -/
abbrev S2463cKScheme (K : Type) [Field K] [Algebra F K] : Scheme :=
  Spec (CommRingCat.of (S2463cKCoordinateRing K))

/-- Exact missing upgrade of the affine model to the hyperbolic orbicurve cF with the
source type-one plus-minus signature. -/
def S2463cFHyperbolicMissing (l : PrimeGeFive) : Prop :=
  ∃ cF : Iut.HyperbolicOrbicurve F,
    cF.signature = InitialThetaSource.sourceTypeOneLTorsionPlusMinus l

#check S2463InvariantCoordinateRing
#check S2463cFOver
#check S2463cKScheme
#check S2463cFHyperbolicMissing

end LeanFormal.IUT.XiFPaper.S2463InvariantQuotientActual

end
