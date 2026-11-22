import tmp.sheaf.xif.paper.S2482QiInvolutionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2456SourceSignQuotientActual

/-- The actual orbicurve constructed by S2482. -/
abbrev S2456Orbicurve : Iut.HyperbolicOrbicurve F := S2482Orbicurve

/-- The actual elliptic involution from the iplsheapt file. -/
abbrev S2456EllipticInvolution : S2456Orbicurve.Hom S2456Orbicurve :=
  S2482EllipticInvolution

/-- Exact missing dependency for cF: a sign action on the actual orbicurve. -/
def S2456SignActionMissing : Prop :=
  Nonempty (Iut.OrbicurveSignAction S2456Orbicurve)

/-- Exact missing dependency for cF: an invariant morphism and its quotient witness. -/
def S2456SignQuotientMissing : Prop :=
  ∃ (action : Iut.OrbicurveSignAction S2456Orbicurve)
    (cF : Iut.HyperbolicOrbicurve F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action cF),
    Nonempty (Iut.OrbicurveSignQuotientWitness action quotient)

/-- Exact missing dependency for cK: an actual scalar extension from F to K. -/
def S2456KSideMissing (K : Type) [Field K] [Algebra F K] : Prop :=
  ∃ (cF : Iut.HyperbolicOrbicurve F)
    (cK : Iut.HyperbolicOrbicurve K)
    (ext : InitialThetaSource.SourceOrbicurveScalarExtension F K cF),
    cK = ext.result

#check S2456Orbicurve
#check S2456EllipticInvolution
#check S2482EllipticInvolution
#check Iut.OrbicurveSignAction
#check Iut.OrbicurveSignInvariantMorphism
#check Iut.OrbicurveSignQuotientWitness
#check InitialThetaSource.SourceOrbicurveScalarExtension

#print axioms S2456EllipticInvolution

end LeanFormal.IUT.XiFPaper.S2456SourceSignQuotientActual

end
