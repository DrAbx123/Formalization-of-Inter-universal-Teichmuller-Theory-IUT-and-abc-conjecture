import tmp.sheaf.xif.paper.S3121QuotientActual
import tmp.sheaf.xif.paper.S3121SignActionActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction

noncomputable section
open LeanFormal.IUT CategoryTheory
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S3121SignActionActual
open LeanFormal.IUT.XiFPaper.S3121QuotientActual

namespace LeanFormal.IUT.XiFPaper.S3121GeometricCorePartial

variable {l : PrimeGeFive}

abbrev S3121A := S1280Arithmetic l

noncomputable def S3121GeometricCorePartial
    (unique_elliptic_involution :
      ∀ inv : (S1536XF (l := l)).Hom (S1536XF (l := l)),
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))) →
        inv = S3119NegEllipticInvolution (l := l))
    (quotientWitness :
      Iut.OrbicurveSignQuotientWitness
        (S3121SignActionActual (l := l)) (S3121Quotient (l := l)))
    (xFGroups : SourceOrbicurveGroupData (S1536XF (l := l))
      (Iut.AbsoluteGaloisProfinite (S3121A (l := l)).F))
    (cFGroups : SourceOrbicurveGroupData (S3121cF (l := l))
      (Iut.AbsoluteGaloisProfinite (S3121A (l := l)).F))
    (fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
      xFGroups.sequence.geometric xFGroups.sequence.arithmetic
      cFGroups.sequence.geometric cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite (S3121A (l := l)).F)
      xFGroups.sequence cFGroups.sequence)
    (xK : Iut.HyperbolicOrbicurve (S3121A (l := l)).K)
    (cK : Iut.HyperbolicOrbicurve (S3121A (l := l)).K)
    (xKExtension : SourceOrbicurveScalarExtension
      (S3121A (l := l)).F (S3121A (l := l)).K (S1536XF (l := l)))
    (cKExtension : SourceOrbicurveScalarExtension
      (S3121A (l := l)).F (S3121A (l := l)).K (S3121cF (l := l)))
    (xKType : xK.signature = sourceTypeOneLTorsion l)
    (cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l)
    (xK_eq_extension : xK = xKExtension.result)
    (cK_eq_extension : cK = cKExtension.result)
    (epsilon : Iut.OrbicurveBoundaryCusp cK) :
    SourceSignQuotientGeometricCore (S3121A (l := l)) where
  xF := S1536XF (l := l)
  xF_geometry := S1536XFGeometry (l := l)
  ellipticInvolution := S3119NegEllipticInvolution (l := l)
  ellipticInvolution_squared := S3119NegEllipticInvolution_squared (l := l)
  unique_elliptic_involution := unique_elliptic_involution
  signAction := S3121SignActionActual (l := l)
  signAction_inversion_eq_ellipticInvolution := rfl
  cF := S3121cF (l := l)
  quotient := S3121Quotient (l := l)
  quotientWitness := quotientWitness
  xFGroups := xFGroups
  cFGroups := cFGroups
  fGroupInclusion := fGroupInclusion
  xK := xK
  cK := cK
  xKExtension := xKExtension
  cKExtension := cKExtension
  xKType := xKType
  cKType := cKType
  xK_eq_extension := xK_eq_extension
  cK_eq_extension := cK_eq_extension
  epsilon := epsilon

#check S3121GeometricCorePartial

end LeanFormal.IUT.XiFPaper.S3121GeometricCorePartial
end
