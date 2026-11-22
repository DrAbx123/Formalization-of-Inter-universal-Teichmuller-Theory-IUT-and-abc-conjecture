import tmp.sheaf.xif.paper.S3121GeometricCorePartial
import tmp.sheaf.xif.paper.S2199RepresentableStackActual
import Mathlib.RingTheory.MvPolynomial.Basic
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3121GeometricCorePartial
open LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S3123cKActual
variable {l : PrimeGeFive}
abbrev S3123K (l : PrimeGeFive) : Type := (S3121A (l := l)).K
noncomputable def S3123KOver (l : PrimeGeFive) : Iut.SchemeOverField (S3123K l) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap (S3123K l) (MvPolynomial (Fin 1) (S3123K l)))))
noncomputable def S3123cK (l : PrimeGeFive) : Iut.HyperbolicOrbicurve (S3123K l) :=
  realizedHyperbolicOrbicurve (S3123K l)
    (Iut.schemeRepresentableEtalePseudofunctor (S3123K l) (S3123KOver l))
    (s2199_representable_isStack (S3123K l) (S3123KOver l))
    (sourceTypeOneLTorsionPlusMinus l)
    (sourceTypeOneLTorsionPlusMinus_hyperbolic l)
theorem S3123cK_signature (l : PrimeGeFive) :
    (S3123cK l).signature = sourceTypeOneLTorsionPlusMinus l :=
  realizedHyperbolicOrbicurve_signature (S3123K l) _ _ _ _
noncomputable def S3123xK (l : PrimeGeFive) : Iut.HyperbolicOrbicurve (S3123K l) :=
  realizedHyperbolicOrbicurve (S3123K l)
    (Iut.schemeRepresentableEtalePseudofunctor (S3123K l) (S3123KOver l))
    (s2199_representable_isStack (S3123K l) (S3123KOver l))
    (sourceTypeOneLTorsion l)
    (sourceTypeOneLTorsion_hyperbolic l)

theorem S3123xK_signature (l : PrimeGeFive) :
    (S3123xK l).signature = sourceTypeOneLTorsion l :=
  realizedHyperbolicOrbicurve_signature (S3123K l) _ _ _ _

/-- K-side orbicurves xK/cK with their actual signatures. -/
structure S3123KOrbicurveData (l : PrimeGeFive) where
  xK : Iut.HyperbolicOrbicurve (S3123K l)
  cK : Iut.HyperbolicOrbicurve (S3123K l)
  xKType : xK.signature = sourceTypeOneLTorsion l
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l

noncomputable def S3123KOrbicurveDataActual (l : PrimeGeFive) :
    S3123KOrbicurveData l :={
  xK := S3123xK l
  cK := S3123cK l
  xKType := S3123xK_signature l
  cKType := S3123cK_signature l }

#check S3123KOrbicurveDataActual
#check S3123xK
#check S3123xK_signature
#check S3123cK
#check S3123cK_signature
#print axioms S3123KOrbicurveDataActual
#print axioms S3123xK_signature
#print axioms S3123cK_signature
end LeanFormal.IUT.XiFPaper.S3123cKActual
end
