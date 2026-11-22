import tmp.sheaf.xif.paper.S3123FiberStrongTransActual
import tmp.sheaf.xif.paper.S3123XKStackExtension
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3123XKExtensionActual
variable {l : PrimeGeFive}
abbrev S3123XF (l : PrimeGeFive) : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F := S1536XF (l := l)
noncomputable def S3123xKResult (l : PrimeGeFive) : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K :=
  realizedHyperbolicOrbicurve (S1280Arithmetic l).K
    (S3123Result (l := l)).fiber (S3123Result (l := l)).isStack
    (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l)
theorem S3123xKResult_signature (l : PrimeGeFive) :
    (S3123xKResult l).signature = sourceTypeOneLTorsion l :=
  realizedHyperbolicOrbicurve_signature (S1280Arithmetic l).K _ _ _ _
noncomputable def S3123XKStackExtension (l : PrimeGeFive)
    (E : Bicategory.Equivalence
      (S3123Result (l := l)).fiber
      (Pseudofunctor.comp
        (schemeRestrictScalarsPseudofunctor
          (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber)) :
    SourceEtaleStackScalarExtension
      (S1280Arithmetic l).F (S1280Arithmetic l).K (S1536XF (l := l)).stack where
  result := (S3123xKResult l).stack
  fiberEquivalence := E
noncomputable def S3123XKOrbicurveExtension (l : PrimeGeFive)
    (E : Bicategory.Equivalence
      (S3123Result (l := l)).fiber
      (Pseudofunctor.comp
        (schemeRestrictScalarsPseudofunctor
          (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber)) :
    SourceOrbicurveScalarExtension
      (S1280Arithmetic l).F (S1280Arithmetic l).K (S1536XF (l := l)) where
  result := S3123xKResult l
  stackExtension := S3123XKStackExtension l E
  target_stack := rfl
  genus_preserved := by
    rw [S3123xKResult_signature, S1536XF_signature]
    rfl

#check S3123XKOrbicurveExtension
#check S3123xKResult
#check S3123XKStackExtension
end LeanFormal.IUT.XiFPaper.S3123XKExtensionActual
end
