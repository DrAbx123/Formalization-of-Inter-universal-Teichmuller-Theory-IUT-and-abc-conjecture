import tmp.sheaf.xif.paper.S2867A6CoreActualInvolutionSignAction
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2867A6CoreActualInvolutionSignAction
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2848D6F6CompleteActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2868A6FieldConstructorBlockers

/-!
## S2868: exact first missing dependency for each of the 16 fields

After S2867, alpha/halpha and signAction are handled.  The 16 fields of
S2867CoreInputs are audited one by one against the actual API; none has a
constructor, and we record the precise first missing object.

1. unique_elliptic_involution
   Missing: a uniqueness theorem for endomorphisms of the realized stack fiber
   with a square-two-cell.  S2857 only supplies one involution.

2. cF
3. quotient
4. quotientWitness
   Missing: a generic S1971 stack-quotient witness for
   S2855HyperbolicOrbicurve.  S2104's provider is type-locked to
   A : OrbicurveSignAction S1726Orbicurve.

5. xFGroups
6. cFGroups
7. fGroupInclusion
   Missing: Iut.OrbicurveEtaleFundamentalGroup X G.  Its fields include
   coverCategory, galoisCategory, baseScheme, basePoint, fiber, fiberFunctor,
   coverMorphism and coherence; no constructor exists.  SourceOrbicurveGroupData
   merely wraps OrbicurveFundamentalGroupData of this.

8. xK
9. cK
   Missing: an EtaleStackOverField K with IsStack for the K-side fiber.
   MissingD6GeometricRealization S2848D6 is only over K=A6F6 and contains no
   K-side stack for A6.K.

10. xKExtension
11. cKExtension
    Missing: SourceEtaleStackScalarExtension A6.F A6.K X.stack.  Its
    EtaleStackOverField K field requires IsStack of the restricted-scalars
    composite; no such instance is proved.

12. xKType
13. cKType
    Missing: actual xK/cK whose signature can be checked.  No xK/cK.

14. xK_eq_extension
15. cK_eq_extension
    Definitional only after xK/cK are chosen as extension results; extensions
    absent.

16. epsilon
    Missing: Iut.OrbicurveBoundaryCusp cK: compactification, open immersion,
    residue scheme, point and boundary proof.  No generic constructor; only
    S2508CuspDataUB.boundaryCusp for S2495cK.

Conclusion: still no generic constructor for any of the 16 fields.  The
S2867 reduction removes alpha/halpha and signAction but leaves these 16.
No fake data.
-/

#check Iut.OrbicurveEtaleFundamentalGroup
#check Iut.OrbicurveFundamentalGroupData
#check SourceEtaleStackScalarExtension
#check Iut.EtaleStackOverField
#check Iut.OrbicurveBoundaryCusp
#check S2848D6
#check S2867CoreInputs

end LeanFormal.IUT.XiFPaper.S2868A6FieldConstructorBlockers
end
