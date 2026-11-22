import tmp.sheaf.xif.paper.S2861A6Remaining16Audit
import Iut.Foundations.Orbicurve
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2860A6CoreWithSignActionConditional
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2862GenericConstructorAudit

/-!
## S2862: deeper audit for new generic constructors of the 16 fields

We inspected the actual structure fields and available generic API.

1. unique_elliptic_involution
   No generic uniqueness of stack automorphisms; S2857 only constructs one
   involution and its square. No new constructor.

2. cF / quotient / quotientWitness
   Only S2104 for S1726. Generic S2854StackQuotientInput is an interface, not
   a constructor. No new generic constructor.

3-5. xFGroups / cFGroups / fGroupInclusion
   SourceOrbicurveGroupData is a wrapper around
   Iut.OrbicurveFundamentalGroupData, which itself requires
   Category/GaloisCategory/fiberFunctor fields for the finite-etale cover
   category. No constructor in the tree. fGroupInclusion is a further
   ProfiniteFundamentalGroupInclusion datum, not derived automatically.
   No new generic constructor.

6-7. xK / cK
   A K-side HyperbolicOrbicurve can only be realized from a K-side etale stack
   with IsStack and signature (realizedHyperbolicOrbicurve). No such K-side
   stack is constructed.

8-9. xKExtension / cKExtension
   SourceOrbicurveScalarExtension requires
   SourceEtaleStackScalarExtension F K X.stack, whose field is an
   EtaleStackOverField K. The latter requires a K-fiber together with an
   IsStack proof. The natural candidate fiber is
   Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K) X.stack.fiber,
   but no IsStack instance for this composite is proved in the tree.
   No generic constructor.

10-11. xKType / cKType
    Would follow from the signature of a realized xK/cK. Since xK/cK are
    absent, no constructor.

12-13. xK_eq_extension / cK_eq_extension
    Are definitional only if xK/cK are chosen as the scalar-extension result.
    Since scalar extensions are absent, no constructor.

14. epsilon
    Iut.OrbicurveBoundaryCusp requires compactification, open immersion,
    residue scheme, point, and boundary proof. No generic constructor; only a
    specific S2508CuspDataUB.boundaryCusp for S2495cK.

Conclusion: no new generic constructor exists for any of the 16 fields.
Only formal reductions are definitional after an upstream object is
constructed; no such upstream object is available. No fake data.
-/

#check SourceOrbicurveGroupData
#check Iut.OrbicurveFundamentalGroupData
#check Iut.OrbicurveEtaleFundamentalGroup
#check SourceOrbicurveScalarExtension
#check SourceEtaleStackScalarExtension
#check Iut.EtaleStackOverField
#check LeanFormal.IUT.InitialThetaSource.schemeRestrictScalarsPseudofunctor
#check Iut.OrbicurveBoundaryCusp
#check S2860CoreInputs

end LeanFormal.IUT.XiFPaper.S2862GenericConstructorAudit
end
