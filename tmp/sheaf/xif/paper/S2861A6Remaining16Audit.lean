import tmp.sheaf.xif.paper.S2860A6CoreWithSignActionConditional
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Iut.Foundations.Orbicurve

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2860A6CoreWithSignActionConditional
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2861A6Remaining16Audit

/-!
## S2861 audit: the 16 remaining S2860CoreInputs fields

For each field we checked for a constructor already in the tree.

1. unique_elliptic_involution
   No uniqueness theorem for stack automorphisms. S2857 gives only one
   involution (and its square); uniqueness remains a gap.

2. cF
3. quotient
4. quotientWitness
   Only actual provider is S2104, which requires
   S1971StackQuotientWitness l A for A : OrbicurveSignAction S1726Orbicurve.
   It cannot instantiate A6. Generic S2854StackQuotientInput is a gap, not a
   constructor. No cF fabricated.

5. xFGroups
6. cFGroups
7. fGroupInclusion
   SourceOrbicurveGroupData has no constructor: it wraps
   Iut.OrbicurveFundamentalGroupData X G, and no construction of that group
   data for an arbitrary realized orbicurve exists in the tree.

8. xK
9. cK
   No K-side HyperbolicOrbicurve is constructed from xF/cF. Scalar extension
   requires its result in advance.

10. xKExtension
11. cKExtension
    SourceOrbicurveScalarExtension requires
    SourceEtaleStackScalarExtension F K X.stack, for which no constructor is
    present in the tree.

12. xKType
13. cKType
    Signature equalities require actual xK/cK (absent).

14. xK_eq_extension
15. cK_eq_extension
    Follow definitionally only after xK/cK and extensions are chosen as the
    extension result; currently absent.

16. epsilon
    OrbicurveBoundaryCusp is a structure with compactification, open immersion,
    residueScheme, point and boundary proof. No generic constructor exists;
    only a specific S2508CuspDataUB.boundaryCusp for S2495cK. The source audit
    file already records that no base-change construction of the boundary cusp
    exists in the tree.

Conclusion: none of the 16 fields has an unconditional automatic supplier.
The only previously removable pair (signAction, signAction_inversion_eq) is
already removed in S2860. Further reduction requires actual cF/quotient stack
witness, orbicurve fundamental group data, K-side scalar extension, or a
boundary cusp, none of which is present generically.
-/

#check S2860CoreInputs
#check S2860S
#check S2860Completion
#check SourceOrbicurveGroupData
#check Iut.OrbicurveFundamentalGroupData
#check SourceOrbicurveScalarExtension
#check SourceEtaleStackScalarExtension
#check Iut.OrbicurveBoundaryCusp
#check S2857StackAuto
#check S2857StackAuto_square
#print axioms S2860S

end LeanFormal.IUT.XiFPaper.S2861A6Remaining16Audit
end
