import tmp.sheaf.xif.paper.S2858A6SFromCore
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2858A6SFromCore
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2856A6CoreWithInvolution
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2859A6CoreFieldReductionAudit

/-!
## S2859 audit: which of the 18 S2856Core fields are auto-fillable

S2857 gives:
* inversion := S2857StackAuto alpha
* inversionSquared := S2857StackAuto_square alpha halpha

S2852 gives the constructor:
* orbicurveSignActionOf (D) (atBase) inversion
    generator_identification inversionSquared : OrbicurveSignAction X

Therefore, GIVEN D : SignActionIndex ⥤ᵖ EtaleStackPseudofunctor F,
atBase, and generator_identification, the field signAction is auto-fillable;
then signAction_inversion_eq_ellipticInvolution is rfl.

NOT auto-fillable from S2853/S2855:
* unique_elliptic_involution: no uniqueness theorem for the stack automorphism.
* cF / quotient / quotientWitness: need a generic stack quotient witness
  (S2104 only covers S1726).
* xFGroups / cFGroups / fGroupInclusion: no group data construction.
* xK / cK / xKExtension / cKExtension / xKType / cKType /
  xK_eq_extension / cK_eq_extension / epsilon: K-side data absent.

S2853 supplies only a chart-Z negation endomorphism and chart-Y negation
formula; S2855ChartYDirectedCover supplies a directed cover, not a global
scheme endomorphism alpha or alpha^2 = 1.  Thus alpha/halpha themselves are
still explicit inputs.

Current S2858CoreInputs therefore has NO field that S2853/S2855 fills
unconditionally.  The only reduction available is:
* if S2852's coherence data D/atBase/generator_identification is supplied,
  then signAction and signAction_inversion_eq can be removed from the 18;
* alpha/halpha still explicit;
* if S2104's S1971StackQuotientWitness were available for A6,
  cF/quotient/quotientWitness could be removed (not available).
-/

#check S2857StackAuto
#check S2857StackAuto_square
#check Iut.orbicurveSignActionOf
#check S2858CoreInputs
#check S2858S
#check S2858Completion
#print axioms Iut.orbicurveSignActionOf

end LeanFormal.IUT.XiFPaper.S2859A6CoreFieldReductionAudit
end
