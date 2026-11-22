import tmp.sheaf.xif.paper.S2902CoreWithQMinimalActual
import tmp.sheaf.xif.paper.S2910VDataInputActual
import tmp.sheaf.xif.paper.S2901CuspBoundaryInputActual
import tmp.sheaf.xif.paper.S2895KSideInputActual
import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2902CoreWithQMinimalActual
open LeanFormal.IUT.XiFPaper.S2892CoreWithQActual
open LeanFormal.IUT.XiFPaper.S2910VDataInputActual
open LeanFormal.IUT.XiFPaper.S2901CuspBoundaryInputActual
open LeanFormal.IUT.XiFPaper.S2895KSideInputActual
open LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2879NontrivialStackAutoActual
open LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2912CorrectedConsumerAudit

/-!
Corrected-S consumer audit.  The corrected structure
SourceSignQuotientDataCorrected has the same field list as
SourceSignQuotientData, except that uniqueness excludes the identity and
ellipticInvolution_nontrivial is explicit.  Field replacements:

xF                         -> S2855HyperbolicOrbicurve (actual S2851)
xF_geometry                -> S2855Geometry (actual S2851)
ellipticInvolution         -> S2857StackAuto alphaOverS2844 (actual S2857)
ellipticInvolution_squared -> S2857StackAuto_square alphaOverS2844 alphaOverS2844_square
ellipticInvolution_nontrivial -> S2879_nontrivial
unique_elliptic_involution -> S2883_unique (from S2883Inputs.classification)
signAction                 -> S2869SignAction D atBase generator_identification
signAction_inversion_eq_ellipticInvolution -> rfl for S2869SignAction
cF/quotient/quotientWitness -> S2891CF hQ plus S2870QuotientWitnessData (explicit)
xFGroups/cFGroups/fGroupInclusion -> S2884 CoreGroupsInput
xK/cK/xKExtension/cKExtension -> S2895KInput
xKType/cKType               -> explicit signature equalities (S2895KInput does not supply them)
V/V_mod_bad/...             -> S2910VInput
epsilon                     -> S2901CuspInput.toGenericCuspData or S2885/S2890
-/

#check SourceSignQuotientDataCorrected
#check S2855HyperbolicOrbicurve
#check S2855Geometry
#check S2857StackAuto
#check S2857StackAuto_square
#check S2879_nontrivial
#check S2883_unique
#check S2869SignAction
#check S2895KInput
#check S2910VInput
#check S2901CuspInput
#check S2902Inputs
#check S2892Inputs
#check S2848Completion

end LeanFormal.IUT.XiFPaper.S2912CorrectedConsumerAudit
end