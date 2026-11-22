import tmp.sheaf.xif.paper.S2862GenericConstructorAudit
import tmp.sheaf.xif.paper.S2856HfOverlapActual
import tmp.sheaf.xif.paper.S2858CoherentDiagramPartialActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2862GenericConstructorAudit
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
open LeanFormal.IUT.XiFPaper.S2858CoherentDiagramPartialActual
open LeanFormal.IUT.XiFPaper.S2860A6CoreWithSignActionConditional
open CategoryTheory CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2864NewConstructorAudit

/-!
## S2864: re-audit of the 16 fields after the new overlap/coherence files

New actual files:
* S2856HfOverlapActual: identifies the chart-Y pullback with the overlap
  tensor spectrum and reduces the glue compatibility hf to HfOverlapRing K.
  This concerns alpha, not any of the 16 fields.
* S2858CoherentDiagramPartialActual: provides S2858DMap, S2858DMapId and
  signGroup_cases for the candidate C2 action.  It does NOT provide the full
  diagramC (the full coherence proof is in S2859CoherentActual, which has no
  olean and currently fails to compile: first error "inv is not a morphism"
  in the associator case).  Therefore it cannot supply D for S2860 either.

The 16 fields remain exactly as in S2861/S2862:
unique involution, cF/quotient/quotientWitness, xF/cF groups and inclusion,
xK/cK, xK/cKExtension, xK/cKType, xK/cK_eq_extension, epsilon.

No new generic constructor is present.  No fake data.
-/

#check HfOverlapRing
#check hf_of_overlapRing
#check S2858DMap
#check S2858DMapId
#check S2858_signGroup_cases
#check S2860CoreInputs

end LeanFormal.IUT.XiFPaper.S2864NewConstructorAudit
end
