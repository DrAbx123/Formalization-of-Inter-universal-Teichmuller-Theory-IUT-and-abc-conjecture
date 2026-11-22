import tmp.sheaf.xif.paper.S2864NewConstructorAudit
import tmp.sheaf.xif.paper.S2856HfOverlapActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaActual
import tmp.sheaf.xif.paper.S2858Z2GroupFinActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2864NewConstructorAudit
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2858Z2GroupFinActual
open LeanFormal.IUT.XiFPaper.S2860A6CoreWithSignActionConditional
open CategoryTheory CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2866NewConstructorAudit2

/-!
## S2866: re-audit after the new alpha/coherence files

New actual progress (alpha side, NOT the 16 fields):
* S2856HfOverlapActual: hfRing and hf_pair are proved, and
  chartYNegGlued : E37ChartYScheme K ⟶ S2820E37ProjectiveScheme K is now an
  unconditional actual morphism.  The previous hf gap is closed.
* S2857GlobalAlphaActual: globalAlphaComp and globalAlpha are actual,
  conditional only on the global Z/Y glue compatibility h.  So alpha is now
  reduced to h plus the square proof; not yet actual.
* S2858Z2GroupFinActual/S2858Z2GroupIfActual: finite-group coherence data,
  but S2859CoherentFinActual still has no olean and fails to compile
  (unsolved associator/unitor goals).  D/atBase/generator_identification
  for S2860 remain unavailable.

The 16 fields in S2860CoreInputs are unchanged and still have no generic
constructor: unique involution; cF/quotient/quotientWitness; xF/cF groups and
fGroupInclusion; xK/cK; xK/cKExtension; xK/cKType; xK/cK_eq_extension; epsilon.

No fake data.
-/

#check hfRing
#check hf_pair
#check chartYNegGlued
#check globalAlphaComp
#check globalAlpha
#check sMapCompGroup
#check S2860CoreInputs

end LeanFormal.IUT.XiFPaper.S2866NewConstructorAudit2
end
