import Mathlib.Analysis.Convex.Body
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-! # S685: tropical / Newton-Okounkov skeleton tool audit

Mathlib inventory:
* ConvexBody: convex, compact, nonempty bodies and module structure;
* NumberField.mixedEmbedding.convexBodyLT and its volume formula;
* geometry of numbers lattice covolume tools.

No Newton-Okounkov/tropical skeleton API is present. The bridge from the root
extension image hull Haar log to a convex-body volume/skeleton integral is
recorded exactly, not asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S685NewtonOkounkovToolAuditActual

open MeasureTheory

#check ConvexBody
#check ConvexBody.isCompact
#check ConvexBody.convex
#check NumberField.mixedEmbedding.convexBodyLT_volume
#check MeasureTheory.addHaar_smul_of_nonneg

/-- Exact missing bridge: finite-dimensional real convex body, skeleton
integral, and Haar-log equality. -/
structure NewtonOkounkovSkeletonBridge where
  ambient : Type
  [normedAddCommGroup : NormedAddCommGroup ambient]
  [normedSpace : NormedSpace Real ambient]
  [finiteDimensional : FiniteDimensional Real ambient]
  [measurableSpace : MeasurableSpace ambient]
  [borelSpace : BorelSpace ambient]
  body : ConvexBody ambient
  haarLog : Real
  skeletonIntegral : Real
  haarLog_eq_skeleton : haarLog = skeletonIntegral
  latticeCovolume : Real
  qPilotContainmentReducesToLattice : Prop

attribute [instance] NewtonOkounkovSkeletonBridge.normedAddCommGroup
  NewtonOkounkovSkeletonBridge.normedSpace
  NewtonOkounkovSkeletonBridge.finiteDimensional
  NewtonOkounkovSkeletonBridge.measurableSpace
  NewtonOkounkovSkeletonBridge.borelSpace

/-- Exact missing bridge datum. -/
def NewtonOkounkovSkeletonBridgeRequired : Prop :=
  Nonempty NewtonOkounkovSkeletonBridge

end LeanFormal.IUT.XiFPaper.S685NewtonOkounkovToolAuditActual

end
