import tmp.sheaf.xif.paper.QVFamTensorCoefficientInclusionActual

/-!
# qPilot region versus completion power hull: exact region factor gap

The actual qPilot region of the qVFamily block is

  qVFamQPilotRegion T b = F(c_b) * O_hol.

The S74 completion power hull lives on the generic source-geometry tensor block
constructed from G.qUnit, not on this qVFamily one-factor block.  There is no
actual inclusion theorem between them in the current tree, and the qUnit tensor
unit part / qPilot fractional-lattice coefficient comparison is missing.

This file records the exact region/factor gap.  It does not assume the
inclusion and does not assert a numerical comparison.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QPilotCompletionPowerRegionGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientInclusionActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily qPilot region. -/
noncomputable abbrev qPilotRegionActual : Set (qVFamTensorBlock T b) :=
  qVFamQPilotRegion T b

/-- Exact qPilot/completion-power region gap data. -/
structure QPilotCompletionPowerRegionGap where
  qPilotRegion : Set (qVFamTensorBlock T b)
  qPilotRegion_eq : qPilotRegion = qPilotRegionActual T b
  completionHullCarrier : Prop
  completionHullRegion : Prop
  correctionScalar : Prop
  qPilotRegion_in_completionHull : Prop
  completionHull_in_qPilotRegion : Prop
  region_equality_after_correction : Prop

/-- The exact missing region/factor object. -/
def QPilotCompletionPowerRegionGapRequired : Prop :=
  Nonempty (QPilotCompletionPowerRegionGap (T := T) b)

/-- Consumer status: the actual qPilot region is defined, but the comparison
with the generic completion power hull is an exact factor gap, not a proved
inclusion. -/
def QPilotCompletionPowerRegionNotProved : Prop :=
  QPilotCompletionPowerRegionGapRequired (T := T) b

end LeanFormal.IUT.XiFPaper.QPilotCompletionPowerRegionGapActual
end
