/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1TripleScalingAlignQpilotActual
import tmp.sheaf.xif.paper.Mzk1S1902CanonicalReexportQpilotActual
import Mathlib.Tactic

/-! # Mzk1ScalingAuditSummaryQpilotActual — scaling audit summary (A628)

Read-only audit evidence for the triple-dependent scaling paper comparison region:
mainline canonical file `Mzk1PaperComparisonRegionScalingActual` (region shape +
conditional ABC), the qpilot alignment with the bridge comparison region, and the
canonical S1902 hull finiteness.  No canonical file is overwritten. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingAuditSummaryQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1TripleScalingAlignQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902CanonicalReexportQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Scaling audit rows (name, status, consumer). -/
def scalingAuditRows : List (String × String × String) :=
  [ ("paper comparison region shape", "GREEN (mainline canonical)",
     "Mzk1PaperComparisonRegionScalingActual.paperComparisonRegion_shape"),
    ("triple-dependent comparison gaps", "NAMED (Gap1/Gap2 fields)",
     "TripleDependentComparison"),
    ("conditional ABC from triple region", "GREEN (conditional)",
     "Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison"),
    ("bridge alignment of triple scaling", "GREEN (qpilot supplementary)",
     "Mzk1TripleScalingAlignQpilotActual.bridgeScalingSpec"),
    ("canonical S1902 hull finiteness", "GREEN (hull canonical re-export)",
     "Mzk1S1902CanonicalReexportQpilotActual.canonicalIQHull_finite") ]

theorem scalingAuditRows_length : scalingAuditRows.length = 5 := rfl

/-- Scaling audit payload: shape, conditional ABC, qpilot alignment, hull finiteness. -/
structure ScalingAuditPayload where
  regionShape : ∀ (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat),
    paperComparisonRegion T point a b c =
      tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c})
  conditionalABC : ∀ (point : Nat → Nat → Nat → S1902Carrier T),
    TripleDependentComparison T point → ABCConjecture
  alignment : ∀ (pt : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat),
    (bridgeScalingSpec T pt).region a b c =
      (s1902IQHullLogVolumeInterface T).scaleShift ''
        ((s1902IQHullLogVolumeInterface T).unitRegion ∪ {pt a b c})
  canonicalHullFinite :
    (canonicalIQHull T).logVolume (canonicalIQHull T).hull < ⊤

/-- The constructed scaling audit payload. -/
noncomputable def scalingAuditPayload : ScalingAuditPayload T := by
  haveI : Nonempty (Bad (nativePlaceSelection T)) := bad_nonempty T
  exact
    { regionShape := fun point => paperComparisonRegion_shape T point
      conditionalABC := fun point C => abc_of_tripleComparison T point C
      alignment := fun pt => bridgeScalingSpec_region_eq T pt
      canonicalHullFinite := canonicalIQHull_finite T }

#check scalingAuditRows_length
#check scalingAuditPayload

end LeanFormal.IUT.XiFPaper.Mzk1ScalingAuditSummaryQpilotActual
end
