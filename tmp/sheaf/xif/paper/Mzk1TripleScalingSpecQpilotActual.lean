/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1TripleScalingSpecQpilotActual — triple-dependent scaling spec (A622, supplementary)

Read-only object-data/audit evidence for the paper comparison region with
triple-dependent scaling (the canonical `Mzk1PaperComparisonRegionScalingActual`
is mainline-owned; this file is a qpilot-prefixed supplement and does not
overwrite it).

Design: `region a b c := tripleScale a b c '' (unitRegion ∪ {pt a b c})`, where the
scale is allowed to depend on the ABC triple.  The fixed `scaleShift = id` case is
recorded as the degenerate instance `identityRegion`.

No `True` placeholders. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TripleScalingSpecQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Triple-dependent scaling comparison-region specification on the S1902 carrier. -/
structure TripleScalingSpec where
  /-- the named point `pt a b c` of the ABC triple. -/
  pt : Nat → Nat → Nat → S1902Carrier T
  /-- triple-dependent scaling map. -/
  scale : Nat → Nat → Nat → S1902Carrier T → S1902Carrier T
  /-- the comparison region of the triple. -/
  region : Nat → Nat → Nat → Set (S1902Carrier T)
  /-- the region is the scaled unit region together with the scaled marked point. -/
  region_eq : ∀ a b c : Nat,
    region a b c = scale a b c '' (s1902UnitRegion T ∪ {pt a b c})

/-- Membership characterization of a scaled comparison region. -/
theorem TripleScalingSpec.mem_region (S : TripleScalingSpec T) (a b c : Nat)
    (x : S1902Carrier T) :
    x ∈ S.region a b c ↔
      ∃ y ∈ s1902UnitRegion T ∪ {S.pt a b c}, S.scale a b c y = x := by
  rw [S.region_eq a b c]
  exact Set.mem_image _ _ _

/-- The degenerate fixed-scaling instance: `scale = id`, region is the unit region
together with the marked point (this is the case whose specialized height
comparison is not faithful; recorded only as an object). -/
noncomputable def identityRegion (pt : Nat → Nat → Nat → S1902Carrier T) :
    TripleScalingSpec T where
  pt := pt
  scale := fun _ _ _ => id
  region := fun a b c => s1902UnitRegion T ∪ {pt a b c}
  region_eq := by
    intro a b c
    simp

/-- For the identity instance the region is exactly `unitRegion ∪ {pt}`. -/
theorem identityRegion_region (pt : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) :
    (identityRegion T pt).region a b c = s1902UnitRegion T ∪ {pt a b c} :=
  rfl

/-- Audit rows for the triple-scaling design (name, status, consumer). -/
def tripleScalingAuditRows : List (String × String × String) :=
  [ ("TripleScalingSpec", "DEFINED (supplementary, canonical mainline)",
     "Mzk1TripleScalingSpecQpilotActual.TripleScalingSpec"),
    ("membership characterization", "PROVED",
     "TripleScalingSpec.mem_region"),
    ("identity degenerate case", "PROVED (object only; faithfulness fails)",
     "identityRegion") ]

theorem tripleScalingAuditRows_length : tripleScalingAuditRows.length = 3 := rfl

#check TripleScalingSpec
#check TripleScalingSpec.mem_region
#check identityRegion
#check tripleScalingAuditRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TripleScalingSpecQpilotActual
end
