/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCEntryQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEntryGap2QpilotActual
import tmp.sheaf.xif.paper.Mzk1AcceptanceFinalRewriteActual
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureSignedConsumerActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual

/-! # Mzk1EvidenceBundleGreenActual — green evidence bundle (qpilot lane)

A574 (qpilot lane, own name): one bundle over the green components:
* ABC height bound and ABC conclusion (conditional through the bridge data),
* Gap-2 region bound,
* paper target equivalence and
* half-ball qRegion normalized volume = 1.
All fields are actual theorems. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EvidenceBundleGreenActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceFinalRewriteActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureSignedConsumerActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Green evidence bundle. -/
structure EvidenceBundle where
  /-- ABC height bound through the bridge interface. -/
  heightBound : Cor312ToABCBridgeInterface.{0} →
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A
  /-- conditional ABC conclusion through the bridge interface. -/
  abcConjecture : Cor312ToABCBridgeInterface.{0} → ABCConjecture
  /-- paper target equivalence. -/
  paperTargetIff : ∀ qMag thetaMag : Real,
    paperTarget qMag thetaMag ↔ thetaMag ≤ qMag
  /-- half-ball qRegion normalized volume = 1. -/
  qRegionNormalized : qNormalizedVolume T (qRegion T) = 1

/-- The constructed green evidence bundle. -/
noncomputable def evidenceBundle : EvidenceBundle T where
  heightBound := fun D => abcEntry_heightBound D
  abcConjecture := fun D => abcEntry_abcConjecture D
  paperTargetIff := fun qMag thetaMag => acceptance_paperTarget_iff qMag thetaMag
  qRegionNormalized := qNormalizedVolume_qRegion_eq T

#check evidenceBundle

end LeanFormal.IUT.XiFPaper.Mzk1EvidenceBundleGreenActual
end
