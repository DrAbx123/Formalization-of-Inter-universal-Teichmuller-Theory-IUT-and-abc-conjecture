/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A618AuditQpilotActual
import tmp.sheaf.xif.paper.Mzk1TripleScalingSpecQpilotActual
import tmp.sheaf.xif.paper.Mzk1TripleScalingAlignQpilotActual
import tmp.sheaf.xif.paper.Mzk1A618ProofQpilotActual
import tmp.sheaf.xif.paper.Mzk1S1902ConcreteBridgeQpilotActual
import tmp.sheaf.xif.paper.Mzk1HqnegDischargedGateQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual

/-! # Mzk1FullAuditSummaryQpilotActual — full audit summary (A626)

One summary object over the green audit/chain files: A618 8-row audit, triple-scaling
3-row audit, the S1902 concrete bridge height bound, the discharged-hqneg existence
result, and the A618 height estimate proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FullAuditSummaryQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1A618AuditQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1TripleScalingSpecQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1TripleScalingAlignQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1A618ProofQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902ConcreteBridgeQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegDischargedGateQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Full audit summary. -/
structure FullAuditSummary where
  qpilotRows : qpilotAuditRows.length = 8
  tripleRows : tripleScalingAuditRows.length = 3
  s1902Bridge : ∀ (C : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (s1902IQHullLogVolumeInterface T) epsilon),
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A
  hqnegDischarged : ∀ (qRead : Real), qRead < 0 → ∀ (apt : Prop), apt →
    ∃ C : StepXIContract, Cor312Conclusion C

/-- The constructed full audit summary. -/
noncomputable def fullAuditSummary : FullAuditSummary T where
  qpilotRows := qpilotAuditRows_length
  tripleRows := tripleScalingAuditRows_length
  s1902Bridge := fun C => s1902Bridge_heightBound T C
  hqnegDischarged := fun qRead hq apt hapt =>
    hqnegDischarged_exists T qRead hq (SHEArrowStatement T)
      (sheArrowStatement_proved T) apt hapt

#check fullAuditSummary

end LeanFormal.IUT.XiFPaper.Mzk1FullAuditSummaryQpilotActual
end
