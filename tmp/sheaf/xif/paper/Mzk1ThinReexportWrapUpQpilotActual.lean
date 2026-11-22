/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThinReexportBundleQpilotActual
import tmp.sheaf.xif.paper.Mzk1A618ProofQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual
import tmp.sheaf.xif.paper.Mzk1HeightWeightFromTripleQpilotActual

/-! # Mzk1ThinReexportWrapUpQpilotActual — thin re-export wrap-up (A646)

Wrap-up of the thin re-export chain: the bundle is inhabited, and the two main
payloads (A618 height estimate and triple height-weight bound) are re-exported. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThinReexportWrapUpQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1ThinReexportBundleQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1A618ProofQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Wrap-up: the thin re-export bundle is inhabited. -/
theorem thinReexport_available : Nonempty (ThinReexportBundle T) :=
  ⟨thinReexportBundle T⟩

/-- Wrap-up: A618 height estimate re-export. -/
theorem thinReexport_heightEstimate {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) :=
  a618_heightEstimate C h0 h1

/-- Wrap-up: triple-comparison height-weight bound re-export. -/
theorem thinReexport_tripleBound
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    HeightWeightBoundShape :=
  heightWeightBoundShape_of_tripleComparison T point C

#check thinReexport_available
#check thinReexport_tripleBound

end LeanFormal.IUT.XiFPaper.Mzk1ThinReexportWrapUpQpilotActual
end
