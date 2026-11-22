/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1StrictnessPackageQpilotActual
import tmp.sheaf.xif.paper.Mzk1ResolvedRequirementAcceptanceQpilotActual
import tmp.sheaf.xif.paper.Mzk1KummerChainAcceptanceActual
import Mathlib.Tactic

/-! # Mzk1StrictChainSummaryQpilotActual — strict chain summary (A596)

Thin summary of the strict chain: 1D strictness, product strictness, resolved
requirement acceptance, and the Kummer realization consumer. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictChainSummaryQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1StrictnessPackageQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerChainAcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal
open scoped NNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {α : Type*} {vol : Set α → Real}

/-- Summary: 1D strict measure increase (thin re-export). -/
theorem chain_oneDim {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    volume (Metric.closedBall (0 : Real) r) <
      volume (Metric.closedBall (0 : Real) R) :=
  strictnessPackage.oneDimVolume hr hrR

/-- Summary: product strictness (thin re-export). -/
theorem chain_prod {ι : Type} [Fintype ι] (f g : ι → ℝ≥0)
    (hpos : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i) (i0 : ι) (hlt : f i0 < g i0) :
    (∏ i, f i) < ∏ i, g i :=
  strictnessPackage.prodStrict f g hpos hle i0 hlt

/-- Summary: resolved requirement strict signed inequality (thin re-export). -/
theorem chain_requirement_strict (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  (resolvedRequirementAcceptance D).strict_signed

/-- The strict chain summary bundle. -/
structure StrictChainSummary (α : Type*) (vol : Set α → Real) where
  oneDim : ∀ {r R : Real}, 0 ≤ r → r < R →
    volume (Metric.closedBall (0 : Real) r) <
      volume (Metric.closedBall (0 : Real) R)
  prod : ∀ {ι : Type} [Fintype ι] (f g : ι → ℝ≥0),
    (∀ i, 0 < f i) → (∀ i, f i ≤ g i) →
    ∀ (i0 : ι), f i0 < g i0 → (∏ i, f i) < ∏ i, g i
  requirementStrict : ∀ (D : XiEContainmentRequirement α vol),
    requirementSignedQ D < requirementSignedTheta D

/-- The constructed strict chain summary. -/
noncomputable def strictChainSummary : StrictChainSummary α vol where
  oneDim := fun {r R} hr hrR => chain_oneDim hr hrR
  prod := fun {ι} _inst f g hpos hle i0 hlt => chain_prod f g hpos hle i0 hlt
  requirementStrict := fun D => chain_requirement_strict D

#check strictChainSummary

end LeanFormal.IUT.XiFPaper.Mzk1StrictChainSummaryQpilotActual
end
