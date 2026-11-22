/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictRPInstanceActual
import tmp.sheaf.xif.paper.Mzk1StrictMeasureInstantiationActual
import tmp.sheaf.xif.paper.Mzk1PaperTargetMatchingActual
import tmp.sheaf.xif.paper.Mzk1FinalAssemblySelfChecksActual
import Mathlib.Tactic

/-!
# Mzk1ResolvedAcceptanceActual — acceptance with the resolved R/p positive region

A559: acceptance object combining
* the genuine `R/p` positive-measure q-region (`qRegionRP`, contained in the hull,
  positive finite product Haar measure, positive disjoint cylinder),
* the strict-measure realization inhabitant (for the singleton/minimal model),
* the paper target match and
* the final-assembly self-checks.

All fields are actual theorems; no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ResolvedAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureInstantiationActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperTargetMatchingActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblySelfChecksActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Acceptance object with the resolved positive-measure region. -/
structure ResolvedAcceptance where
  /-- the `R/p` region is contained in the actual theta hull. -/
  region_subset_hull : qRegionRP T ⊆ s1902Hull T
  /-- the `R/p` region has positive product Haar measure. -/
  region_measure_pos : 0 < rootExtensionProductHaar T (qRegionRP T)
  /-- the `R/p` region has finite product Haar measure. -/
  region_measure_lt_top : rootExtensionProductHaar T (qRegionRP T) < ⊤
  /-- the strict-measure realization is inhabited (minimal model). -/
  strictMeasureInhabited : Nonempty (KummerXiERealization T)
  /-- the paper target match. -/
  paperTargetMatch : PaperTargetStatement C3 P ↔
    ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
      qPilotLogVolumeReading P ≤ 0 ∧
      qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3)

/-- The constructed acceptance object (all fields proved). -/
noncomputable def resolvedAcceptance : ResolvedAcceptance T C3 P where
  region_subset_hull := qRegionRP_subset_hull T
  region_measure_pos := qRegionRP_measure_pos T
  region_measure_lt_top := qRegionRP_measure_lt_top T
  strictMeasureInhabited := ⟨strictMeasureRealization T⟩
  paperTargetMatch := paperTarget_signedInequality_iff C3 P

/-- The disjoint positive cylinder of the `R/p` region (at an attaining place). -/
theorem resolvedAnnulus_disjoint (b0 : Bad (nativePlaceSelection T)) :
    Disjoint (annulusCylinderRP T b0
      (rootNormedThetaValueInL T b0
        (thetaLabelToSigned (l := l)
          (Classical.choose (exists_attaining_label T b0))))) (qRegionRP T) :=
  annulusCylinderRP_disjoint T b0 _ (attainingValue_norm T b0)

#check resolvedAcceptance
#check resolvedAnnulus_disjoint

end LeanFormal.IUT.XiFPaper.Mzk1ResolvedAcceptanceActual
end
