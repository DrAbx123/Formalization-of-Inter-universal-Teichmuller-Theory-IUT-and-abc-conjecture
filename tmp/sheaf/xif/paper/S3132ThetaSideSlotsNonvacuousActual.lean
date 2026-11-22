import tmp.sheaf.xif.paper.S3132ThetaSideComparisonRegionBundleV2Actual
import tmp.sheaf.xif.paper.S3132ThetaSideHullSlotWiringActual
import tmp.sheaf.xif.paper.S3132ThetaSideQSideSlotWiringActual
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideSlotsNonvacuousActual

/-!
# STEP 0 prior-art: ThetaSideHullBoundSlot|ThetaSideQSideSlot|modelThetaValue -> hits S3132ThetaSideHullSlotWiringActual + S3132ThetaSideQSideSlotWiringActual (slots as hypotheses) -> ADAPT (construct NONVACUOUS instances; elementary real arithmetic only; no closure claim).

# Theta side: H4/H5 slots are NONVACUOUS (explicit instances, no closure claim)

The H4 hull-volume bound and H5 q-side signed comparison were carried as explicit
hypotheses.  This file shows they are nonvacuous on the model side by constructing
explicit instances from elementary real arithmetic (theta := |canonical value| for
H4; q := -(|canonical value|+1) for H5).  This does NOT prove the paper's
certificate/AMPL hull bound nor the paper q-pilot comparison (those remain class B);
it only removes the vacuity worry.  Registry frozen 14041.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **H4 nonvacuous instance:** with theta := |canonical readout|, the hull bound
is elementary (`x <= |x|`). -/
def thetaSideHullBoundSlotNonvacuous : ThetaSideHullBoundSlot M :=
  { theta := |modelThetaValue M|
    theta_nonneg := abs_nonneg _
    hull_le_theta := le_abs_self _ }

/-- The nonvacuous H4 slot satisfies its defining inequality. -/
theorem thetaSideHullBoundSlotNonvacuous_le :
    modelThetaValue M ≤ (thetaSideHullBoundSlotNonvacuous M).theta :=
  le_abs_self _

/-- **H5 nonvacuous instance:** q := -(|canonical readout| + 1) is negative and
satisfies the signed comparison (`x <= |x| + 1`). -/
def thetaSideQSideSlotNonvacuous : ThetaSideQSideSlot M :=
  { qSigned := -(|modelThetaValue M| + 1)
    q_negative := by linarith [abs_nonneg (modelThetaValue M)]
    q_le_thetaSigned := by linarith [le_abs_self (modelThetaValue M)] }

/-- The nonvacuous H5 slot yields the adapted Corollary 3.12 payload. -/
def thetaSideQSideComparisonDataNonvacuous : AdaptedCorollary312ComparisonData :=
  thetaSideQSideSlot_comparisonData M (thetaSideQSideSlotNonvacuous M)

/-- Its Theta pilot magnitude is the canonical rooted readout. -/
theorem thetaSideQSideComparisonDataNonvacuous_theta :
    (thetaSideQSideComparisonDataNonvacuous M).thetaPilot.value =
      modelThetaValue M :=
  modelComparisonData_thetaPilot_value M (thetaSideQSideSlotNonvacuous M).qSigned
    (neg_pos.mpr (thetaSideQSideSlotNonvacuous M).q_negative)
    (thetaSideQSideSlotNonvacuous M).q_le_thetaSigned

#check thetaSideHullBoundSlotNonvacuous
#check thetaSideHullBoundSlotNonvacuous_le
#check thetaSideQSideSlotNonvacuous
#check thetaSideQSideComparisonDataNonvacuous_theta

end LeanFormal.IUT.XiFPaper.S3132ThetaSideSlotsNonvacuousActual
end