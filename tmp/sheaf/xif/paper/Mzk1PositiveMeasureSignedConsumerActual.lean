/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-! # Mzk1PositiveMeasureSignedConsumerActual — half-ball qRegion signed consumer

A565: consumer of the now-green `Mzk1PositiveMeasureQRegionProofActual`:
the half-ball q-region has positive/finite product Haar measure and normalized
volume 1; a strict Haar increase of the hull over it gives the strict signed
comparison and the StepXI contract/Cor312Conclusion.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureSignedConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The half-ball qRegion has positive real measure (proved). -/
theorem qRegion_measure_pos_real :
    0 < (rootExtensionProductHaar T (qRegion T)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (qRegion_measure_pos T))
    (ne_of_lt (qRegion_measure_lt_top T))

/-- The normalized volume of the qRegion is 1 (proved). -/
theorem qNormalizedVolume_qRegion_eq :
    qNormalizedVolume T (qRegion T) = 1 :=
  qNormalizedVolume_qRegion T (qRegion_measure_pos_real T)

/-- Conditional strict signed comparison: strict Haar increase of the hull over
the positive-measure qRegion gives the strict normalized-volume comparison. -/
theorem qNormalizedVolume_strict
    (h : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) :=
  qNormalizedVolume_strict_of_haarStrict T (qRegion_measure_pos_real T) h

/-- Consumer: the StepXI contract from the half-ball normalized volumes and the
strict Haar increase hypothesis. -/
noncomputable def qRegionContract
    (h : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal)
    (hqneg : qNormalizedVolume T (qRegion T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract (qNormalizedVolume T (qRegion T))
    (qNormalizedVolume T (s1902Hull T)) hqneg
    ipl hipl she hshe apt hapt (le_of_lt (qNormalizedVolume_strict T h))

/-- Consumer: Cor 3.12 conclusion from the half-ball qRegion. -/
theorem qRegionContract_cor312
    (h : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal)
    (hqneg : qNormalizedVolume T (qRegion T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (qRegionContract T h hqneg ipl hipl she hshe apt hapt) :=
  signedCor312_conclusion (qNormalizedVolume T (qRegion T))
    (qNormalizedVolume T (s1902Hull T)) hqneg
    ipl hipl she hshe apt hapt (le_of_lt (qNormalizedVolume_strict T h))

#check qNormalizedVolume_strict
#check qRegionContract_cor312

end LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureSignedConsumerActual
end
