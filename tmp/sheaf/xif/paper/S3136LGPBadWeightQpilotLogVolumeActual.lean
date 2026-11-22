import tmp.sheaf.xif.paper.S3136LGPBadWeightQpilotCompareActual

/-! # Stage-4 host: normalized-reading comparison with the qpilot weights

Source anchors: IUT III, Remark 3.1.1, (ii)-(iv), pp. 95--97; IUT III, Rem.
3.9.4; IUT II, Remark 2.5.1, (i).

Conditional comparison of the normalized readings: under the pointwise raw
weight agreement hypothesis, the two actual normalized families agree
pointwise, their totals agree, and both total normalized readings equal one.

LABEL: prerequisite component only.  Consumer: lattice R1/R-C, abc F4(a). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPBadWeightQpilotLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.W6ActualPilotMonodromyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeSignActual
open LeanFormal.IUT.XiFPaper.S3133S3131WeightNormalizationActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPWeightAgreementBridgeActual
open LeanFormal.IUT.XiFPaper.S3136LGPBadWeightNormalizationActual
open LeanFormal.IUT.XiFPaper.S3136LGPBadWeightQpilotCompareActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

/-- Under pointwise raw weight agreement, the two normalized families have
equal total readings (both totals are one). -/
theorem lgpBadQpilotNormalizedTotals_eq
    [Nonempty (Bad (nativePlaceSelection T))] :
    (∑ b : Bad (nativePlaceSelection T), lgpBadNormalizedWeight T b) =
      (∑ b : Bad (nativePlaceSelection T), S3131NormalizedWeight T b) := by
  rw [lgpBadNormalizedWeight_total T, S3131NormalizedWeightTotal T]

/-- Under pointwise raw weight agreement, the two normalized families agree
pointwise and the total readings are equal. -/
theorem lgpBadQpilotNormalizedReading_agree
    [Nonempty (Bad (nativePlaceSelection T))]
    (h : ∀ b : Bad (nativePlaceSelection T),
      lgpBadWeight T b = nativeBadLocalWeight T b) :
    (∀ b : Bad (nativePlaceSelection T),
        lgpBadNormalizedWeight T b = S3131NormalizedWeight T b) ∧
      (∑ b : Bad (nativePlaceSelection T), lgpBadNormalizedWeight T b) =
        (∑ b : Bad (nativePlaceSelection T), S3131NormalizedWeight T b) :=
  ⟨lgpBadNormalizedWeight_eq_qpilot_of_weightAgreement T h,
    lgpBadQpilotNormalizedTotals_eq T⟩

#check lgpBadQpilotNormalizedTotals_eq
#check lgpBadQpilotNormalizedReading_agree

end LeanFormal.IUT.XiFPaper.S3136LGPBadWeightQpilotLogVolumeActual
end