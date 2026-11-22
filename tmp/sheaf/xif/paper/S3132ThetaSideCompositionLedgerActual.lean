import tmp.sheaf.xif.paper.S3132ThetaSideSharpResidualActual
import tmp.sheaf.xif.paper.S3132ThetaSideModelComparisonDataActual

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
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideCompositionLedgerActual

/-! # Paper-route Theta side: end-to-end composition ledger

Records the full composition from the sharp residual to the comparison-region
payload: (1) minimal data + Haar family; (2) sharp residual identity;
(3) canonical packaged source readout; (4) adapted Corollary 3.12 comparison
payload with Theta magnitude = canonical readout.  Component, not a paper object.

Composition chain (all checker-verified):
  LGPModelSourceClauseMissing (data)
    -> lgpModelNativeData + lgpNativeHaarFamily (T, mu)
    -> MissingConcreteVFormCanonicalReadout T mu (sharp identity)
    -> Real.log sourceHullRealLogVolume = S3131CanonicalRootedHC T mu
    -> AdaptedCorollary312ComparisonData (Theta magnitude = that value).
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Composition step 3: the packaged canonical source readout from the sharp
residual. -/
theorem composition_canonicalReadout
    (h : ThetaSideSharpResidual (l := l) M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (l := l)
        (lgpModelNativeData (l := l) M)
        (lgpNativeHaarFamily (lgpModelNativeData (l := l) M)) :=
  thetaSideSharpResidual_canonicalReadout (l := l) M h

/-- Composition step 4: the comparison payload, whose Theta magnitude equals the
same canonical readout (no extra hypotheses beyond the sharp residual and the
q-side comparison data). -/
def composition_comparisonData (qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤ -modelThetaValue (l := l) M) :
    AdaptedCorollary312ComparisonData :=
  modelComparisonData (l := l) M qSigned hq hle

/-- The composition payload's Theta magnitude is the canonical readout value. -/
theorem composition_comparisonData_thetaPilot_value (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -modelThetaValue (l := l) M) :
    (composition_comparisonData (l := l) M qSigned hq hle).thetaPilot.value =
      modelThetaValue (l := l) M :=
  modelComparisonData_thetaPilot_value (l := l) M qSigned hq hle

/-- **End-to-end**: the sharp residual plus q-side data yields the comparison
payload anchored at the canonical source readout. -/
theorem composition_thetaSide
    (h : ThetaSideSharpResidual (l := l) M) (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -modelThetaValue (l := l) M) :
    (Real.log sourceHullRealLogVolume =
        S3131CanonicalRootedHC (l := l)
          (lgpModelNativeData (l := l) M)
          (lgpNativeHaarFamily (lgpModelNativeData (l := l) M))) ∧
      ((composition_comparisonData (l := l) M qSigned hq hle).thetaPilot.value =
        modelThetaValue (l := l) M) :=
  ⟨composition_canonicalReadout (l := l) M h,
    composition_comparisonData_thetaPilot_value (l := l) M qSigned hq hle⟩

#check composition_canonicalReadout
#check composition_comparisonData
#check composition_comparisonData_thetaPilot_value
#check composition_thetaSide

end LeanFormal.IUT.XiFPaper.S3132ThetaSideCompositionLedgerActual
end
