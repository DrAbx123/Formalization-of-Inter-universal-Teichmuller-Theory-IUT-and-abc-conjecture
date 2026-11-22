import tmp.sheaf.xif.paper.S862OtriLogVolumeInterfacePaperActual
import tmp.sheaf.xif.paper.S859PaperIntrinsicLogVolumeActual
import tmp.sheaf.xif.paper.S864PaperLambdaOLogVolumeActual

-- S869: fill S862's nonunitHaar and rootTheta normalization gaps.
-- nonunitHaar := divisor * log p (S859 intrinsic log-volume).
-- rootTheta := paperLambdaOLogVolume cRoot = -intrinsic(rootSection)
-- (S864), with least-hull log on the paper least hull.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S869OtriGapsFilledActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S862OtriLogVolumeInterfacePaperActual
open LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual
open LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.OtriangleLogVolumeObjectActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Nonunit O-triangle log measure: actual divisor*log p. -/
noncomputable def otriNonunitLogMeasure : StackSectionCarrier (l := l) T b → Real :=
  paperIntrinsicLogVolume (l := l) T b

theorem otriNonunitLogMeasure_root :
    otriNonunitLogMeasure (l := l) T b (stackRootSection (l := l) T b) =
      (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real) :=
  paperIntrinsicLogVolume_root (l := l) T b

theorem otriNonunitLogMeasure_q :
    otriNonunitLogMeasure (l := l) T b (stackQSection (l := l) T b) =
      ((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real) :=
  paperIntrinsicLogVolume_q (l := l) T b

/-- The actual nonunit Haar gap is filled by the divisor*log p measure. -/
theorem NonunitHaarRequired_filled :
    NonunitHaarRequired (K := T.arithmetic.F) (p := qVFamTensorP T b)
      (paperOtriPlace (l := l) T b) := by
  refine ⟨StackSectionCarrier (l := l) T b,
    otriNonunitLogMeasure (l := l) T b,
    (∀ u : StackSectionCarrier (l := l) T b,
      otriNonunitLogMeasure (l := l) T b u =
        (stackDivisorSection (l := l) T b u).toAdd *
          Real.log (qVFamTensorP T b : Real))⟩

/-- Root-theta least-hull log equals the negative intrinsic root log (S864). -/
theorem rootThetaLeastHullLog_eq_neg_intrinsic :
    paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) =
      -paperIntrinsicLogVolume (l := l) T b
        (stackRootSection (l := l) T b) :=
  paperLambdaOLogVolume_cRoot_eq_neg_section (l := l) T b

/-- The actual root-theta normalization gap is filled by the least-hull log. -/
theorem RootThetaNormalizationRequired_filled :
    RootThetaNormalizationRequired (K := T.arithmetic.F)
      (p := qVFamTensorP T b) (paperOtriPlace (l := l) T b) := by
  refine ⟨((qVFamily T b).order : Real),
    Set (rootStackExtension (l := l) T b),
    (paperLambdaOLogVolume (l := l) T b
      (paperRootCoefficientFamily T b) =
        -paperIntrinsicLogVolume (l := l) T b
          (stackRootSection (l := l) T b))⟩

theorem OtriNonunitHaarAndRootThetaRequired_filled :
    OtriNonunitHaarAndRootThetaRequired (l := l) T b :=
  ⟨NonunitHaarRequired_filled (l := l) T b,
    RootThetaNormalizationRequired_filled (l := l) T b⟩

#check NonunitHaarRequired_filled
#check RootThetaNormalizationRequired_filled
#check OtriNonunitHaarAndRootThetaRequired_filled

end LeanFormal.IUT.XiFPaper.S869OtriGapsFilledActual

end