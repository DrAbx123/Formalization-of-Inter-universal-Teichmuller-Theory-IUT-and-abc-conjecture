import tmp.sheaf.xif.paper.S1675GlobalReadoutNormalizationActual
import tmp.sheaf.xif.paper.S2725GlobalThetaHullActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S1675GlobalReadoutNormalizationActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalHullSignedComparisonActual
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3068GlobalReadoutLeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The paper's global readout inequality. -/
def S3068GlobalReadoutLe : Prop :=
  globalThetaHullLogVolume (I := I) R n <= qPilotMagnitude (I := I)

/-- Conditional actual: native hull magnitude bound plus one-column
normalization imply the global readout inequality. -/
theorem S3068GlobalReadoutLe_of_native
    (hnorm : S1675OneColumnNormalization (I := I) T)
    (hbound : S1675HullNativeMagnitudeBound (I := I) R n T) :
    S3068GlobalReadoutLe (I := I) R n := by
  unfold S3068GlobalReadoutLe
  have hcomp : qPilotThetaHullComparison (I := I) R n := by
    exact s1675GlobalComparison_of_normalization (I := I) R n T
      { one_column_eq := hnorm, hull_bound := hbound }
  exact (qPilotThetaHullComparison_iff (I := I) R n).mp hcomp

theorem S3068GlobalReadoutLe_iff_condition :
    S3068GlobalReadoutLe (I := I) R n ↔
      GlobalComparisonCondition (I := I) R n := by
  unfold S3068GlobalReadoutLe GlobalComparisonCondition
  exact Iff.rfl

/-- The exact first unproved subformula: the hull-to-native-q magnitude bound. -/
abbrev S3068FirstMissingSubformula : Prop :=
  S1675HullNativeMagnitudeBound (I := I) R n T

/-- Actual local qVFamily formula identity is only an equality of formulas,
not yet an identification with the arithmetic hull log. -/
abbrev S3068LocalFormulaGap (b : Bad (nativePlaceSelection T)) : Type :=
  GlobalQVFamThetaHullSumActual.LocalThetaHullFormulaGap T b

#check S3068GlobalReadoutLe
#check S3068GlobalReadoutLe_of_native
#check S3068GlobalReadoutLe_iff_condition
#check S3068FirstMissingSubformula
#print axioms S3068GlobalReadoutLe_of_native

end LeanFormal.IUT.XiFPaper.S3068GlobalReadoutLeActual
end
