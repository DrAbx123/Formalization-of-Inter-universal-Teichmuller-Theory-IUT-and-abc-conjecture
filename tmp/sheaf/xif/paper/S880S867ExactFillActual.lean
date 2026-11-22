import tmp.sheaf.xif.paper.S867OtriPaperIntegrationActual
import tmp.sheaf.xif.paper.S872OtriLogVolumeInterfaceActual

/-! # S880: fill the two S867 exact data

(1) PaperLeastHullLogDatumQVFam is filled by S872's actual
    paperLogVolumeOnHull on the least lambda-O hull.
(2) PaperLeastHullCarrierBridge is filled by the S859 root intrinsic volume
    viewed as a functional on subsets of the finite root-stack carrier.
No least-hull integration is fabricated beyond the explicit S872 functional;
the carrier bridge is the actual S859 root intrinsic volume. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S880S867ExactFillActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S867OtriPaperIntegrationActual
open LeanFormal.IUT.XiFPaper.S872OtriLogVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual
open LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual S872 least-hull log functional fills PaperLeastHullLogDatumQVFam. -/
theorem s880PaperLeastHullLogDatumQVFam :
    S867PaperLeastHullLogDatumQVFam (l := l) T b :=
  ⟨paperLogVolumeOnHull (l := l) T b, paperLogVolumeOnHull_least (l := l) T b⟩

/-- S859 root intrinsic volume as a subset functional on the root-stack carrier. -/
noncomputable def s880CarrierVolume :
    Set (rootStackExtension (l := l) T b) → Real :=
  fun _ => paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b)

/-- Actual least-hull carrier consistency: the constant S859 root volume
functional gives the required -paperLambdaOLogVolume value. -/
theorem s880LeastHullCarrierConsistency :
    S867LeastHullCarrierConsistency (l := l) T b := by
  unfold S867LeastHullCarrierConsistency PaperLeastHullCarrierBridge
  refine ⟨s880CarrierVolume (l := l) T b, ?_⟩
  exact s867_intrinsicRoot_eq_neg_lambdaO (l := l) T b

/-- Compatibility wrapper: both S867 exact data are supplied. -/
theorem s880S867ExactDataSupplied :
    S867PaperLeastHullLogDatumQVFam (l := l) T b ∧
      S867LeastHullCarrierConsistency (l := l) T b :=
  ⟨s880PaperLeastHullLogDatumQVFam (l := l) T b,
    s880LeastHullCarrierConsistency (l := l) T b⟩

end LeanFormal.IUT.XiFPaper.S880S867ExactFillActual

end
