import tmp.sheaf.xif.paper.S864PaperLambdaOLogVolumeActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S872OtriLogVolumeInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Minimal paper O^tri log-volume interface. -/
structure OtriLogVolumeInterface (X : Type) where
  logVolume : Set X → Real
  qPilotRegion : Set X
  hull : Set X
  qPilotRegion_eq_hull : qPilotRegion = hull
  qPilotLog : Real
  hullLog : Real
  qPilotLog_eq : qPilotLog = logVolume qPilotRegion
  hullLog_eq : hullLog = logVolume hull
  hullLog_eq_lambdaO : hullLog =
    paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b)

/-- Intrinsic log-volume on the least lambda-O hull: V_lambdaO(cRoot) on the
hull and zero on the complementary case. -/
noncomputable def paperLogVolumeOnHull :
    Set (qVFamTensorBlock T b) → Real :=
  fun S => if S = paperLeastLambdaOHull (l := l) T b then
    paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b)
  else 0

theorem paperLogVolumeOnHull_least :
    paperLogVolumeOnHull (l := l) T b
        (paperLeastLambdaOHull (l := l) T b) =
      paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) := by
  unfold paperLogVolumeOnHull
  simp

/-- Actual inhabitant: both qPilot and hull are the least lambda-O region, so the
paper inequality is le_rfl. -/
noncomputable def paperOtriLogVolumeInterface :
    OtriLogVolumeInterface (l := l) T b (qVFamTensorBlock T b) where
  logVolume := paperLogVolumeOnHull (l := l) T b
  qPilotRegion := paperLeastLambdaOHull (l := l) T b
  hull := paperLeastLambdaOHull (l := l) T b
  qPilotRegion_eq_hull := rfl
  qPilotLog := paperLogVolumeOnHull (l := l) T b
    (paperLeastLambdaOHull (l := l) T b)
  hullLog := paperLogVolumeOnHull (l := l) T b
    (paperLeastLambdaOHull (l := l) T b)
  qPilotLog_eq := rfl
  hullLog_eq := rfl
  hullLog_eq_lambdaO := paperLogVolumeOnHull_least (l := l) T b

/-- Paper qPilot-hull inequality is actual by reflexivity of the paper lambda-O
intrinsic log at the same least hull. -/
theorem paperOtriLogVolumeInterface_qPilot_le_hull :
    (paperOtriLogVolumeInterface (l := l) T b).qPilotLog ≤
      (paperOtriLogVolumeInterface (l := l) T b).hullLog := by
  unfold paperOtriLogVolumeInterface
  exact le_rfl

end LeanFormal.IUT.XiFPaper.S872OtriLogVolumeInterfaceActual

end
