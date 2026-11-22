import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual
import tmp.sheaf.xif.paper.NativeBadFintypeForTActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperXiFFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeForTActual
open MeasureTheory

variable {l : PrimeGeFive}

local instance nativeBadFintypeInstance
    (T : SourceNativeInitialThetaData.{0} l) :
    Fintype (Bad (nativePlaceSelection T)) :=
  LeanFormal.IUT.N8Closure.NativeBadFintypeForTActual.nativeBadFintype T

@[reducible] noncomputable def qVFamCanonicalMeasurableSpace
    (T : SourceNativeInitialThetaData.{0} l) :
    ∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (qVFamTensorBlock T b) :=
  fun b => borel (qVFamTensorBlock T b)

local instance qVFamCanonicalMeasurableSpaceInstance
    (T : SourceNativeInitialThetaData.{0} l) :
    ∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (qVFamTensorBlock T b) :=
  qVFamCanonicalMeasurableSpace T

@[reducible] noncomputable def qVFamCanonicalBorelSpace
    (T : SourceNativeInitialThetaData.{0} l) :
    ∀ b : Bad (nativePlaceSelection T),
      BorelSpace (qVFamTensorBlock T b) :=
  fun _ => ⟨rfl⟩

local instance qVFamCanonicalBorelSpaceInstance
    (T : SourceNativeInitialThetaData.{0} l) :
    ∀ b : Bad (nativePlaceSelection T),
      BorelSpace (qVFamTensorBlock T b) :=
  qVFamCanonicalBorelSpace T

attribute [instance] LeanFormal.IUT.N8Closure.NativeBadFintypeForTActual.nativeBadFintype

theorem paperLevelXiF_actual
    (T : SourceNativeInitialThetaData.{0} l) :
    ActualPaperXiFTarget (l := l) T := by
  exact actualPaperXiFTarget (l := l) T

end LeanFormal.IUT.XiFPaper.PaperXiFFinalActual

end
