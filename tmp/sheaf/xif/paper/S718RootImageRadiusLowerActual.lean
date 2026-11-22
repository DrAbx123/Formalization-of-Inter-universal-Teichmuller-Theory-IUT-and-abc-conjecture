import tmp.sheaf.xif.paper.S712RootLabelRegionNormActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S718RootImageRadiusLowerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.S712RootLabelRegionNormActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The positive theta label whose signed representative is one. -/
noncomputable def rootThetaLabelOne : ThetaLabel (l := l) :=
  ⟨oneSignedLabel (l := l), by
    rw [oneSignedLabel_val_local]
    norm_num⟩

/-- Exact root-theta norm formula at label one, the missing numerical input. -/
def RootThetaOneNormFormula : Prop :=
  ‖(rootNormedThetaValueInL T b
      (thetaLabelToSigned (l := l) (rootThetaLabelOne (l := l))) :
      rootNormedExtension T b)‖ =
    Real.rpow (qVFamTensorP T b : Real)
      (-((qVFamily T b).order : Real) / (2 * (l.value : Real)))

/-- Conditional root image radius lower bound from the exact label-one norm. -/
theorem rootImageRadiusLowerBound_of_rootThetaOneNorm
    (h : RootThetaOneNormFormula (l := l) T b) :
    S712RootLabelRegionNormActual.RootImageRadiusLowerBound (l := l) T b := by
  unfold S712RootLabelRegionNormActual.RootImageRadiusLowerBound
    rootLabelRegionRadiusCandidate
  rw [← h]
  have hle : (⟨‖(rootNormedThetaValueInL T b
      (thetaLabelToSigned (l := l) (rootThetaLabelOne (l := l))) :
      rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal) ≤ rootImageRadius T b := by
    unfold rootImageRadius
    exact Finset.le_sup (α := NNReal) (β := ThetaLabel (l := l))
      (s := Finset.univ)
      (f := fun j : ThetaLabel (l := l) =>
        (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal))
      (b := rootThetaLabelOne (l := l)) (Finset.mem_univ _)
  exact_mod_cast hle

end LeanFormal.IUT.XiFPaper.S718RootImageRadiusLowerActual

end
