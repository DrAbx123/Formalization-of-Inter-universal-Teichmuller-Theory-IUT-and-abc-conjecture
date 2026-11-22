import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamThetaImagePointActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! # L-valued pure-tensor lift of the root theta image (ThetaLabel) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.QVFamRootThetaTensorLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImagePointActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

/-- Actual L-valued pure-tensor lift at a positive paper theta label. -/
noncomputable def qVFamRootThetaTensorLift
    (j : ThetaLabel (l := l)) : rootTensorBlock T b :=
  rootTensorThetaImage T b (thetaLabelToSigned (l := l) j)

/-- The actual L-valued root theta tensor image set. -/
noncomputable def qVFamRootThetaTensorImageSet : Set (rootTensorBlock T b) :=
  Set.range (qVFamRootThetaTensorLift (l := l) T b)

theorem qVFamRootThetaTensorLift_mem_image
    (j : ThetaLabel (l := l)) :
    qVFamRootThetaTensorLift (l := l) T b j ∈
      qVFamRootThetaTensorImageSet (l := l) T b :=
  ⟨j, rfl⟩

/-- The pure-tensor lift is the actual root tensor theta image at the positive label. -/
theorem qVFamRootThetaTensorLift_eq_rootTensorThetaImage
    (j : ThetaLabel (l := l)) :
    qVFamRootThetaTensorLift (l := l) T b j =
      rootTensorThetaImage T b (thetaLabelToSigned (l := l) j) :=
  rfl

/-- Exact remaining gap: the mu_{2l} action on the L-valued tensor direction
requires a root of unity in L; no such root is constructed here. -/
structure QVFamRootThetaMuTensorLiftGap where
  muAction : Nat → ThetaLabel (l := l) → rootTensorBlock T b
  muAction_compat : Prop

def QVFamRootThetaMuTensorLiftGapRequired : Prop :=
  Nonempty (QVFamRootThetaMuTensorLiftGap (l := l) T b)

end LeanFormal.IUT.XiFPaper.QVFamRootThetaTensorLiftActual

end
