import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.W11ScratchAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem stackMuRoot_isPrimitiveRoot :
    IsPrimitiveRoot
      (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
        rootNormedAmbient T b)) (2 * l.value) := by
  unfold stackMuRoot
  rw [Units.val_mk0]
  exact Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot (rootNormedAmbient T b) (2 * l.value))

end LeanFormal.IUT.XiFPaper.W11ScratchAdapted

end
