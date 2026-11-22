import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import tmp.sheaf.xif.paper.PaperCompletionThetaValueActual
/-! # S1210: no q_v 2l-root witness
The paper q_v^(1/2l) root card is definitionally the S330 QVFamilyTwoLRootCard.
S342 proves it is impossible (order coprime to l), so it cannot witness the
S1187 KummerQuotientNontrivial.  No weak witness is introduced. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1210NoRootWitnessActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperCompletionThetaValueActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
theorem noPaperQRootCard : ¬ Nonempty (PaperQRootCard T b) :=
  S342QVFamilyRootImpossibleActual.qVFamilyTwoLRootCard_impossible (T := T) b
end LeanFormal.IUT.XiFPaper.S1210NoRootWitnessActual
