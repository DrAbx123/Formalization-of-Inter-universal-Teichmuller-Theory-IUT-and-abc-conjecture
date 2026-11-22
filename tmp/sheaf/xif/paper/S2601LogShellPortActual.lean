import tmp.sheaf.xif.paper.S2600LogShellRealizationActual
import tmp.sheaf.xif.paper.S2597CarrierBridgeActual
import tmp.sheaf.xif.paper.S2592ValueMapCandidateActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2600LogShellRealizationActual
open LeanFormal.IUT.XiFPaper.S2597CarrierBridgeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2601LogShellPortActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V}
variable (R : SourceImageRealizationLogShell I v)
variable {T : SourceNativeInitialThetaData.{0} l} {b : Bad (nativePlaceSelection T)}
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

theorem S2601_sourceLocalLogDegree (a n c : Nat) :
    I.sourceLocalLogDegree v
      (S2597Point I R.toSourceImageRealization (T := T) (b := b) a n c) =
      Real.log ‖S2588PointMap T b a n c‖ :=
  S2597_sourceLocalLogDegree I R.toSourceImageRealization R.hdeg a n c

#check S2601_sourceLocalLogDegree
#print axioms S2601_sourceLocalLogDegree

end LeanFormal.IUT.XiFPaper.S2601LogShellPortActual
end