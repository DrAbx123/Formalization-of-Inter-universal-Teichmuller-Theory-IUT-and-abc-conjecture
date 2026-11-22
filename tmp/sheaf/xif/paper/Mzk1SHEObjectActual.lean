import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual

/-!
# SHE object reference (q-pilot / Theta-pilot double image, literal carriers)

Reuses the green `Mzk1QPilotSHEDoubleImageActual` (literal q-pilot image, root-valued
Theta-pilot image, root equation and the proved SHE arrow).  This file exposes
the objects under a stable namespace for the Theorem 3.11 / Cor 3.12 route.

No sorry, axiom, True or placeholder; VOID q/(2l) theta readout is NOT used.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1SHEObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual

noncomputable section

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- q-pilot literal completion image. -/
noncomputable def sheQPilotImage : LiteralCompletionIQCarrier T :=
  qPilotCompletionImage T

/-- Theta-pilot literal root-extension image. -/
noncomputable def sheThetaPilotImage (j : ThetaLabel (l := l)) : S1902Carrier T :=
  thetaPilotImage T j

/-- The SHE root equation (`thetaPilot ^ (2l) = completion qPilot`) at every bad place. -/
theorem she_root_relation (b : Bad (nativePlaceSelection T)) :
    completionToRootExtension T (qPilotCompletionImage T) b =
      (thetaPilotImage T (oneThetaLabel l) b) ^ (2 * l.value) :=
  she_arrow_apply T b

/-- The proved SHE arrow statement (coordinatewise simultaneous expression). -/
theorem she_statement : SHEArrowStatement T := sheArrowStatement_proved T

/-- The q-pilot / Theta-pilot double image object. -/
noncomputable def sheDoubleImage : QThetaDoubleImage T := qThetaDoubleImage T

end

end LeanFormal.IUT.XiFPaper.Mzk1SHEObjectActual
