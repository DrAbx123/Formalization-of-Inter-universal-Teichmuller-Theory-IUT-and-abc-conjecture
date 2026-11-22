import tmp.sheaf.xif.paper.S1035LogVolumeIdentificationAuditActual
import tmp.sheaf.xif.paper.S706ThetaPilotHullLogActual
import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S1025S994FiniteInputActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

/-! # S1036: global qPilot object audit and corrected bridge

C3.q is a single finite-place q candidate (SourcePilotRegionData.q :
FinitePlaceQCandidate place.val), not the global V_bad q collection.
s994VR/s994VS are per-b finite-carrier logs; weightedPaperV is their Bad-place
weighted sum (global over Bad).

Hence the S1034 bridge compares a single local scalar with a global weighted
sum: object mismatch.  The correct global qPilot object on the same Bad index
is S706's globalQPilotLog T (the global Theta-pilot qPilot log).  The corrected
bridge uses this global object; no local/global identification is asserted. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1036GlobalQPilotObjectAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe uX uLabel

variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Corrected bridge: global qPilot log (S706) and paper hull average are the
finite weighted S994 logs. -/
structure S1036CorrectedBridge (In : S994FiniteInput T) where
  globalQPilotMagnitude_eq :
    -globalQPilotLog (l := l) T =
      -weightedPaperV (l := l) T (s994VR (l := l) T In)
  hullMagnitude_eq :
    P.procession.average =
      -weightedPaperV (l := l) T (s994VS (l := l) T In)

/-- Corrected global comparison: P.average ≤ -global qPilot log. -/
theorem s1036GlobalComparison_of_bridge
    (In : S994FiniteInput T)
    (hb : S1036CorrectedBridge (l := l) P T In) :
    P.procession.average ≤ -globalQPilotLog (l := l) T := by
  rw [hb.hullMagnitude_eq, hb.globalQPilotMagnitude_eq]
  have h := s994GlobalWeightedInequality (l := l) T In
  linarith

/-- Exact corrected bridge existence. -/
def S1036CorrectedBridgeRequired : Prop :=
  ∃ In : S994FiniteInput T,
    Nonempty (S1036CorrectedBridge (l := l) P T In)

/-- Exact local/global object identification: the single local q scalar of an
actual paper object would have to equal S706's global qPilot log. -/
def S1036LocalGlobalQIdentification
    (Qlocal : Real) : Prop :=
  Qlocal = globalQPilotLog (l := l) T

end LeanFormal.IUT.XiFPaper.S1036GlobalQPilotObjectAuditActual

end
