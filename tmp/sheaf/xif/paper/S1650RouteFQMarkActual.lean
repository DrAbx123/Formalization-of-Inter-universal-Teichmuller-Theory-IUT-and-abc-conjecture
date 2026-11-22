import tmp.sheaf.xif.paper.S1527OOrderEqualityActual
import tmp.sheaf.xif.paper.S1447ReportFMarkedTraceActual

/-! # S1650 Route F: q mark / allowed-output readout on the same C

Layer: F (Route F consumer) on the same concrete S1487/S1527 faithful
Gaussian input C.  S1447 supplies the value-layer q mark, allowed output
source and source local-log readout for an arbitrary OriginalInput plus a
SourceImageRealization.  S1487 supplies the same-C O-layer scalar equality.

EXACT FIRST MISSING source datum:
  R : S1487FaithfulInput.SourceImageRealization S1487w0
the actual value-group realization at the chosen place.  The tree contains no
inhabitant of SourceImageRealization at this concrete input/place, so the q
mark is recorded conditionally on R.  No conditional R -> OrigXiFThetaLinkActual
wrapper, no fake realization, no trivial action, no Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1650RouteFQMarkActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual

universe u
variable {l : PrimeGeFive}

/-- The same concrete faithful source input C of S1487/S1527. -/
abbrev S1650Input : OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487FaithfulInput (l := l)

/-- Chosen place v of the same C. -/
def S1650Place : S1487W := S1487w0

/-- Exact first missing source q-mark datum. -/
abbrev S1650SourceImageRealizationExact : Type _ :=
  (S1650Input (l := l)).SourceImageRealization (S1650Place)

/-- Actual q mark, conditional on the missing source realization. -/
noncomputable def S1650QMark
    (R : S1650SourceImageRealizationExact (l := l))
    (n : ThetaPilotCarrier l) :
    (S1650Input (l := l)).ThetaPilotPoint (S1650Place) :=
  qMark (S1650Input (l := l)) (S1650Place) R n

end LeanFormal.IUT.XiFPaper.S1650RouteFQMarkActual

end
