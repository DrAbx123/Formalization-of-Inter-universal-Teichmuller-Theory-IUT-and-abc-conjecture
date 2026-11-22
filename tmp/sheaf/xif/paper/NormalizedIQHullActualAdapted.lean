import tmp.sheaf.xif.paper.GlobalPositiveThetaHullLogVolumeActual
import tmp.sheaf.xif.paper.GlobalHullPaperXiFActual

/-!
# Normalized IQ hull: only the scalar needed for xi-f

The final xi-f comparison only needs two actual scalars:

* H = normalized Theta-hull scalar = - global positive Theta-hull log-volume;
* Q = q-pilot scalar = - I.qPilotSignedLogVolume (the q-pilot magnitude).

The comparison is H <= Q.  This is algebraically the paper direction

  I.qPilotSignedLogVolume <= thetaHullSignedLogVolume.

This file deliberately does NOT construct the full IQHullLogVolumeInterface:
no imageSet_subset_hull, scaleShift, compactness or unit-log finiteness fields
are assumed.  Only the actual scalar data and the exact comparison proposition
are kept.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.NormalizedIQHullActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalPositiveThetaHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
open LeanFormal.IUT.XiFPaper.GlobalHullPaperXiFActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Actual normalized Theta-hull scalar H (signed). -/
def normalizedThetaHullScalar : Real :=
  - globalThetaHullPositiveLogVolume (I := I) R n

/-- Actual q-pilot scalar Q (the q-pilot magnitude). -/
def normalizedQPilotScalar : Real :=
  - I.qPilotSignedLogVolume

/-- The actual normalized xi-f comparison H <= Q. -/
def normalizedXiFInequality : Prop :=
  normalizedThetaHullScalar (I := I) R n <= normalizedQPilotScalar (I := I)

/-- H is the negative of the actual positive hull log-volume. -/
theorem normalizedThetaHullScalar_eq :
    normalizedThetaHullScalar (I := I) R n =
      - globalThetaHullPositiveLogVolume (I := I) R n := rfl

/-- Q is the actual q-pilot magnitude. -/
theorem normalizedQPilotScalar_eq :
    normalizedQPilotScalar (I := I) = qPilotMagnitude (I := I) := rfl

/-- The normalized scalar comparison is exactly the q-pilot/Theta-hull signed
comparison. -/
theorem normalizedXiFInequality_iff_qPilotThetaHull :
    normalizedXiFInequality (I := I) R n ↔
      qPilotThetaHullComparison (I := I) R n := by
  unfold normalizedXiFInequality normalizedThetaHullScalar normalizedQPilotScalar
    qPilotThetaHullComparison thetaHullSignedLogVolume
  constructor <;> intro h <;> linarith

/-- Actual scalar data for the final xi-f comparison. -/
structure NormalizedIQHullScalarData where
  thetaHullScalar : Real
  thetaHullScalar_eq : thetaHullScalar =
    normalizedThetaHullScalar (I := I) R n
  qPilotScalar : Real
  qPilotScalar_eq : qPilotScalar = normalizedQPilotScalar (I := I)
  scalarInequality : thetaHullScalar <= qPilotScalar

/-- The actual normalized Theta-hull scalar H. -/
def normalizedThetaHullScalarData : Real :=
  normalizedThetaHullScalar (I := I) R n

/-- The actual normalized q-pilot scalar Q. -/
def normalizedQPilotScalarData : Real :=
  normalizedQPilotScalar (I := I)

/-- The exact normalized scalar comparison proposition. -/
def normalizedScalarInequality : Prop :=
  normalizedThetaHullScalarData (I := I) R n <= normalizedQPilotScalarData (I := I)

/-- The exact normalized scalar comparison is H <= Q. -/
theorem normalizedScalarInequality_iff :
    normalizedScalarInequality (I := I) R n ↔
      normalizedThetaHullScalar (I := I) R n <= normalizedQPilotScalar (I := I) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.NormalizedIQHullActualAdapted

end
