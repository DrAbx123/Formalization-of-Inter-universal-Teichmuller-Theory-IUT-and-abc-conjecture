import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: Corollary 3.12 signed comparison schema (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/CorollarySchema.lean (signedPilotLogVolume
:28, corollary312_of_signed_le :41, structure Corollary312ComparisonData :55,
thetaPilot/qPilot :63/:66, qPilot_positive :77, corollary312 :81): a signed pilot
log-volume schema with tagged sides and the positive-magnitude law, re-proved
with our production StepXIContract (LeanFormal.IUT.StepXIContract).  This is the
Cor 3.12 signed comparison payload the paper route consumes; the vendor file is
not importable, so the schema is re-established here.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorCorollarySchemaActual

open LeanFormal.IUT

/-- The two pilot sides of the Corollary 3.12 comparison. -/
inductive SourcePilotSide
  | theta
  | q
  deriving DecidableEq, Repr

/-- A tagged pilot log-volume: the stored value is the positive magnitude of the
signed log-volume. -/
structure SourcePilotLogVolume where
  /-- which pilot this log-volume belongs to -/
  side : SourcePilotSide
  /-- the positive magnitude -/
  value : ℝ

/-- Turn a signed real log-volume (e.g. -|log q|) into a tagged pilot
log-volume whose stored value is the positive magnitude. -/
def sourceSignedPilotLogVolume (side : SourcePilotSide) (signedValue : ℝ) :
    SourcePilotLogVolume where
  side := side
  value := -signedValue

/-- The signed comparison payload of Corollary 3.12: signed q-pilot and
Theta-pilot log-volumes with the q-positivity and the ordered comparison. -/
structure SourceCor312ComparisonData where
  /-- signed Theta-pilot log-volume -thetaSigned = -|log Theta| -/
  thetaSigned : ℝ
  /-- signed q-pilot log-volume qSigned = -|log q| -/
  qSigned : ℝ
  /-- qSigned is negative (q != 1) -/
  q_positive : 0 < -qSigned
  /-- the ordered comparison -/
  qSigned_le_thetaSigned : qSigned ≤ thetaSigned

namespace SourceCor312ComparisonData

/-- The tagged Theta pilot log-volume. -/
def thetaPilot (data : SourceCor312ComparisonData) : SourcePilotLogVolume :=
  sourceSignedPilotLogVolume SourcePilotSide.theta data.thetaSigned

/-- The tagged q pilot log-volume. -/
def qPilot (data : SourceCor312ComparisonData) : SourcePilotLogVolume :=
  sourceSignedPilotLogVolume SourcePilotSide.q data.qSigned

/-- The q pilot's stored value is positive. -/
theorem qPilot_positive (data : SourceCor312ComparisonData) :
    0 < data.qPilot.value := by
  simpa [qPilot, sourceSignedPilotLogVolume] using data.q_positive

end SourceCor312ComparisonData

/-- Every constructed StepXI contract gives the signed comparison payload. -/
def sourceCor312ComparisonDataOfContract (C : LeanFormal.IUT.StepXIContract) :
    SourceCor312ComparisonData where
  thetaSigned := C.thetaSigned
  qSigned := C.qSigned
  q_positive := LeanFormal.IUT.q_positive_of_constructed_stepXI C
  qSigned_le_thetaSigned := LeanFormal.IUT.cor312_of_constructed_stepXI C

/-- The signed comparison payload's q side is the constructed contract's q. -/
theorem sourceCor312ComparisonDataOfContract_qSigned
    (C : LeanFormal.IUT.StepXIContract) :
    (sourceCor312ComparisonDataOfContract C).qSigned = C.qSigned := rfl

end LeanFormal.IUT.XiFPaper.S3139VendorCorollarySchemaActual

end
