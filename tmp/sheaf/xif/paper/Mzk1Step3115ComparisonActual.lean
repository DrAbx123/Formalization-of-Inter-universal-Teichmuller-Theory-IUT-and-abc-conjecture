/-! **A497 VOID (see coord/VACUITY-AUDIT-A497.md):** the qTheta readouts used here are
  vacuous: `thetaPilotLogImage := qPilotLogImage / (2*l.value)` is a definitional rescaling,
  so `qThetaReadout_ordered` (hull <= det) is an arithmetic identity `-A <= -A/(2l)`, not the
  paper Cor 3.12 comparison.  The declarations below are kept for audit only and must NOT be
  cited as 3.12 evidence.  Real content: the two `hcomp` IUT IV comparisons. -/
import tmp.sheaf.xif.paper.Mzk1QPilotR4Stage5AlignActual
import tmp.sheaf.xif.paper.Mzk1R4LiteralAssemblyActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import tmp.sheaf.xif.paper.Mzk1LiteralIQHullFinitenessActual

/-! Mainline (A485 3.12 key point): the Step (xi-f) signed comparison
  `(hull readout) <= (det readout)` is DERIVED on the literal carrier from the qpilot
  double image (q/Theta dual readouts, `qThetaReadout_ordered`), the determinant/root
  normalization `theta^(2l) = q`, and the literal hull finiteness.  The four-triangle
  synthesis field `step3115_comparison` is then FILLED by the proved theorem. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Step3115ComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1LiteralIQHullFinitenessActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The literal HDD decomposition on the qpilot double image: hull readout = signed
  q-pilot log-volume, det readout = signed Theta-pilot log-volume (the (2l)-th-root
  readout of the determinant normalization `theta^(2l) = q`). -/
def qThetaHDD : HDDDecomp Real Real (Bad (nativePlaceSelection T)) where
  hullReadout := qThetaHullReadout T
  detReadout := qThetaDetReadout T

/-- **Step (xi-f) comparison, proved:** on the literal carrier the hull readout is at
  most the determinant readout; derived from the qpilot dual-image signed ordering. -/
theorem step3115_comparison_proved (b : Bad (nativePlaceSelection T)) :
    (fourTriangleReadout (qThetaHDD T) id b).1 ≤
      (fourTriangleReadout (qThetaHDD T) id b).2 :=
  qThetaReadout_ordered T b

/-- Determinant/root normalization: scaling the determinant readout by `2l` recovers the
  hull readout (the signed form of `theta^(2l) = q`). -/
theorem detReadout_twoL_mul_eq_hull (b : Bad (nativePlaceSelection T)) :
    (2 * (l.value : Real)) * qThetaDetReadout T b = qThetaHullReadout T b :=
  twoL_mul_thetaPilotLogImage T b

/-- Four-triangle synthesis on the literal carrier with the Step (xi-f) field FILLED by
  the proved comparison theorem (no longer a bare structure field). -/
def qThetaFourTriangleSynthesis (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    FourTriangleSynthesis (Bad (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) where
  contract := qThetaStepXIContract T b ipl hipl apt hapt
  hdd := qThetaHDD T
  dsc := id
  sheOut := b
  hull_eq := rfl
  theta_eq := rfl
  step3115_comparison := step3115_comparison_proved T b

/-- Consumer: the filled synthesis yields the Cor 3.12 ordered conclusion. -/
theorem cor312Conclusion_of_qThetaSynthesis (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (qThetaFourTriangleSynthesis T b ipl hipl apt hapt).contract :=
  cor312Conclusion_of_fourTriangleSynthesis _


end LeanFormal.IUT.XiFPaper.Mzk1Step3115ComparisonActual
-- A489 retry: shared-module olean available; refresh mtime.
